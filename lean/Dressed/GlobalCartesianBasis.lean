import Dressed.PhysicalGramLowerBound
import Dressed.PairVacuumNorm

/-!
# A genuine global real basis map for the Cartesian pair Hamiltonian

The diagonal involution is U(s)=(-1)^(N(s)/2), with natural-number division.
It is one globally defined operator, not a product of overlapping edge adapters.
It flips pair creation/annihilation and preserves the number-conserving bond
matrix entries. Consequently it conjugates the full Cartesian Hamiltonian to
the actual real magic-rung representative of the standard Pauli Hamiltonian.
-/
noncomputable section
namespace BilayerDressed.CartesianBasis
open Matrix BilayerGap
open scoped BigOperators Kronecker
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Config (V : Type*) := V → Fin 4
abbrev Op (V : Type*) := Matrix (Config V) (Config V) ℝ

/-- The natural-valued occupation of a single rung. -/
def rungCount (i : Fin 4) : ℕ := if i = 0 then 0 else 1
/-- The natural-valued total number of triplets in a basis configuration. -/
def count (s : Config V) : ℕ := ∑ v, rungCount (s v)
def pairCount (p : LocalBond.PairIndex) : ℕ := rungCount p.1 + rungCount p.2
/-- The exterior number, with each of the two endpoints removed exactly once. -/
def outsideCount (u v : V) (s : Config V) : ℕ :=
  ∑ w ∈ (Finset.univ.erase u).erase v, rungCount (s w)

def countPhase (n : ℕ) : ℝ := (-1) ^ (n / 2)
def phase (s : Config V) : ℝ := countPhase (count s)
/-- One global matrix, diagonal in the full configuration basis. -/
def U : Op V := Matrix.diagonal phase

@[simp] theorem countPhase_mul_self (n : ℕ) : countPhase n * countPhase n = 1 := by
  unfold countPhase
  rw [← mul_pow]
  norm_num

@[simp] theorem countPhase_add_two (n : ℕ) : countPhase (n+2) = -countPhase n := by
  have h : (n+2)/2 = n/2+1 := by omega
  simp only [countPhase, h, pow_succ]
  ring

omit [DecidableEq V] in
@[simp] theorem phase_mul_self (s : Config V) : phase s * phase s = 1 :=
  countPhase_mul_self _

omit [DecidableEq V] in
@[simp] theorem U_transpose : (U : Op V).transpose = U := by
  simp [U]

/-- The inverse exists exactly and equals the same real matrix. -/
@[simp] theorem U_mul_U : (U : Op V) * U = 1 := by
  rw [U, Matrix.diagonal_mul_diagonal]
  simp [← Matrix.diagonal_one]

/-- Entrywise conjugation, valid for every matrix on the full Hilbert space. -/
theorem conjugate_entry (A : Op V) (s t : Config V) :
    ((U : Op V) * A * U : Op V) s t = phase s * A s t * phase t := by
  simp [U, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

omit [DecidableEq V] in
@[simp] theorem count_vacuum : count (TripletNumber.vacuum : Config V) = 0 := by
  simp [count, TripletNumber.vacuum, rungCount]

omit [DecidableEq V] in
@[simp] theorem phase_vacuum : phase (TripletNumber.vacuum : Config V) = 1 := by
  simp [phase, countPhase]

/-- In particular, the physical normalized all-singlet vacuum is unchanged. -/
theorem U_vacuum : (U : Op V).mulVec
    (Pi.single (TripletNumber.vacuum : Config V) 1) =
      Pi.single (TripletNumber.vacuum : Config V) 1 := by
  ext s
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    U, Matrix.diagonal_apply]
  by_cases hs : s = TripletNumber.vacuum
  · subst s; simp
  · simp [hs]

/-- The exact number operator is fixed by this global change of basis. -/
theorem conjugate_number : U * (TripletNumber.number : Op V) * U =
    TripletNumber.number := by
  ext s t
  rw [conjugate_entry, TripletNumber.number_eq_diagonal]
  by_cases h : s=t
  · subst t
    simp only [Matrix.diagonal_apply_eq]
    calc
      phase s * TripletNumber.energy s * phase s =
          (phase s * phase s) * TripletNumber.energy s := by ring
      _ = TripletNumber.energy s := by rw [phase_mul_self, one_mul]
  · simp [h]

/-- Exact separation of the two endpoints, with no Hilbert-space dimension factor. -/
theorem count_eq_pair_add_outside (u v : V) (huv : u ≠ v) (s : Config V) :
    count s = pairCount (s u,s v) + outsideCount u v s := by
  have h₁ := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun w => rungCount (s w)) (by simp : u ∈ (Finset.univ : Finset V))
  have h₂ := Finset.sum_erase_add ((Finset.univ : Finset V).erase u)
    (fun w => rungCount (s w)) (by simp [huv.symm] : v ∈ (Finset.univ : Finset V).erase u)
  unfold count pairCount outsideCount
  dsimp only at *
  omega

theorem outsideCount_eq (u v : V) (s t : Config V)
    (hout : ∀ w, w ≠ u → w ≠ v → s w = t w) :
    outsideCount u v s = outsideCount u v t := by
  apply Finset.sum_congr rfl
  intro w hw
  rw [hout w (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    (Finset.mem_erase.mp hw).1]

/-- Local vacuum sign expressed only through the local triplet count. -/
theorem pairSign_eq_count (p : LocalBond.PairIndex) :
    LocalBond.pairSign p = if pairCount p = 0 then -1 else 1 := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [LocalBond.pairSign, pairCount, rungCount]

/-- All nonzero Cartesian entries either conserve number or create/annihilate a pair. -/
theorem twiceBond_count_support_Q : ∀ p q : LocalBond.PairIndex,
    (LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℚ) p q = 0 ∨
      pairCount p = pairCount q ∨
      (pairCount p = 0 ∧ pairCount q = 2) ∨
      (pairCount p = 2 ∧ pairCount q = 0) := by
  decide +kernel

/-- Exact scalar extension of the rational Cartesian matrix. -/
theorem twiceBond_cast (p q : LocalBond.PairIndex) :
    ((LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℚ) p q : ℝ) =
      (LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ) p q := by
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  simp only [LocalBond.twiceBond, LocalBond.difference, LocalBond.create,
    LocalBond.annihilate, LocalBond.unit, Matrix.sum_apply, Matrix.kronecker_apply,
    Matrix.single, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_one,
    Rat.cast_zero, apply_ite]

theorem twiceBond_count_support (p q : LocalBond.PairIndex) :
    (LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ) p q = 0 ∨
      pairCount p = pairCount q ∨
      (pairCount p = 0 ∧ pairCount q = 2) ∨
      (pairCount p = 2 ∧ pairCount q = 0) := by
  rcases twiceBond_count_support_Q p q with h | h
  · left
    rw [← twiceBond_cast, h, Rat.cast_zero]
  · exact Or.inr h

/-- On a nonzero bond entry, the global phase product is exactly the required sign.
The common exterior count is arbitrary; no even-number-sector restriction is used. -/
theorem phase_product_on_bond (u v : V) (huv : u ≠ v) (s t : Config V)
    (hout : ∀ w, w ≠ u → w ≠ v → s w = t w)
    (hnonzero : (LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
      (s u,s v) (t u,t v) ≠ 0) :
    phase s * phase t = LocalBond.pairSign (s u,s v) * LocalBond.pairSign (t u,t v) := by
  have hs := count_eq_pair_add_outside u v huv s
  have ht := count_eq_pair_add_outside u v huv t
  have ho := outsideCount_eq u v s t hout
  rcases twiceBond_count_support (s u,s v) (t u,t v) with hz | he | he | he
  · exact False.elim (hnonzero hz)
  · have hc : count s = count t := by rw [hs, ht, he, ho]
    rw [phase, phase, hc, countPhase_mul_self, pairSign_eq_count,
      pairSign_eq_count, he]
    split_ifs <;> norm_num
  · rcases he with ⟨he₁,he₂⟩
    rw [phase, phase, hs, ht, he₁, he₂, ho, Nat.zero_add,
      Nat.add_comm 2, countPhase_add_two, pairSign_eq_count, pairSign_eq_count,
      he₁, he₂]
    norm_num
  · rcases he with ⟨he₁,he₂⟩
    rw [phase, phase, hs, ht, he₁, he₂, ho, Nat.zero_add,
      Nat.add_comm 2, countPhase_add_two, pairSign_eq_count, pairSign_eq_count,
      he₁, he₂]
    norm_num

/-- The actual Cartesian two-rung interaction in physical J_parallel units. -/
def bond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ :=
  (1/2 : ℝ) • LocalBond.twiceBond

/-- A single global U conjugates every distinct-endpoint bond simultaneously. -/
theorem conjugate_pairLift (u v : V) (huv : u ≠ v) :
    (U : Op V) * Torus.pairLift bond u v * U =
      Torus.pairLift LocalBond.magicBond u v := by
  ext s t
  rw [conjugate_entry]
  by_cases hout : ∀ w, w ≠ u → w ≠ v → s w = t w
  · simp only [Torus.pairLift, if_pos hout, bond, Matrix.smul_apply, smul_eq_mul,
      LocalBond.magicBond_entry]
    by_cases hz : (LocalBond.twiceBond : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
        (s u,s v) (t u,t v) = 0
    · simp [hz]
    · have hh := phase_product_on_bond u v huv s t hout hz
      calc
        phase s * ((1/2)*LocalBond.twiceBond (s u,s v) (t u,t v)) * phase t =
            (1/2)*LocalBond.twiceBond (s u,s v) (t u,t v)*(phase s*phase t) := by ring
        _ = _ := by rw [hh]; ring
  · simp [Torus.pairLift, hout]

/-- Cartesian graph Hamiltonian with two positively oriented edge families. -/
def graphHamiltonian (ex ey : Equiv.Perm V) (g : ℝ) : Op V :=
  TripletNumber.number + (g/2) •
    ((∑ v, Torus.pairLift LocalBond.twiceBond v (ex v)) +
      (∑ v, Torus.pairLift LocalBond.twiceBond v (ey v)))

theorem graphHamiltonian_as_bonds (ex ey : Equiv.Perm V) (g : ℝ) :
    graphHamiltonian ex ey g = TripletNumber.number + g •
      ((∑ v, Torus.pairLift bond v (ex v)) +
        (∑ v, Torus.pairLift bond v (ey v))) := by
  simp only [graphHamiltonian, bond, Torus.pairLift_smul, ← Finset.smul_sum,
    ← smul_add, smul_smul]
  congr 2
  ring

/-- Exact full-Hamiltonian equality, not just equality of selected matrix elements. -/
theorem graphHamiltonian_conjugation (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v) (g : ℝ) :
    (U : Op V) * graphHamiltonian ex ey g * U =
      PhysicalGram.graphHamiltonian ex ey g := by
  rw [graphHamiltonian_as_bonds, PhysicalGram.graphHamiltonian_as_bonds ex ey hx hy]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul, conjugate_number,
    conjugate_pairLift _ _ (hx _), conjugate_pairLift _ _ (hy _)]
  rfl

/-- Cartesian version of the even rectangular periodic system. -/
def fullHamiltonian (n m : ℕ) (g : ℝ) : Op (Torus.FullVertex (2*n) (2*m)) :=
  graphHamiltonian (Torus.xNext n m) (Torus.yNext n m) g

/-- The global real involution links the concrete Cartesian and physical-rung torus. -/
theorem fullHamiltonian_conjugation (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    U * fullHamiltonian n m g * U =
      Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g := by
  have hh := graphHamiltonian_conjugation (Torus.xNext n m) (Torus.yNext n m)
    (fun v => (Torus.xNext_ne n m hn v).symm)
    (fun v => (Torus.yNext_ne n m hm v).symm) g
  simpa only [fullHamiltonian, PhysicalGram.graphHamiltonian, PhysicalGram.number,
    Torus.fullHamiltonian, Torus.fullXNext, Torus.fullYNext, Torus.xNext, Torus.yNext] using hh

/-- This matrix is a real orthogonal involution. -/
theorem U_orthogonal : (U : Op V).transpose * U = 1 := by
  rw [U_transpose, U_mul_U]

/-- The normalized Euclidean physical vacuum is fixed as well. -/
theorem U_vacuumVector : Matrix.toEuclideanCLM (n := Config V) (𝕜 := ℝ)
    U (vacuumVector : ConfigurationHilbert V) = vacuumVector := by
  ext s
  exact congrFun U_vacuum s

/-- Every concrete number-conserving operator is fixed by global conjugation. -/
theorem conjugate_of_count_preserving (A : Op V)
    (hA : ∀ s t, A s t ≠ 0 → count s = count t) :
    U * A * U = A := by
  ext s t
  rw [conjugate_entry]
  by_cases hz : A s t = 0
  · simp [hz]
  · have he : phase s = phase t := congrArg countPhase (hA s t hz)
    rw [he]
    calc
      phase t * A s t * phase t = (phase t * phase t) * A s t := by ring
      _ = A s t := by rw [phase_mul_self, one_mul]

/-- Any actual operator raising triplet number by two acquires exactly one minus sign. -/
theorem conjugate_of_count_raise_two (A : Op V)
    (hA : ∀ s t, A s t ≠ 0 → count s = count t + 2) :
    U * A * U = -A := by
  ext s t
  rw [conjugate_entry]
  by_cases hz : A s t = 0
  · simp [hz]
  · have he : phase s = -phase t := by
      simp only [phase, hA s t hz, countPhase_add_two]
    rw [he]
    simp only [Matrix.neg_apply]
    calc
      -phase t * A s t * phase t = -(phase t * phase t) * A s t := by ring
      _ = -A s t := by rw [phase_mul_self]; ring

/-- Local pair creation is lifted into the genuine full tensor space before conjugation. -/
theorem conjugate_pairLift_raise_two
    (A : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
    (hA : ∀ p q, A p q ≠ 0 → pairCount p = 2 ∧ pairCount q = 0)
    (u v : V) (huv : u ≠ v) :
    (U : Op V) * Torus.pairLift A u v * U = -Torus.pairLift A u v := by
  apply conjugate_of_count_raise_two
  intro s t hst
  have hout : ∀ w, w ≠ u → w ≠ v → s w = t w := by
    by_contra hh
    exact hst (by simp [Torus.pairLift, hh])
  have hn : A (s u,s v) (t u,t v) ≠ 0 := by
    simpa only [Torus.pairLift, if_pos hout] using hst
  rcases hA (s u,s v) (t u,t v) hn with ⟨hs,ht⟩
  rw [count_eq_pair_add_outside u v huv s, count_eq_pair_add_outside u v huv t,
    hs, ht, outsideCount_eq u v s t hout]
  omega

/-- Exact support of a hard-core same-color creation, with no assumed algebra. -/
theorem local_creation_count_support (α : Fin 3) (p q : LocalBond.PairIndex)
    (hn : (rungCreate α ⊗ₖ rungCreate α) p q ≠ 0) :
    pairCount p = 2 ∧ pairCount q = 0 := by
  rcases p with ⟨p₁,p₂⟩
  rcases q with ⟨q₁,q₂⟩
  simp only [Matrix.kronecker_apply, rungCreate, Matrix.single, Matrix.of_apply] at hn
  have h₁ : α.succ = p₁ ∧ 0 = q₁ := by
    by_contra hh
    simp [hh] at hn
  have h₂ : α.succ = p₂ ∧ 0 = q₂ := by
    by_contra hh
    simp [hh] at hn
  rcases h₁ with ⟨rfl,rfl⟩
  rcases h₂ with ⟨rfl,rfl⟩
  simp [pairCount, rungCount]

/-- Actual lifted creation products change sign under the global basis map. -/
theorem conjugate_creation_product (u v : V) (huv : u ≠ v) (α : Fin 3) :
    (U : Op V) * (globalCreate u α * globalCreate v α) * U =
      -(globalCreate u α * globalCreate v α) := by
  unfold globalCreate
  rw [Torus.siteLift_mul_distinct _ _ huv]
  exact conjugate_pairLift_raise_two _ (local_creation_count_support α) u v huv

/-- The concrete SU(2)-invariant pair creation flips sign, even for coinciding endpoints. -/
theorem conjugate_pairCreate (u v : V) :
    (U : Op V) * pairCreate u v * U = -pairCreate u v := by
  by_cases huv : u = v
  · subst v
    simp [pairCreate_same_site_zero]
  · simp only [pairCreate, Matrix.mul_sum, Matrix.sum_mul,
      conjugate_creation_product _ _ huv, Finset.sum_neg_distrib]

/-- Arbitrary ordered pair kernels, including the standard half-weight convention. -/
theorem conjugate_pairKernelOperator (K : V → V → ℝ) :
    (U : Op V) * pairKernelOperator K * U = -pairKernelOperator K := by
  simp only [pairKernelOperator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, conjugate_pairCreate,
    smul_neg, Finset.sum_neg_distrib]

theorem conjugate_pairKernelS (K : V → V → ℝ) :
    (U : Op V) * pairKernelS K * U = -pairKernelS K :=
  conjugate_pairKernelOperator _

omit [DecidableEq V] in
/-- The integer label is exactly the eigenvalue of the physical number projector sum. -/
theorem count_cast (s : Config V) : (count s : ℝ) = TripletNumber.energy s := by
  simp [count, rungCount, TripletNumber.energy, TripletNumber.localEnergy]

/-- Norm preservation in the genuine Hilbert norm, not the entrywise matrix norm. -/
theorem U_norm_apply (x : ConfigurationHilbert V) :
    ‖Matrix.toEuclideanCLM (n := Config V) (𝕜 := ℝ) U x‖ = ‖x‖ := by
  have hsq : ‖Matrix.toEuclideanCLM (n := Config V) (𝕜 := ℝ) U x‖^2 = ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro s _
    change ‖(U *ᵥ (fun t => x t)) s‖^2 = ‖x s‖^2
    simp only [U, Matrix.mulVec_diagonal, norm_mul, mul_pow]
    have hp : ‖phase s‖^2 = 1 := by
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith only [phase_mul_self s]
    rw [hp, one_mul]
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Config V) (𝕜 := ℝ) U x), norm_nonneg x]

/-- Pair annihilation has the same sign rule by exact real transpose. -/
theorem conjugate_pairCreate_transpose (u v : V) :
    (U : Op V) * (pairCreate u v).transpose * U = -(pairCreate u v).transpose := by
  simpa only [Matrix.transpose_mul, U_transpose, Matrix.transpose_neg, mul_assoc] using
    congrArg Matrix.transpose (conjugate_pairCreate u v)

/-- All characteristic roots and their algebraic multiplicities are preserved. -/
theorem conjugate_charpoly (A : Op V) :
    ((U : Op V) * A * U).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, U_mul_U, one_mul]

theorem fullHamiltonian_charpoly (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).charpoly =
      (fullHamiltonian n m g).charpoly := by
  rw [← fullHamiltonian_conjugation n m hn hm, conjugate_charpoly]

/-- The Cartesian Hamiltonian has the exact spectrum of the standard complex Pauli model. -/
theorem standardPauli_charpoly (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    (PhysicalSpinHamiltonian.fullHamiltonian (2*n) (2*m) g).charpoly =
      (fullHamiltonian n m g).charpoly.map (algebraMap ℝ ℂ) := by
  rw [PhysicalSpinHamiltonian.fullHamiltonian_charpoly]
  unfold PhysicalSpinHamiltonian.complexify
  rw [Matrix.charpoly_map, fullHamiltonian_charpoly n m hn hm]
  rfl

end BilayerDressed.CartesianBasis
