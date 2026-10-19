import Dressed.PhysicalBasisAdapter
import Dressed.TensorQuadratic
import Dressed.NumberSpectrum
import Gap.PhysicalSpinHamiltonian

/-!
A global quadratic-form bound for the concrete bilayer Hamiltonian.
Every local bound is applied in the physical model's real rung coordinates;
tensor lifts and degree counting are proved, not assumed.
-/
noncomputable section
namespace BilayerDressed.PhysicalGram
open Matrix BilayerGap
open scoped BigOperators Kronecker RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Config (V : Type*) := V → Fin 4
abbrev Op (V : Type*) := Matrix (Config V) (Config V) ℝ
abbrev Outside (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- Separate two actual local factors from all other rung coordinates. -/
def pairConfigEquiv (u v : V) (huv : u ≠ v) :
    (LocalBond.PairIndex × (Outside u v → Fin 4)) ≃ Config V where
  toFun p w := if hu : w = u then p.1.1 else
    if hv : w = v then p.1.2 else p.2 ⟨w,hu,hv⟩
  invFun s := ((s u,s v),fun w => s w)
  left_inv := by
    rintro ⟨⟨a,b⟩,s⟩
    simp only [dif_neg huv.symm]
    congr
    funext w
    simp [w.property.1,w.property.2]
  right_inv := by
    intro s
    funext w
    dsimp only
    split_ifs with h₁ h₂ <;> simp_all

/-- The entry-defined two-site lift really is a tensor identity extension. -/
theorem pairLift_eq_reindex (A : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
    (u v : V) (huv : u ≠ v) :
    Torus.pairLift A u v = Matrix.reindex (pairConfigEquiv u v huv)
      (pairConfigEquiv u v huv)
      (A ⊗ₖ (1 : Matrix (Outside u v → Fin 4) (Outside u v → Fin 4) ℝ)) := by
  ext s t
  have he : (fun w : Outside u v => s w) = (fun w : Outside u v => t w) ↔
      ∀ w, w ≠ u → w ≠ v → s w = t w := by
    constructor
    · intro h w hwu hwv
      exact congrFun h ⟨w,hwu,hwv⟩
    · intro h
      funext w
      exact h w w.property.1 w.property.2
  simp only [Torus.pairLift, Matrix.reindex_apply, Matrix.submatrix_apply,
    pairConfigEquiv, Equiv.coe_fn_symm_mk, Matrix.kronecker_apply, Matrix.one_apply]
  simp only [he]
  split_ifs <;> simp

/-- Every positive local quadratic form stays positive on the full Hilbert space. -/
theorem pairLift_quadratic_nonneg (A : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
    (hA : ∀ z, 0 ≤ dotProduct z (A.mulVec z)) (u v : V) (huv : u ≠ v)
    (x : Config V → ℝ) :
    0 ≤ dotProduct x ((Torus.pairLift A u v).mulVec x) := by
  rw [pairLift_eq_reindex A u v huv, BilayerDressed.reindex_quadratic]
  exact BilayerDressed.kronecker_identity_quadratic_nonneg A hA _

/-- Lifting the local identity does not multiply it by the exterior dimension. -/
theorem pairLift_one (u v : V) (huv : u ≠ v) :
    Torus.pairLift (1 : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ) u v = 1 := by
  rw [pairLift_eq_reindex _ u v huv, Matrix.one_kronecker_one]
  simp

def qform (A : Matrix (Config V) (Config V) ℝ) (x : Config V → ℝ) : ℝ :=
  dotProduct x (A.mulVec x)

@[simp] theorem qform_add (A B : Op V) (x : Config V → ℝ) :
    qform (A+B) x = qform A x + qform B x := by
  simp [qform, Matrix.add_mulVec, dotProduct_add]

@[simp] theorem qform_smul (c : ℝ) (A : Op V) (x : Config V → ℝ) :
    qform (c • A) x = c*qform A x := by
  simp [qform, Matrix.smul_mulVec, dotProduct_smul]

@[simp] theorem qform_sum {I : Type*} [Fintype I]
    (A : I → Op V) (x : Config V → ℝ) :
    qform (∑ i,A i) x = ∑ i,qform (A i) x := by
  simp [qform, Matrix.sum_mulVec, dotProduct_sum]

@[simp] theorem qform_sub (A B : Op V) (x : Config V → ℝ) :
    qform (A-B) x = qform A x-qform B x := by
  simp [qform, Matrix.sub_mulVec, dotProduct_sub]

/-- Actual global triplet-count operator, with the physical rung projector. -/
def number : Op V := ∑ v : V, Torus.siteLift RealRungOperators.h v


def localNumber : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ :=
  RealRungOperators.h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) +
    (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ RealRungOperators.h

theorem localNumber_quadratic (z : LocalBond.RealPair) :
    dotProduct z (localNumber.mulVec z) = LocalBond.numberForm z := by
  simp [localNumber, RealRungOperators.h, LocalRung.rungDiagonal, dotProduct,
    Matrix.mulVec, Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ, LocalBond.numberForm,
    LocalBond.stNorm, LocalBond.ttNorm, LocalBond.offNorm]
  ring

def localGram (g : ℝ) : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ :=
  g • LocalBond.magicBond + (g/2+1/20) • localNumber + (15/2*g^2) • 1

theorem localGram_nonneg (g : ℝ) (hg : 0 ≤ g) (z : LocalBond.RealPair) :
    0 ≤ dotProduct z ((localGram g).mulVec z) := by
  have hh := LocalBond.magicBond_lower_bound g hg z
  have hn : dotProduct z z = LocalBond.normForm z := by
    rw [LocalBond.normForm_eq_sum_sq]
    simp [dotProduct, pow_two]
  simp only [localGram, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    localNumber_quadratic, hn]
  linarith

theorem pairGram_expansion (g : ℝ) (u v : V) (huv : u ≠ v) :
    Torus.pairLift (localGram g) u v =
      g • Torus.pairLift LocalBond.magicBond u v +
      (g/2+1/20) • (Torus.siteLift RealRungOperators.h u+
        Torus.siteLift RealRungOperators.h v) + (15/2*g^2) • (1 : Op V) := by
  simp only [localGram, Torus.pairLift_add, Torus.pairLift_smul, localNumber,
    Torus.pairLift_left _ huv, Torus.pairLift_right _ huv, pairLift_one u v huv]

theorem magicBond_lift (u v : V) (huv : u ≠ v) :
    Torus.pairLift LocalBond.magicBond u v =
      -(∑ a : Fin 6, Torus.siteLift (RealRungOperators.G a) u *
        Torus.siteLift (RealRungOperators.G a) v) := by
  have hlocal : LocalBond.magicBond = (-1 : ℝ) •
      ∑ a : Fin 6, (RealRungOperators.G a) ⊗ₖ (RealRungOperators.G a) := by
    simp [LocalBond.magicBond, LocalBond.magicGenerator, RealRungOperators.G]
  rw [hlocal, Torus.pairLift_smul, Torus.pairLift_sum]
  simp only [← Torus.siteLift_mul_distinct _ _ huv, neg_one_smul]

/-- Actual nearest-neighbor Hamiltonian for two oriented permutation edges per site. -/
def graphHamiltonian (ex ey : Equiv.Perm V) (g : ℝ) : Op V :=
  number - g •
    ((∑ v, ∑ a : Fin 6, Torus.siteLift (RealRungOperators.G a) v *
      Torus.siteLift (RealRungOperators.G a) (ex v)) +
     (∑ v, ∑ a : Fin 6, Torus.siteLift (RealRungOperators.G a) v *
      Torus.siteLift (RealRungOperators.G a) (ey v)))


theorem endpoint_number_sum (e : Equiv.Perm V) (x : Config V → ℝ) :
    (∑ v, (qform (Torus.siteLift RealRungOperators.h v) x+
      qform (Torus.siteLift RealRungOperators.h (e v)) x)) = 2*qform (number : Op V) x := by
  have he : (∑ v, qform (Torus.siteLift RealRungOperators.h (e v)) x) =
      ∑ v, qform (Torus.siteLift RealRungOperators.h v) x :=
    Equiv.sum_comp e (fun v => qform (Torus.siteLift RealRungOperators.h v) x)
  rw [Finset.sum_add_distrib, he]
  simp only [number, qform_sum]
  ring

theorem edge_sum_lower (e : Equiv.Perm V) (he : ∀ v, v ≠ e v)
    (g : ℝ) (hg : 0 ≤ g) (x : Config V → ℝ) :
    -(g+1/10)*qform (number : Op V) x -
      (Fintype.card V : ℝ)*(15/2)*g^2*qform (1 : Op V) x ≤
      g*(∑ v, qform (Torus.pairLift LocalBond.magicBond v (e v)) x) := by
  have hn : 0 ≤ ∑ v : V, qform (Torus.pairLift (localGram g) v (e v)) x :=
    Finset.sum_nonneg fun v _ => pairLift_quadratic_nonneg (localGram g)
      (localGram_nonneg g hg) v (e v) (he v) x
  simp_rw [pairGram_expansion g _ _ (he _), qform_add, qform_smul] at hn
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hn
  simp_rw [qform_add] at hn
  rw [endpoint_number_sum] at hn
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  nlinarith only [hn]

theorem graphHamiltonian_as_bonds (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v) (g : ℝ) :
    graphHamiltonian ex ey g = number + g •
      ((∑ v, Torus.pairLift LocalBond.magicBond v (ex v))+
       (∑ v, Torus.pairLift LocalBond.magicBond v (ey v))) := by
  simp_rw [magicBond_lift _ _ (hx _), magicBond_lift _ _ (hy _)]
  simp only [graphHamiltonian, Finset.sum_neg_distrib, ← neg_add, smul_neg, sub_eq_add_neg]

/-- Degree four gives the exact coefficient 4/5−2g and the exact 15 A g² loss. -/
theorem graphHamiltonian_lower_bound (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : Config V → ℝ) :
    (4/5-2*g)*qform (number : Op V) x -
      15*(Fintype.card V : ℝ)*g^2*qform (1 : Op V) x ≤
      qform (graphHamiltonian ex ey g) x := by
  have h₁ := edge_sum_lower ex hx g hg x
  have h₂ := edge_sum_lower ey hy g hg x
  rw [graphHamiltonian_as_bonds ex ey hx hy, qform_add, qform_smul, qform_add,
    qform_sum, qform_sum]
  nlinarith only [h₁,h₂]

/-- Concrete even rectangular torus. Ordinary square-lattice convention has n,m≥2. -/
theorem fullHamiltonian_lower_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : ℝ) (hg : 0 ≤ g) (x : Torus.FullConfig (2*n) (2*m) → ℝ) :
    (4/5-2*g)*qform (number : Op (Torus.FullVertex (2*n) (2*m))) x -
      15*((2*n)*(2*m) : ℝ)*g^2*qform (1 : Op (Torus.FullVertex (2*n) (2*m))) x ≤
      qform (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g) x := by
  have hh := graphHamiltonian_lower_bound (Torus.xNext n m) (Torus.yNext n m)
    (fun v => (Torus.xNext_ne n m hn v).symm) (fun v => (Torus.yNext_ne n m hm v).symm)
    g hg x
  simpa only [graphHamiltonian, number, Torus.fullHamiltonian, Torus.fullXNext,
    Torus.fullYNext, Torus.xNext, Torus.yNext, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hh

/-- Real quadratic forms and the standard Hilbert-space inner product agree. -/
theorem inner_eq_qform (A : Op V) (x : EuclideanSpace ℝ (Config V)) :
    ⟪x, A.toEuclideanLin x⟫ = qform A (WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
  simp only [star_trivial, dotProduct_comm, qform]

theorem qform_one_eq_norm_sq (x : EuclideanSpace ℝ (Config V)) :
    qform (1 : Op V) (WithLp.ofLp x) = ‖x‖^2 := by
  unfold qform
  rw [Matrix.one_mulVec]
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    (real_inner_self_eq_norm_sq x)

theorem fullHamiltonian_inner_lower_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : ℝ) (hg : 0 ≤ g) (x : EuclideanSpace ℝ (Torus.FullConfig (2*n) (2*m))) :
    (4/5-2*g)*⟪x,(TripletNumber.number : Op (Torus.FullVertex (2*n) (2*m))).toEuclideanLin x⟫ -
      (15*((2*n)*(2*m) : ℝ)*g^2)*‖x‖^2 ≤
      ⟪x,(Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).toEuclideanLin x⟫ := by
  have hh := fullHamiltonian_lower_bound n m hn hm g hg (WithLp.ofLp x)
  rw [qform_one_eq_norm_sq] at hh
  change (4/5-2*g)*qform TripletNumber.number (WithLp.ofLp x) - _ ≤ _ at hh
  simpa only [← inner_eq_qform] using hh

/-- The unchanged physical all-singlet trial has exactly zero energy expectation. -/
theorem fullHamiltonian_vacuum (n m : ℕ) (g : ℝ) :
    Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g
      TripletNumber.vacuum TripletNumber.vacuum = 0 :=
  Torus.hamiltonian_vacuum_diagonal n m RealRungOperators.h RealRungOperators.G g
    RealRungOperators.h_vacuum (fun a => RealRungOperators.G_diagonal_zero a 0)

/-- Hermiticity of the concrete physical real-rung representative. -/
theorem fullHamiltonian_hermitian (L M : ℕ) (g : ℝ) :
    (Torus.fullHamiltonian L M RealRungOperators.h RealRungOperators.G g).IsHermitian := by
  apply Torus.fullHamiltonian_hermitian
  · rw [TripletNumber.rung_h_eq_diagonal]
    exact Matrix.isHermitian_diagonal _
  · exact RealRungOperators.G_antisymmetric

/-- The standard complex Pauli-spin Hamiltonian has exactly this full real
spectrum, including every multiplicity. This is the actual global physical
basis similarity, not an assumed equality of spectra. -/
theorem standardPauli_charpoly (L M : ℕ) (g : ℝ) :
    (PhysicalSpinHamiltonian.fullHamiltonian L M g).charpoly =
      ∏ i : Torus.FullConfig L M,
        (Polynomial.X - Polynomial.C
          ((fullHamiltonian_hermitian L M g).eigenvalues i : ℂ)) := by
  rw [PhysicalSpinHamiltonian.fullHamiltonian_charpoly]
  unfold PhysicalSpinHamiltonian.complexify
  rw [Matrix.charpoly_map, (fullHamiltonian_hermitian L M g).charpoly_eq, Polynomial.map_prod]
  simp

/-- An explicit finite thermal-tail bound for the actual Hamiltonian, with no
assumed number spectrum, physical gap, or ground-energy normalization. -/
theorem fullHamiltonian_thermal_tail (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 2/5) (β : ℝ) (hβ : 0 ≤ β) :
    relativePartition (fullHamiltonian_hermitian (2*n) (2*m) g) β - 1 ≤
      Real.exp (β*(15*((2*n)*(2*m) : ℝ)*g^2)) *
        ((1+3*Real.exp (-β*(4/5-2*g)))^((2*n)*(2*m))-1) := by
  have hh := TripletNumber.relativePartition_tail_le_of_vacuum
    (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g)
    (fullHamiltonian_hermitian (2*n) (2*m) g)
    (4/5-2*g) (15*((2*n)*(2*m) : ℝ)*g^2) (by linarith)
    (fullHamiltonian_inner_lower_bound n m hn hm g hg) β hβ
    (le_of_eq (fullHamiltonian_vacuum n m g))
  simpa only [Fintype.card_prod, Fintype.card_fin] using hh

/-- A finite excitation estimate. The area-dependent loss is explicit, so
this theorem alone makes no infinite-volume positive-gap claim. -/
theorem fullHamiltonian_excitation_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 2/5)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    (4/5-2*g)-15*((2*n)*(2*m) : ℝ)*g^2 ≤
      ascendingEigenvalue (fullHamiltonian_hermitian (2*n) (2*m) g) k -
        groundEnergy (fullHamiltonian_hermitian (2*n) (2*m) g) :=
  TripletNumber.excitationEnergy_lower_of_vacuum
    (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g)
    (fullHamiltonian_hermitian (2*n) (2*m) g)
    (4/5-2*g) (15*((2*n)*(2*m) : ℝ)*g^2) (by linarith)
    (fullHamiltonian_inner_lower_bound n m hn hm g hg)
    (le_of_eq (fullHamiltonian_vacuum n m g)) k hk

#print axioms localGram_nonneg
#print axioms graphHamiltonian_lower_bound
#print axioms fullHamiltonian_lower_bound
#print axioms fullHamiltonian_inner_lower_bound
#print axioms fullHamiltonian_vacuum
#print axioms standardPauli_charpoly
#print axioms fullHamiltonian_thermal_tail
#print axioms fullHamiltonian_excitation_lower
end BilayerDressed.PhysicalGram
