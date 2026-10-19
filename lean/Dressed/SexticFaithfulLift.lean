import Dressed.FiniteHomogeneousCreationNorm
import Dressed.FiniteWordHomogeneous
import Dressed.GlobalDressedResidual
import Dressed.FiniteDressedProjection
import Mathlib.Data.List.FinRange

/-!
# Faithful sextic lift with the six-distinct-site constant

Repeated-site hard-core creation monomials must vanish before lifting. A
surviving product of three color-contracted pairs has vacuum norm squared 27,
not the larger norm of an unfiltered bosonic edge polynomial.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.SexticFaithfulLift
open Matrix FiniteOccupation
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Which of the three color contractions contains a given site slot. -/
def pairSlot (i : Fin 6) : Fin 3 := ⟨i.val / 2, by omega⟩

/-- First site slot of a specified contraction. -/
def firstSlot (i : Fin 3) : Fin 6 := ⟨2 * i.val, by omega⟩

@[simp] theorem pairSlot_firstSlot (i : Fin 3) : pairSlot (firstSlot i) = i := by
  fin_cases i <;> decide

/-- Six actual mode labels, with one independent color per pair. -/
def sixWord (sites : Fin 6 → V) (colors : Fin 3 → Fin 3) : List (Mode V) :=
  List.ofFn (fun i => (sites i, colors (pairSlot i)))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem length_sixWord (sites : Fin 6 → V) (colors : Fin 3 → Fin 3) :
    (sixWord sites colors).length = 6 := by simp [sixWord]

omit [Fintype V] [DecidableEq V] in
/-- Distinct physical sites imply distinct modes, for every color choice. -/
theorem sixWord_nodup (sites : Fin 6 → V) (hsites : Function.Injective sites)
    (colors : Fin 3 → Fin 3) : (sixWord sites colors).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact hsites (congrArg Prod.fst h)

/-- There is no factorial enhancement on a six-distinct-site monomial. -/
theorem sixWord_factorial (sites : Fin 6 → V) (hsites : Function.Injective sites)
    (colors : Fin 3 → Fin 3) : RotatedWords.wordFactorial (sixWord sites colors) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Nat.factorial_eq_one.mpr
  simpa only [List.count_eq_countP, beq_eq_decide] using
    (List.nodup_iff_count_le_one.mp (sixWord_nodup sites hsites colors) i)

omit [Fintype V] [DecidableEq V] in
/-- The 27 color choices give distinct occupation words. -/
theorem sixWord_perm_iff (sites : Fin 6 → V) (hsites : Function.Injective sites)
    (colors other : Fin 3 → Fin 3) :
    (sixWord sites colors).Perm (sixWord sites other) ↔ colors = other := by
  constructor
  · intro h
    funext i
    have hm : (sites (firstSlot i), colors (pairSlot (firstSlot i))) ∈ sixWord sites colors := by
      apply List.mem_ofFn.mpr
      exact ⟨firstSlot i, rfl⟩
    have hm' := h.mem_iff.mp hm
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm'
    have he : j = firstSlot i := hsites (congrArg Prod.fst hj)
    subst j
    simpa using (congrArg Prod.snd hj).symm
  · intro h; subst other; exact List.Perm.refl _

/-- Actual unrotated creation words have orthonormal vacuum outputs here. -/
theorem sixWord_inner {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (sites : Fin 6 → V) (hsites : Function.Injective sites)
    (colors other : Fin 3 → Fin 3) :
    RotatedWords.word (M := M) (N := N) 1 (sixWord sites colors) ⬝ᵥ
      RotatedWords.word 1 (sixWord sites other) = if colors = other then 1 else 0 := by
  rw [RotatedWords.word_inner hNM 1 (by simp) _ _ (by simpa using hN) (by simpa using hN)]
  simp only [sixWord_perm_iff sites hsites, sixWord_factorial sites hsites, Nat.cast_one]

/-- Vacuum image of three genuine pair contractions on the listed six sites. -/
def sixSeed {M N : ℕ} (sites : Fin 6 → V) : RotatedWords.Vector V M N :=
  ∑ colors : Fin 3 → Fin 3, RotatedWords.word 1 (sixWord sites colors)

/-- The exact constant behind F₆ ≤ sqrt(27) ell₆. -/
theorem sixSeed_norm_sq {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (sites : Fin 6 → V) (hsites : Function.Injective sites) :
    (sixSeed sites : RotatedWords.Vector V M N) ⬝ᵥ sixSeed sites = 27 := by
  simp only [sixSeed, sum_dotProduct, dotProduct_sum, sixWord_inner hNM hN sites hsites]
  simp

/-- Second site slot of a specified contraction. -/
def secondSlot (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by omega⟩

section CommutativePolynomial
variable {R : Type*} [CommRing R]

/-- Color-contracted pair polynomial in a genuine commutative creation algebra. -/
def pairPolynomial (c : V → Fin 3 → R) (u v : V) : R :=
  ∑ α, c u α * c v α

/-- Six-site color polynomial with three independent contractions. -/
def sixPolynomial (c : V → Fin 3 → R) (sites : Fin 6 → V) : R :=
  ∑ colors : Fin 3 → Fin 3, ∏ i : Fin 6, c (sites i) (colors (pairSlot i))

omit [Fintype V] [DecidableEq V] in
/-- The color sum is exactly three Q factors, without a combinatorial factor. -/
theorem sixPolynomial_eq_pairs (c : V → Fin 3 → R) (sites : Fin 6 → V) :
    sixPolynomial c sites = pairPolynomial c (sites 0) (sites 1) *
      pairPolynomial c (sites 2) (sites 3) * pairPolynomial c (sites 4) (sites 5) := by
  have hp (colors : Fin 3 → Fin 3) :
      (∏ i : Fin 6, c (sites i) (colors (pairSlot i))) =
      ∏ j : Fin 3, c (sites (firstSlot j)) (colors j) *
        c (sites (secondSlot j)) (colors j) := by
    simp [Fin.prod_univ_succ, pairSlot, firstSlot, secondSlot]
    ring
  unfold sixPolynomial
  simp_rw [hp]
  have hsum := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3)))
    (fun j α => c (sites (firstSlot j)) α * c (sites (secondSlot j)) α)
  simp only [Fintype.piFinset_univ] at hsum
  rw [← hsum]
  simp [Fin.prod_univ_succ, firstSlot, secondSlot, pairPolynomial]
  ring

omit [Fintype V] [DecidableEq V] in
/-- Hard-core nilpotence removes every repeated-site monomial, even when its
repeated creators have different colors. -/
theorem sixPolynomial_zero_of_repeated_site (c : V → Fin 3 → R)
    (hc : ∀ u α β, c u α * c u β = 0) (sites : Fin 6 → V)
    (hrepeated : ¬ Function.Injective sites) : sixPolynomial c sites = 0 := by
  classical
  simp only [Function.Injective] at hrepeated
  push_neg at hrepeated
  obtain ⟨i, j, hij, hne⟩ := hrepeated
  apply Finset.sum_eq_zero
  intro colors hcolors
  have hj : j ∈ (Finset.univ : Finset (Fin 6)).erase i := by simp [Ne.symm hne]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ hj, ← mul_assoc]
  have hz : c (sites i) (colors (pairSlot i)) * c (sites j) (colors (pairSlot j)) = 0 := by
    rw [hij]
    exact hc _ _ _
  rw [hz, zero_mul]

end CommutativePolynomial

/-- The six sites appearing in one expanded edge monomial, grouped in Q pairs. -/
def edgeSites (r s i j k l : V) : Fin 6 → V := ![r, i, s, j, k, l]

/-- Exact scalar coefficient from the four outside fields. -/
def edgeCoefficient (K : V → V → ℝ) (r s i j k l : V) : ℝ :=
  K r i * K s j * K r k * K s l

/-- Absolute outside row mass, omitting both endpoints. -/
def outsideRow (K : V → V → ℝ) (r s u : V) : ℝ :=
  ∑ w : PhysicalGram.Outside r s, |K u w|

/-- The faithful scalar mass for one edge; repeated-site terms are already zero. -/
def edgeMass (K : V → V → ℝ) (r s : V) : ℝ :=
  ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
  ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
    if Function.Injective (edgeSites r s i j k l) then
      |edgeCoefficient K r s i j k l| else 0

/-- Deleting repeated-site terms cannot increase the absolute coefficient mass. -/
theorem edgeMass_le (K : V → V → ℝ) (r s : V) :
    edgeMass K r s ≤ outsideRow K r s r ^ 2 * outsideRow K r s s ^ 2 := by
  calc
    _ ≤ ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
        ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
        |edgeCoefficient K r s i j k l| := by
      apply Finset.sum_le_sum; intro i hi
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro k hk
      apply Finset.sum_le_sum; intro l hl
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
    _ = _ := by
      simp only [edgeCoefficient, abs_mul, outsideRow, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Full faithful sextic coefficient mass over the two oriented edge families. -/
def sexticMass (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) : ℝ :=
  (g / 2) * ((∑ r, edgeMass K r (ex r)) + ∑ r, edgeMass K r (ey r))

/-- The exact upper envelope used by the frozen degree-six certificate. -/
def ell6 (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) : ℝ :=
  (g / 2) * ((∑ r, outsideRow K r (ex r) r ^ 2 * outsideRow K r (ex r) (ex r) ^ 2) +
    ∑ r, outsideRow K r (ey r) r ^ 2 * outsideRow K r (ey r) (ey r) ^ 2)

/-- The scalar envelope is nonnegative on the physical coupling interval. -/
theorem ell6_nonneg (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) (hg : 0 ≤ g) :
    0 ≤ ell6 K ex ey g := by
  unfold ell6
  positivity

/-- No graph positivity or absence of coefficient cancellation is assumed. -/
theorem sexticMass_le_ell6 (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) (hg : 0 ≤ g) :
    sexticMass K ex ey g ≤ ell6 K ex ey g := by
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ g / 2)
  exact add_le_add (Finset.sum_le_sum (fun r _ => edgeMass_le K r (ex r)))
    (Finset.sum_le_sum (fun r _ => edgeMass_le K r (ey r)))

section PhysicalExpansion
open GlobalResidual

/-- First outside field contracted with its endpoint. -/
theorem endpoint_field_pair (K : V → V → ℝ) (r s u : V) :
    (∑ α : Fin 3, GlobalResidual.C u α * GlobalResidual.outsideField GlobalResidual.C K r s u α) =
      ∑ i : PhysicalGram.Outside r s, K u i • pairPolynomial GlobalResidual.C u i := by
  simp only [outsideField, Algebra.smul_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [pairPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro α hα
  ring

/-- The third contraction is precisely the product of the two outside rows. -/
theorem outside_fields_pair (K : V → V → ℝ) (r s : V) :
    LocalBond.dot (outsideField C K r s r) (outsideField C K r s s) =
      ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
        (K r k * K s l) • pairPolynomial C (k : V) (l : V) := by
  have hm (α : Fin 3) : outsideField C K r s r α * outsideField C K r s s α =
      ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
        (K r k * K s l) • (C (k : V) α * C (l : V) α) := by
    simp only [outsideField]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l hl
    simp only [Algebra.smul_def, map_mul]
    ring
  simp only [LocalBond.dot, hm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.sum_comm]
  simp only [pairPolynomial, Finset.smul_sum]

/-- Controlled expansion preserving the four outside-index order. -/
theorem four_sum_product {R : Type*} [Ring R] {J : Type*} [Fintype J]
    (a b : J → R) (c : J → J → R) :
    (∑ i, a i) * (∑ j, b j) * (∑ k, ∑ l, c k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i * b j * c k l := by
  calc
    _ = (∑ i, a i * (∑ j, b j)) * (∑ k, ∑ l, c k l) := by rw [Finset.sum_mul]
    _ = ∑ i, (a i * (∑ j, b j)) * (∑ k, ∑ l, c k l) := by rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl; intro i hi
      have he : a i * (∑ j, b j) = ∑ j, a i * b j := by rw [Finset.mul_sum]
      rw [he, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j hj
      simp only [Finset.mul_sum]

/-- Factor the literal sextic polynomial without changing any coefficient. -/
theorem bondResidual6_factor (K : V → V → ℝ) (r s : V) :
    bondResidual6 K r s =
      (∑ α : Fin 3, C r α * outsideField C K r s r α) *
      (∑ β : Fin 3, C s β * outsideField C K r s s β) *
      LocalBond.dot (outsideField C K r s r) (outsideField C K r s s) := by
  simp only [bondResidual6, bondR6, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

/-- Exact four-outside-index expansion of the frozen literal sextic residual. -/
theorem bondResidual6_expansion (K : V → V → ℝ) (r s : V) :
    bondResidual6 K r s =
      ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
      ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
        edgeCoefficient K r s i j k l • sixPolynomial C (edgeSites r s i j k l) := by
  rw [bondResidual6_factor, endpoint_field_pair, endpoint_field_pair, outside_fields_pair,
    four_sum_product]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  apply Finset.sum_congr rfl; intro l hl
  rw [sixPolynomial_eq_pairs]
  simp [edgeSites, edgeCoefficient, Algebra.smul_def, map_mul]
  ring

/-- Physical sextic edge after deleting exactly its zero repeated-site terms. -/
def faithfulPhysicalEdge (K : V → V → ℝ) (r s : V) : creationAlgebra V :=
  ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
  ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
    if Function.Injective (edgeSites r s i j k l) then
      edgeCoefficient K r s i j k l • sixPolynomial C (edgeSites r s i j k l) else 0

/-- Deletion is a proved hard-core identity, not an approximation or a norm bound. -/
theorem faithfulPhysicalEdge_eq (K : V → V → ℝ) (r s : V) :
    faithfulPhysicalEdge K r s = bondResidual6 K r s := by
  rw [bondResidual6_expansion]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  apply Finset.sum_congr rfl; intro l hl
  split_ifs with hsites
  · rfl
  · rw [sixPolynomial_zero_of_repeated_site C C_mul_same _ hsites, smul_zero]

end PhysicalExpansion

section ActualLift

/-- Actual six-creation polynomial on the total occupation cutoff. -/
def sixLift {M N : ℕ} (sites : Fin 6 → V) : TotalCutoff.Op V M N :=
  ∑ colors : Fin 3 → Fin 3,
    ((sixWord sites colors).map (fun i => TotalCutoff.create (M := M) (N := N) i)).prod

theorem rotated_create_identity {M N : ℕ} (i : Mode V) :
    RotatedWords.create (M := M) (N := N) 1 i = TotalCutoff.create i := by
  simp [RotatedWords.create, Matrix.one_apply]

/-- Word recursion is the literal product of actual unrotated creation matrices. -/
theorem word_identity_eq_product {M N : ℕ} (L : List (Mode V)) :
    RotatedWords.word (M := M) (N := N) 1 L =
      (L.map (fun i => TotalCutoff.create (M := M) (N := N) i)).prod *ᵥ
        RotatedWords.vacuumVector := by
  induction L with
  | nil => simp [RotatedWords.word]
  | cons i L ih =>
    simp only [RotatedWords.word_cons, rotated_create_identity, ih,
      List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

/-- The exact vacuum image of the actual polynomial used in the lift. -/
theorem sixLift_vacuum {M N : ℕ} (sites : Fin 6 → V) :
    sixLift sites *ᵥ (RotatedWords.vacuumVector : RotatedWords.Vector V M N) = sixSeed sites := by
  simp only [sixLift, Matrix.sum_mulVec, sixSeed, word_identity_eq_product]

/-- Genuine Hilbert norm for a finite occupation vacuum image. -/
def vacuumImage {M N : ℕ} (A : TotalCutoff.Op V M N) :
    EuclideanSpace ℝ (TotalCutoff.Basis V M N) :=
  WithLp.toLp 2 (A *ᵥ RotatedWords.vacuumVector)

/-- The exact sqrt(27) norm, in the actual Euclidean Hilbert structure. -/
theorem sixLift_vacuum_norm {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (sites : Fin 6 → V) (hsites : Function.Injective sites) :
    ‖vacuumImage (sixLift sites : TotalCutoff.Op V M N)‖ = Real.sqrt 27 := by
  have hs : ‖vacuumImage (sixLift sites : TotalCutoff.Op V M N)‖ ^ 2 = 27 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [vacuumImage, sixLift_vacuum, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact sixSeed_norm_sq hNM hN sites hsites
  nlinarith [norm_nonneg (vacuumImage (sixLift sites : TotalCutoff.Op V M N)),
    Real.sqrt_nonneg (27 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)]

/-- Faithful bosonic lift of one edge: the repeated-site filter is applied
before the surviving creation products are lifted. -/
def faithfulEdge {M N : ℕ} (K : V → V → ℝ) (r s : V) : TotalCutoff.Op V M N :=
  ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
  ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
    if Function.Injective (edgeSites r s i j k l) then
      edgeCoefficient K r s i j k l • sixLift (edgeSites r s i j k l) else 0

/-- The actual faithful degree-six residual for both physical edge families. -/
def faithfulResidual6 {M N : ℕ} (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) :
    TotalCutoff.Op V M N :=
  (g / 2) • ((∑ r, faithfulEdge K r (ex r)) + ∑ r, faithfulEdge K r (ey r))

@[simp] theorem vacuumImage_zero {M N : ℕ} :
    vacuumImage (0 : TotalCutoff.Op V M N) = 0 := by
  ext ν
  simp [vacuumImage]

@[simp] theorem vacuumImage_add {M N : ℕ} (A B : TotalCutoff.Op V M N) :
    vacuumImage (A + B) = vacuumImage A + vacuumImage B := by
  ext ν
  simp [vacuumImage, Matrix.add_mulVec]

@[simp] theorem vacuumImage_smul {M N : ℕ} (a : ℝ) (A : TotalCutoff.Op V M N) :
    vacuumImage (a • A) = a • vacuumImage A := by
  ext ν
  simp [vacuumImage, Matrix.smul_mulVec]

@[simp] theorem vacuumImage_sum {M N : ℕ} {J : Type*} (s : Finset J)
    (A : J → TotalCutoff.Op V M N) : vacuumImage (∑ j ∈ s, A j) = ∑ j ∈ s, vacuumImage (A j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert, hj, ih]

/-- The precise faithful edge vacuum bound, retaining the sqrt(27) constant. -/
theorem faithfulEdge_vacuum_norm_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (K : V → V → ℝ) (r s : V) :
    ‖vacuumImage (faithfulEdge K r s : TotalCutoff.Op V M N)‖ ≤ Real.sqrt 27 * edgeMass K r s := by
  simp only [faithfulEdge, vacuumImage_sum]
  calc
    _ ≤ ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
        ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
        ‖vacuumImage (if Function.Injective (edgeSites r s i j k l) then
          edgeCoefficient K r s i j k l • (sixLift (edgeSites r s i j k l) : TotalCutoff.Op V M N)
          else 0)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro j hj
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro k hk
      exact norm_sum_le _ _
    _ = _ := by
      simp only [edgeMass, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk
      apply Finset.sum_congr rfl; intro l hl
      by_cases hs : Function.Injective (edgeSites r s i j k l)
      · simp [hs, norm_smul, Real.norm_eq_abs, sixLift_vacuum_norm hNM hN _ hs, mul_comm]
      · simp [hs]

/-- Complete actual faithful vacuum seed bound in terms of its coefficient mass. -/
theorem faithfulResidual6_vacuum_norm_le_mass {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) (hg : 0 ≤ g) :
    ‖vacuumImage (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N)‖ ≤
      Real.sqrt 27 * sexticMass K ex ey g := by
  simp only [faithfulResidual6, vacuumImage_smul, vacuumImage_add, vacuumImage_sum, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g / 2)]
  have hx := (norm_sum_le Finset.univ (fun r => vacuumImage (faithfulEdge K r (ex r) : TotalCutoff.Op V M N))).trans (Finset.sum_le_sum (fun r _ => faithfulEdge_vacuum_norm_le (M := M) (N := N) hNM hN K r (ex r)))
  have hy := (norm_sum_le Finset.univ (fun r => vacuumImage (faithfulEdge K r (ey r) : TotalCutoff.Op V M N))).trans (Finset.sum_le_sum (fun r _ => faithfulEdge_vacuum_norm_le (M := M) (N := N) hNM hN K r (ey r)))
  have hh := (norm_add_le _ _).trans (add_le_add hx hy)
  have hg2 : 0 ≤ g / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hh hg2
  simpa only [sexticMass, ← Finset.mul_sum, ← mul_add, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The frozen sextic amplification constant, for the actual faithful lift. -/
theorem faithfulResidual6_vacuum_norm_le_ell6 {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) (hg : 0 ≤ g) :
    ‖vacuumImage (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N)‖ ≤
      Real.sqrt 27 * ell6 K ex ey g :=
  (faithfulResidual6_vacuum_norm_le_mass hNM hN K ex ey g hg).trans
    (mul_le_mul_of_nonneg_left (sexticMass_le_ell6 K ex ey g hg) (Real.sqrt_nonneg 27))

/-- Squared form directly matching the frozen scalar certificate F₆ = 27 ell₆². -/
theorem faithfulResidual6_vacuum_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) (hg : 0 ≤ g) :
    ‖vacuumImage (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N)‖ ^ 2 ≤
      27 * ell6 K ex ey g ^ 2 := by
  have h := faithfulResidual6_vacuum_norm_le_ell6 (M := M) (N := N) hNM hN K ex ey g hg
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 27)
    (ell6_nonneg K ex ey g hg))).mpr h
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)] using hs

/-- An explicit scalar-envelope premise for a subsequent whole-interval cubic
instantiation. No endpoint estimate is silently substituted for this premise. -/
theorem faithfulResidual6_vacuum_norm_sq_le_envelope {M N : ℕ}
    (hNM : N ≤ M) (hN : 6 ≤ N) (K : V → V → ℝ) (ex ey : V → V)
    (g : ℝ) (hg : 0 ≤ g) {L : ℝ} (hL : ell6 K ex ey g ≤ L) :
    ‖vacuumImage (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N)‖ ^ 2 ≤
      27 * L ^ 2 := by
  apply (faithfulResidual6_vacuum_norm_sq_le hNM hN K ex ey g hg).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 27)
  exact (sq_le_sq₀ (ell6_nonneg K ex ey g hg)
    ((ell6_nonneg K ex ey g hg).trans hL)).mpr hL

/-- Coercing the physical six-site polynomial produces the literal ordered
matrix words used by the no-repair intertwiner. -/
theorem coe_sixPolynomial (sites : Fin 6 → V) :
    ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V) =
      ∑ colors : Fin 3 → Fin 3,
        ((sixWord sites colors).map (fun i => globalCreate i.1 i.2)).prod := by
  simp only [sixPolynomial, AddSubmonoidClass.coe_finset_sum]
  apply Finset.sum_congr rfl
  intro colors hcolors
  rw [← List.prod_ofFn]
  change (GlobalResidual.creationAlgebra V).val
    ((List.ofFn (fun i => GlobalResidual.C (sites i) (colors (pairSlot i)))).prod) = _
  rw [map_list_prod]
  simp only [sixWord, List.map_ofFn, Function.comp_def]
  rfl

/-- Exact one-sided physical projection of the actual six-creator polynomial. -/
theorem physical_transpose_sixLift {M : ℕ} (hM : 2 ≤ M) (sites : Fin 6 → V) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
      (sixLift sites : TotalCutoff.Op V M (Fintype.card V)) =
      ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) *
        (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  simp only [sixLift, Matrix.mul_sum, FiniteDressed.physical_transpose_word hM,
    coe_sixPolynomial, Matrix.sum_mul]

/-- Faithful edge lifting projects to the complete literal edge residual. -/
theorem physical_transpose_faithfulEdge {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (r s : V) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
      (faithfulEdge K r s : TotalCutoff.Op V M (Fintype.card V)) =
      (GlobalResidual.bondResidual6 K r s : ConfigurationMatrix V) *
        (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  rw [← faithfulPhysicalEdge_eq]
  simp only [faithfulEdge, faithfulPhysicalEdge, Matrix.mul_sum,
    AddSubmonoidClass.coe_finset_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  apply Finset.sum_congr rfl; intro l hl
  by_cases hs : Function.Injective (edgeSites r s i j k l)
  · simp only [if_pos hs, Subalgebra.coe_smul, Matrix.mul_smul, Matrix.smul_mul,
      physical_transpose_sixLift hM]
  · simp [hs]

/-- Exact physical projection to the frozen full residual6, including both
edge families and the g/2 factor. No projection equality is assumed. -/
theorem physical_transpose_faithfulResidual6 {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
      (faithfulResidual6 K ex ey g : TotalCutoff.Op V M (Fintype.card V)) =
      (GlobalResidual.residual6 K ex ey g : ConfigurationMatrix V) *
        (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  simp only [faithfulResidual6, GlobalResidual.residual6, Subalgebra.coe_smul,
    Subalgebra.coe_add, AddSubmonoidClass.coe_finset_sum, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    physical_transpose_faithfulEdge hM]

/-- Explicit normalized occupation coefficients of one six-site QQQ polynomial. -/
def sixCoefficients (sites : Fin 6 → V) (α : Mode V → ℕ) : ℝ :=
  ∑ colors : Fin 3 → Fin 3, WordHomogeneous.wordCoefficient (sixWord sites colors) α

/-- Exact concrete homogeneous representation, including the normalization. -/
theorem sixLift_eq_homogeneous {M N : ℕ} (sites : Fin 6 → V) :
    (sixLift sites : TotalCutoff.Op V M N) =
      Homogeneous.homogeneousOperator 6 (sixCoefficients sites) := by
  unfold sixLift sixCoefficients
  rw [WordHomogeneous.homogeneousOperator_sum]
  apply Finset.sum_congr rfl
  intro colors hcolors
  exact WordHomogeneous.word_eq_homogeneousOperator _ (length_sixWord sites colors)

/-- Coefficients after the physical repeated-site deletion, before lifting. -/
def faithfulEdgeCoefficients (K : V → V → ℝ) (r s : V) (α : Mode V → ℕ) : ℝ :=
  ∑ i : PhysicalGram.Outside r s, ∑ j : PhysicalGram.Outside r s,
  ∑ k : PhysicalGram.Outside r s, ∑ l : PhysicalGram.Outside r s,
    if Function.Injective (edgeSites r s i j k l) then
      edgeCoefficient K r s i j k l * sixCoefficients (edgeSites r s i j k l) α else 0

theorem faithfulEdge_eq_homogeneous {M N : ℕ} (K : V → V → ℝ) (r s : V) :
    (faithfulEdge K r s : TotalCutoff.Op V M N) =
      Homogeneous.homogeneousOperator 6 (faithfulEdgeCoefficients K r s) := by
  unfold faithfulEdge faithfulEdgeCoefficients
  simp only [WordHomogeneous.homogeneousOperator_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  apply Finset.sum_congr rfl; intro l hl
  by_cases hs : Function.Injective (edgeSites r s i j k l)
  · simp only [if_pos hs, WordHomogeneous.homogeneousOperator_smul, sixLift_eq_homogeneous]
  · simp only [if_neg hs, WordHomogeneous.homogeneousOperator_zero]

/-- Complete concrete degree-six coefficient function for the actual residual. -/
def faithfulCoefficients (K : V → V → ℝ) (ex ey : V → V) (g : ℝ)
    (α : Mode V → ℕ) : ℝ :=
  (g / 2) * ((∑ r, faithfulEdgeCoefficients K r (ex r) α) +
    ∑ r, faithfulEdgeCoefficients K r (ey r) α)

/-- The faithful residual is exactly the operator consumed by the frozen
homogeneous amplification theorem, not an operator with assumed degree. -/
theorem faithfulResidual6_eq_homogeneous {M N : ℕ} (K : V → V → ℝ)
    (ex ey : V → V) (g : ℝ) :
    (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N) =
      Homogeneous.homogeneousOperator 6 (faithfulCoefficients K ex ey g) := by
  unfold faithfulResidual6 faithfulCoefficients
  simp only [WordHomogeneous.homogeneousOperator_smul,
    WordHomogeneous.homogeneousOperator_add, WordHomogeneous.homogeneousOperator_sum,
    faithfulEdge_eq_homogeneous]

/-- Actual degree-six support, suitable for orthogonal finite pair-grade sums. -/
theorem faithfulResidual6_grade {M N n : ℕ} (K : V → V → ℝ)
    (ex ey : V → V) (g : ℝ) {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) :
    RotatedWords.HasGrade (n + 6) (faithfulResidual6 K ex ey g *ᵥ x) := by
  rw [faithfulResidual6_eq_homogeneous]
  exact Homogeneous.homogeneousOperator_grade _ _ hx

end ActualLift

end BilayerDressed.SexticFaithfulLift
