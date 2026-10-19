import Dressed.GlobalResidualAlgebra
import Dressed.PhysicalGramLowerBound

/-! Exact separation of the two bond endpoints from all outside sites. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.GlobalResidual
variable {V : Type*} [Fintype V] [DecidableEq V]
open PhysicalGram

/-- A finite sum split into two distinct endpoints and their complement. -/
theorem sum_two_sites {M : Type*} [AddCommMonoid M]
    (u v : V) (huv : u ≠ v) (f : V → M) :
    (∑ w, f w) = f u + f v + ∑ w : Outside u v, f w := by
  have h₁ := Finset.sum_erase_add (Finset.univ : Finset V) f (by simp : u ∈ (Finset.univ : Finset V))
  have h₂ := Finset.sum_erase_add ((Finset.univ : Finset V).erase u) f
    (by simp [huv.symm] : v ∈ (Finset.univ : Finset V).erase u)
  have he : (∑ w ∈ ((Finset.univ : Finset V).erase u).erase v, f w) =
      ∑ w : Outside u v, f w :=
    Finset.sum_subtype _ (by intro w; simp [Outside, and_comm]) f
  rw [← h₁, ← h₂, he]
  simp only [add_comm, add_left_comm, add_assoc]

/-- A pair polynomial over any commutative real algebra. -/
def pairPolynomial {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) : R :=
  ∑ r, ∑ s, (K r s / 2) • ∑ α : Fin 3, c r α * c s α

/-- The field seen by one endpoint, excluding both local endpoints. -/
def outsideField {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) (u v r : V) (α : Fin 3) : R :=
  ∑ w : Outside u v, (K r w) • c w α

/-- Only pairs with both endpoints outside the selected bond remain here. -/
def outsidePairPolynomial {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) (u v : V) : R :=
  pairPolynomial (fun w : Outside u v => c w) (fun r s => K r s)

/-- The exact local part of the quadratic creation generator. -/
def twoSitePolynomial {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) (u v : V) : R :=
  (∑ α : Fin 3, c u α * outsideField c K u v u α) +
  (∑ α : Fin 3, c v α * outsideField c K u v v α) +
  (K u v) • ∑ α : Fin 3, c u α * c v α

/-- Splitting the standard half-ordered sum introduces neither a missing half
nor a spurious diagonal term. -/
theorem pairPolynomial_split {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (hc : ∀ r α β, c r α * c r β = 0)
    (K : V → V → ℝ) (hK : ∀ r s, K r s = K s r)
    (u v : V) (huv : u ≠ v) :
    pairPolynomial c K = twoSitePolynomial c K u v + outsidePairPolynomial c K u v := by
  let q : V → V → R := fun r s => (K r s / 2) • ∑ α : Fin 3, c r α * c s α
  have qsym (r s : V) : q r s = q s r := by
    simp only [q, hK r s, mul_comm]
  have qdiag (r : V) : q r r = 0 := by simp [q, hc]
  have row (r : V) : (∑ s, q r s) = q r u + q r v + ∑ s : Outside u v, q r s :=
    sum_two_sites u v huv _
  change (∑ r, ∑ s, q r s) = _
  rw [sum_two_sites u v huv, row u, row v]
  simp only [qdiag, zero_add, add_zero, qsym v u]
  simp_rw [row, Finset.sum_add_distrib, qsym _ u, qsym _ v]
  have hd (r s : V) : q r s + q r s =
      (K r s) • ∑ α : Fin 3, c r α * c s α := by
    dsimp only [q]
    rw [← add_smul]
    congr 1
    ring
  have hf (r : V) :
      (∑ s : Outside u v, q r s) + (∑ s : Outside u v, q r s) =
        ∑ α : Fin 3, c r α * outsideField c K u v r α := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hd]
    simp only [outsideField, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
  rw [qsym v u]
  change q u v + (∑ s : Outside u v, q u s) +
      (q u v + ∑ s : Outside u v, q v s) +
      ((∑ s : Outside u v, q u s) + (∑ s : Outside u v, q v s) +
        ∑ r : Outside u v, ∑ s : Outside u v, q r s) = _
  calc
    _ = (q u v + q u v) +
        ((∑ s : Outside u v, q u s) + (∑ s : Outside u v, q u s)) +
        ((∑ s : Outside u v, q v s) + (∑ s : Outside u v, q v s)) +
        (∑ r : Outside u v, ∑ s : Outside u v, q r s) := by abel
    _ = _ := by rw [hd, hf, hf]; unfold twoSitePolynomial outsidePairPolynomial pairPolynomial; dsimp only [q]; abel

end BilayerDressed.GlobalResidual
