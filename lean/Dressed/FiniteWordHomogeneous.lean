import Dressed.FiniteHomogeneousCreationNorm

/-! Every finite weighted polynomial of genuine fixed-length creation words has
an explicit normalized homogeneous coefficient representation. The factorial
normalization is retained for arbitrary repeated modes. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation.WordHomogeneous
open Matrix Homogeneous
set_option maxHeartbeats 250000
set_option maxRecDepth 2000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Occupation multiplicities of the actual finite creation word. -/
def wordOccupation (L : List (Mode V)) : Mode V → ℕ := fun i => L.count i

@[simp] theorem degree_wordOccupation (L : List (Mode V)) :
    (∑ i, wordOccupation L i) = L.length := by
  induction L with
  | nil => simp [wordOccupation]
  | cons i L ih =>
    simp only [wordOccupation, List.count_cons, beq_iff_eq, Finset.sum_add_distrib]
    simpa [wordOccupation] using congrArg (fun n : ℕ => n + 1) ih

/-- Vacuum coefficient of the unnormalized creation word. -/
def wordCoefficient (L : List (Mode V)) (α : Mode V → ℕ) : ℝ :=
  if α = wordOccupation L then Real.sqrt (RotatedWords.wordFactorial L : ℝ) else 0

@[simp] theorem homogeneousOperator_zero {M N : ℕ} (d : ℕ) :
    homogeneousOperator (V := V) (M := M) (N := N) d (fun _ => 0) = 0 := by
  simp [homogeneousOperator]

theorem homogeneousOperator_smul {M N : ℕ} (d : ℕ) (c : ℝ)
    (r : (Mode V → ℕ) → ℝ) :
    homogeneousOperator (M := M) (N := N) d (fun α => c * r α) =
      c • homogeneousOperator d r := by
  simp [homogeneousOperator, Finset.smul_sum, smul_smul]

theorem homogeneousOperator_sum {M N : ℕ} {J : Type*} (d : ℕ) (s : Finset J)
    (r : J → (Mode V → ℕ) → ℝ) :
    homogeneousOperator (M := M) (N := N) d (fun α => ∑ j ∈ s, r j α) =
      ∑ j ∈ s, homogeneousOperator d (r j) := by
  simp only [homogeneousOperator, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem homogeneousOperator_add {M N : ℕ} (d : ℕ) (r t : (Mode V → ℕ) → ℝ) :
    homogeneousOperator (M := M) (N := N) d (fun α => r α + t α) =
      homogeneousOperator d r + homogeneousOperator d t := by
  simp [homogeneousOperator, add_smul, Finset.sum_add_distrib]

/-- Coefficient delta gives precisely one normalized actual monomial. -/
theorem homogeneousOperator_single {M N : ℕ} (d : ℕ) (α : Mode V → ℕ)
    (hα : α ∈ gradeIndices d) (c : ℝ) :
    homogeneousOperator (M := M) (N := N) d (fun β => if β = α then c else 0) =
      c • TotalCutoff.compress (normalizedMonomial α) := by
  simp [homogeneousOperator, ite_smul, hα]

/-- The recursive actual word and the literal matrix-list product agree. -/
theorem totalCreationWord_eq_product {M N : ℕ} (L : List (Mode V)) :
    totalCreationWord (M := M) (N := N) L =
      (L.map (fun i => TotalCutoff.create (M := M) (N := N) i)).prod := by
  induction L with
  | nil => rfl
  | cons i L ih => simp [totalCreationWord, ih]

/-- No homogeneous representation is assumed: it follows from the proved
actual normalized-monomial action, with its square-root factorial. -/
theorem word_eq_homogeneousOperator {M N d : ℕ} (L : List (Mode V)) (hL : L.length = d) :
    (L.map (fun i => TotalCutoff.create (M := M) (N := N) i)).prod =
      homogeneousOperator d (wordCoefficient L) := by
  change _ = homogeneousOperator d (fun α =>
    if α = wordOccupation L then Real.sqrt (RotatedWords.wordFactorial L : ℝ) else 0)
  rw [homogeneousOperator_single d (wordOccupation L)
    (mem_gradeIndices.mpr (by rw [degree_wordOccupation, hL]))]
  calc
    _ = TotalCutoff.compress (creationWord L) := by
      rw [compress_creationWord, totalCreationWord_eq_product]
    _ = TotalCutoff.compress (Real.sqrt (RotatedWords.wordFactorial L : ℝ) •
        normalizedKernel (wordOccupation L)) := by rw [creationWord_eq_kernel]; rfl
    _ = Real.sqrt (RotatedWords.wordFactorial L : ℝ) •
        TotalCutoff.compress (normalizedMonomial (wordOccupation L)) := by
      rw [normalizedMonomial_eq_kernel]
      rfl

/-- Explicit coefficients of an arbitrary finite weighted word polynomial. -/
def polynomialCoefficient {J : Type*} (s : Finset J) (c : J → ℝ)
    (words : J → List (Mode V)) (α : Mode V → ℕ) : ℝ :=
  ∑ j ∈ s, c j * wordCoefficient (words j) α

/-- Every finite fixed-degree actual word polynomial is a concrete homogeneous
operator, including repeated modes and cutoff zeros. -/
theorem wordPolynomial_eq_homogeneousOperator {M N d : ℕ} {J : Type*} (s : Finset J)
    (c : J → ℝ) (words : J → List (Mode V)) (hwords : ∀ j ∈ s, (words j).length = d) :
    (∑ j ∈ s, c j • ((words j).map
      (fun i => TotalCutoff.create (M := M) (N := N) i)).prod) =
      homogeneousOperator d (polynomialCoefficient s c words) := by
  unfold polynomialCoefficient
  rw [homogeneousOperator_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [homogeneousOperator_smul, word_eq_homogeneousOperator (words j) (hwords j hj)]

end BilayerDressed.FiniteOccupation.WordHomogeneous
