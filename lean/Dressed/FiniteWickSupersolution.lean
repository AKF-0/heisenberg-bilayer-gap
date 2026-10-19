import Mathlib

/-!
# Finite entrywise covariance supersolutions

This module proves finite matrix inequalities only.  It does not assume or
assert a physical Gaussian/Wick identity.  A separate creation-operator proof
must supply the finite moment recurrence before these comparison lemmas apply.
The parameter `rowSquare` is a squared row-l2 bound, NOT a maximum-entry bound.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteWick
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite nonnegative row contraction has no positive subharmonic vector. -/
theorem row_contraction_le_zero (P : Matrix ι ι ℝ) (q : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hq : q < 1)
    (hrow : ∀ i, ∑ j, P i j ≤ q)
    (f : ι → ℝ) (hf : ∀ i, f i ≤ ∑ j, P i j * f j) :
    ∀ i, f i ≤ 0 := by
  classical
  intro i
  by_contra hi
  have hip : 0 < f i := lt_of_not_ge hi
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image Finset.univ f
    ⟨i, Finset.mem_univ i⟩
  have him : f i ≤ f m := hmax i (Finset.mem_univ i)
  have hmp : 0 < f m := lt_of_lt_of_le hip him
  have hs : (∑ j, P m j * f j) ≤ q * f m := by
    calc
      _ ≤ ∑ j, P m j * f m := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hP m j)
      _ = (∑ j, P m j) * f m := by rw [Finset.sum_mul]
      _ ≤ q * f m := mul_le_mul_of_nonneg_right (hrow m) hmp.le
  have hc := hf m
  nlinarith

/-- Comparison of a finite subsolution and supersolution; no inverse is used. -/
theorem subsolution_le_supersolution (P : Matrix ι ι ℝ) (q : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hq : q < 1)
    (hrow : ∀ i, ∑ j, P i j ≤ q)
    (f v c : ι → ℝ)
    (hf : ∀ i, f i ≤ c i + ∑ j, P i j * f j)
    (hv : ∀ i, c i + ∑ j, P i j * v j ≤ v i) :
    ∀ i, f i ≤ v i := by
  have hd : ∀ i, f i - v i ≤ ∑ j, P i j * (f j - v j) := by
    intro i
    have he : (∑ j, P i j * (f j - v j)) =
        (∑ j, P i j * f j) - ∑ j, P i j * v j := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [he]
    linarith [hf i, hv i]
  have hh := row_contraction_le_zero P q hP hq hrow (fun i => f i-v i) hd
  exact fun i => sub_nonpos.mp (hh i)

/-- Entrywise nonnegativity of the square of a nonnegative finite matrix. -/
theorem square_nonneg (B : Matrix ι ι ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (B * B) i j := by
  intro i j
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hB i k) (hB k j)

/-- Row mass at most κ gives square row mass at most κ². -/
theorem square_row_le (B : Matrix ι ι ℝ) (κ : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hκ : 0 ≤ κ)
    (hrow : ∀ i, ∑ j, B i j ≤ κ) :
    ∀ i, ∑ j, (B*B) i j ≤ κ^2 := by
  intro i
  calc
    _ = ∑ k, B i k * (∑ j, B k j) := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ k, B i k * κ := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hrow k) (hB i k)
    _ = (∑ k, B i k) * κ := by rw [Finset.sum_mul]
    _ ≤ κ * κ := mul_le_mul_of_nonneg_right (hrow i) hκ
    _ = κ^2 := by ring

/-- Symmetry and squared row-l2 bounds control every square entry. -/
theorem square_entry_le_rowSquare (B : Matrix ι ι ℝ) (rowSquare : ℝ)
    (hsym : ∀ i j, B i j = B j i)
    (hsq : ∀ i, ∑ j, (B i j)^2 ≤ rowSquare) :
    ∀ i j, (B*B) i j ≤ rowSquare := by
  intro i j
  have ht : ∀ k, 2 * (B i k * B k j) ≤ (B i k)^2 + (B j k)^2 := by
    intro k
    rw [hsym k j]
    nlinarith [sq_nonneg (B i k - B j k)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => ht k)
  have he : 2 * (B*B) i j ≤ (∑ k, (B i k)^2) + ∑ k, (B j k)^2 := by
    simpa only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_add_distrib] using hh
  linarith [hsq i, hsq j]

/-- The cubic entry bound uses squared row-l2, not maximum entry. -/
theorem cube_entry_le (B : Matrix ι ι ℝ) (κ rowSquare : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hsym : ∀ i j, B i j = B j i)
    (hrow : ∀ i, ∑ j, B i j ≤ κ)
    (hsq : ∀ i, ∑ j, (B i j)^2 ≤ rowSquare) (hsq0 : 0 ≤ rowSquare) :
    ∀ i j, (B * (B*B)) i j ≤ κ * rowSquare := by
  intro i j
  calc
    _ ≤ ∑ k, B i k * rowSquare := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (square_entry_le_rowSquare B rowSquare hsym hsq k j)
        (hB i k)
    _ = (∑ k, B i k) * rowSquare := by rw [Finset.sum_mul]
    _ ≤ κ * rowSquare := mul_le_mul_of_nonneg_right (hrow i) hsq0

/-- Constant-entry correction to the actual positive kernel. -/
def covarianceMajorant (B : Matrix ι ι ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  fun i j => B i j + τ

theorem covarianceMajorant_nonneg (B : Matrix ι ι ℝ) (τ : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hτ : 0 ≤ τ) :
    ∀ i j, 0 ≤ covarianceMajorant B τ i j :=
  fun i j => add_nonneg (hB i j) hτ

theorem covarianceMajorant_symmetric (B : Matrix ι ι ℝ) (τ : ℝ)
    (hsym : ∀ i j, B i j = B j i) :
    ∀ i j, covarianceMajorant B τ i j = covarianceMajorant B τ j i := by
  intro i j
  simp only [covarianceMajorant, hsym i j]

/-- Actual finite covariance supersolution, with all norm-data hypotheses explicit. -/
theorem covarianceMajorant_supersolution (B : Matrix ι ι ℝ) (κ rowSquare τ : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hsym : ∀ i j, B i j = B j i)
    (hκ : 0 ≤ κ) (hsq0 : 0 ≤ rowSquare) (hτ : 0 ≤ τ)
    (hrow : ∀ i, ∑ j, B i j ≤ κ)
    (hsq : ∀ i, ∑ j, (B i j)^2 ≤ rowSquare)
    (hscalar : κ * rowSquare ≤ (1-κ^2)*τ) :
    ∀ i j, B i j + ((B*B) * covarianceMajorant B τ) i j ≤
      covarianceMajorant B τ i j := by
  intro i j
  have he : ((B*B) * covarianceMajorant B τ) i j =
      (B * (B*B)) i j + τ * ∑ k, (B*B) i k := by
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, covarianceMajorant, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hc := cube_entry_le B κ rowSquare hB hsym hrow hsq hsq0 i j
  have hr := mul_le_mul_of_nonneg_left (square_row_le B κ hB hκ hrow i) hτ
  rw [he]
  change B i j + ((B*(B*B)) i j + τ * ∑ k, (B*B) i k) ≤ B i j + τ
  nlinarith

/-- A finite weighted-column update. Repeated column indices are allowed.
The input recurrence must be proved separately for actual physical moments. -/
theorem weighted_column_comparison {α : Type*} [Fintype α]
    (B L : Matrix ι ι ℝ) (q : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hq : q < 1)
    (hrow : ∀ i, ∑ j, (B*B) i j ≤ q)
    (hL : ∀ i j, B i j + ((B*B)*L) i j ≤ L i j)
    (j : α → ι) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : ι → ℝ)
    (hf : ∀ i, f i ≤ (∑ a, B i (j a)*w a) + ∑ k, (B*B) i k*f k) :
    ∀ i, f i ≤ ∑ a, L i (j a)*w a := by
  apply subsolution_le_supersolution (B*B) q (square_nonneg B hB) hq hrow
    f (fun i => ∑ a, L i (j a)*w a) (fun i => ∑ a, B i (j a)*w a) hf
  intro i
  calc
    _ = ∑ a, (B i (j a) + ((B*B)*L) i (j a))*w a := by
      simp only [add_mul, Finset.sum_add_distrib, Matrix.mul_apply, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (hL i (j a)) (hw a)

/-- The exact rational correction, under a strict row contraction. -/
theorem exact_covariance_correction (B : Matrix ι ι ℝ) (κ rowSquare : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hsym : ∀ i j, B i j = B j i)
    (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hsq0 : 0 ≤ rowSquare)
    (hrow : ∀ i, ∑ j, B i j ≤ κ)
    (hsq : ∀ i, ∑ j, (B i j)^2 ≤ rowSquare) :
    ∀ i j, B i j + ((B*B) * covarianceMajorant B (κ*rowSquare/(1-κ^2))) i j ≤
      covarianceMajorant B (κ*rowSquare/(1-κ^2)) i j := by
  have hd : 0 < 1-κ^2 := by nlinarith
  apply covarianceMajorant_supersolution B κ rowSquare (κ*rowSquare/(1-κ^2))
    hB hsym hκ hsq0 (by positivity) hrow hsq
  exact le_of_eq (by field_simp)

/-- Scalar constants only: the actual kernel must establish the row-square input. -/
theorem seed16_scalar_correction :
    (493/4000 : ℝ) * (362417/128000000) =
      (1-(493/4000 : ℝ)^2)*(178671581/504222432000) := by norm_num

theorem seed32_scalar_correction :
    (493/4000 : ℝ) * (1443579/512000000) =
      (1-(493/4000 : ℝ)^2)*(237228149/672296576000) := by norm_num

theorem seed64_scalar_correction :
    (493/4000 : ℝ) * (143749/51200000) =
      (1-(493/4000 : ℝ)^2)*(70868257/201688972800) := by norm_num

/-- Preserve independent color sectors rather than adding an all-color constant. -/
def colorLift {χ : Type*} [DecidableEq χ] (B : Matrix ι ι ℝ) :
    Matrix (ι × χ) (ι × χ) ℝ := fun u v => if u.2=v.2 then B u.1 v.1 else 0

theorem colorLift_mul {χ : Type*} [Fintype χ] [DecidableEq χ]
    (B C : Matrix ι ι ℝ) :
    (colorLift (χ := χ) B)*(colorLift C)=colorLift (B*C) := by
  ext u v
  simp only [Matrix.mul_apply, colorLift, Fintype.sum_prod_type]
  by_cases h : u.2=v.2
  · simp [h]
  · simp [h]

theorem colorLift_row_sum {χ : Type*} [Fintype χ] [DecidableEq χ]
    (B : Matrix ι ι ℝ) (u : ι × χ) :
    (∑ v, colorLift B u v)=∑ j, B u.1 j := by
  simp [colorLift, Fintype.sum_prod_type]

theorem colorLift_supersolution {χ : Type*} [Fintype χ] [DecidableEq χ]
    (B L : Matrix ι ι ℝ)
    (hL : ∀ i j, B i j + ((B*B)*L) i j ≤ L i j) :
    ∀ i j : ι × χ, colorLift B i j +
      ((((colorLift (χ := χ) B)*(colorLift (χ := χ) B))*colorLift (χ := χ) L) : Matrix (ι × χ) (ι × χ) ℝ) i j ≤ colorLift L i j := by
  rw [colorLift_mul, colorLift_mul]
  intro i j
  by_cases h : i.2=j.2
  · simpa [colorLift,h] using hL i.1 j.1
  · simp [colorLift,h]

end BilayerDressed.FiniteWick
