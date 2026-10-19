import Mathlib

/-! Explicit finite row-sum estimates used by the constructive pair kernel.
These bounds concern actual matrix entries, not an external norm oracle. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def absRowSum (A : Matrix ι ι ℝ) (i : ι) : ℝ := ∑ j, |A i j|
def HasAbsRowBound (A : Matrix ι ι ℝ) (a : ℝ) : Prop := ∀ i, absRowSum A i≤a

theorem absRowSum_nonneg (A : Matrix ι ι ℝ) (i : ι) : 0≤absRowSum A i :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem absRowSum_add_le (A B : Matrix ι ι ℝ) (i : ι) :
    absRowSum (A+B) i≤absRowSum A i+absRowSum B i := by
  unfold absRowSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => abs_add_le (A i j) (B i j)

theorem absRowSum_smul (r : ℝ) (A : Matrix ι ι ℝ) (i : ι) :
    absRowSum (r • A) i=|r| * absRowSum A i := by
  simp [absRowSum, abs_mul, Finset.mul_sum]

/-- Matrix multiplication is bounded in the explicitly defined maximum row-sum norm. -/
theorem absRowSum_mul_le (A B : Matrix ι ι ℝ) (b : ℝ)
    (hB : HasAbsRowBound B b) (i : ι) : absRowSum (A*B) i≤absRowSum A i*b := by
  unfold absRowSum
  calc
    (∑ j, |(A*B) i j|) ≤ ∑ j, ∑ k, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa [Matrix.mul_apply, abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun k : ι => A i k*B k j) Finset.univ)
    _ = ∑ k, |A i k| * absRowSum B k := by
      rw [Finset.sum_comm]
      simp only [absRowSum, Finset.mul_sum]
    _ ≤ ∑ k, |A i k| * b :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem HasAbsRowBound.mul (A B : Matrix ι ι ℝ) (a b : ℝ)
    (hA : HasAbsRowBound A a) (hB : HasAbsRowBound B b) (hb : 0≤b) :
    HasAbsRowBound (A*B) (a*b) := by
  intro i
  exact (absRowSum_mul_le A B b hB i).trans (mul_le_mul_of_nonneg_right (hA i) hb)

/-- An individual entry is bounded by its containing absolute row sum. -/
theorem abs_entry_le_absRowSum (A : Matrix ι ι ℝ) (i j : ι) : |A i j|≤absRowSum A i :=
  Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)

/-- Mixed entrywise/row-sum bounds directly control the squared Frobenius sum. -/
theorem sum_sq_le_entry_row (A : Matrix ι ι ℝ) (a b : ℝ)
    (hentry : ∀ i j, |A i j|≤a) (hrow : HasAbsRowBound A b) (ha : 0≤a) :
    (∑ i, ∑ j, (A i j)^2)≤(Fintype.card ι : ℝ)*a*b := by
  calc
    (∑ i, ∑ j, (A i j)^2) ≤ ∑ i, a*absRowSum A i := by
      apply Finset.sum_le_sum
      intro i _
      rw [absRowSum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg (A i j))
      rw [← pow_two, sq_abs] at h
      exact h
    _ ≤ ∑ _i : ι, a*b := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) ha
    _ = _ := by simp; ring

/-- A row bound alone controls the Frobenius sum, with the correct site-count factor. -/
theorem sum_sq_le_card_row_sq (A : Matrix ι ι ℝ) (a : ℝ)
    (hrow : HasAbsRowBound A a) (ha : 0≤a) :
    (∑ i, ∑ j, (A i j)^2)≤(Fintype.card ι : ℝ)*a^2 := by
  have he (i j : ι) : |A i j|≤a := (abs_entry_le_absRowSum A i j).trans (hrow i)
  simpa only [pow_two, mul_assoc] using sum_sq_le_entry_row A a a he hrow ha

/-- Removing a diagonal never increases an absolute row sum. -/
def offDiagonal (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j => if i=j then 0 else A i j

theorem absRowSum_offDiagonal_le (A : Matrix ι ι ℝ) (i : ι) :
    absRowSum (offDiagonal A) i≤absRowSum A i := by
  apply Finset.sum_le_sum
  intro j _
  by_cases h : i=j <;> simp [offDiagonal,h]

end BilayerDressed
