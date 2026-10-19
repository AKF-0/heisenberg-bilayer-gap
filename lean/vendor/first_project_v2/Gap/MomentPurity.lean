import Gap.CountableSquaring
import Gap.Moments

/-!
# Spatial moment ratios are actual countable purities

The spectrum is a natural-number indexed real list. A summable positive moment
provides normalized nonnegative weights; doubling that moment squares the
weights. This supplies the probability interpretation of the spatial ratios.
A model-specific transfer representation is still a separate obligation.
-/
noncomputable section
namespace BilayerGap

/-- Probability weight obtained from a positive absolute spectral moment. -/
def momentWeight (lambda : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ :=
  |lambda i| ^ n / absMoment lambda n

theorem momentWeight_nonneg (lambda : ℕ → ℝ) (n : ℕ)
    (hm : 0 < absMoment lambda n) (i : ℕ) : 0 ≤ momentWeight lambda n i :=
  div_nonneg (pow_nonneg (abs_nonneg _) _) hm.le

theorem momentWeight_summable (lambda : ℕ → ℝ) (n : ℕ)
    (hs : Summable (fun i ↦ |lambda i| ^ n)) :
    Summable (momentWeight lambda n) := hs.div_const _

theorem momentWeight_sum (lambda : ℕ → ℝ) (n : ℕ)
    (hm : 0 < absMoment lambda n) : ∑' i, momentWeight lambda n i = 1 := by
  simp only [momentWeight, tsum_div_const]
  change absMoment lambda n / absMoment lambda n = 1
  exact div_self hm.ne'

/-- The moment ratio has exactly the collision-purity interpretation, not an
assumed estimate. -/
theorem moment_purity_ratio (lambda : ℕ → ℝ) (n : ℕ) :
    countablePurity (momentWeight lambda n) =
      absMoment lambda (2*n) / absMoment lambda n ^ 2 := by
  simp only [countablePurity, momentWeight, div_pow, ← pow_mul, tsum_div_const]
  rw [Nat.mul_comm n 2]
  rfl

/-- A positive summable spectral moment also has a positive doubled moment. -/
theorem doubled_moment_pos (lambda : ℕ → ℝ) (n : ℕ)
    (hs : Summable (fun i ↦ |lambda i| ^ n)) (hm : 0 < absMoment lambda n) :
    0 < absMoment lambda (2*n) := by
  have hp := countablePurity_pos (momentWeight lambda n)
    (momentWeight_nonneg lambda n hm) (momentWeight_summable lambda n hs)
    (momentWeight_sum lambda n hm)
  rw [moment_purity_ratio] at hp
  exact (div_pos_iff_of_pos_right (sq_pos_of_pos hm)).mp hp

/-- The normalized weights at the doubled size are exactly the squared and
renormalized weights, including the denominator identity. -/
theorem momentWeight_double (lambda : ℕ → ℝ) (n : ℕ)
    (hs : Summable (fun i ↦ |lambda i| ^ n)) (hm : 0 < absMoment lambda n) (i : ℕ) :
    momentWeight lambda (2*n) i = momentWeight lambda n i ^ 2 /
      countablePurity (momentWeight lambda n) := by
  have hm2 := doubled_moment_pos lambda n hs hm
  rw [moment_purity_ratio]
  unfold momentWeight
  have hp : |lambda i| ^ (2*n) = (|lambda i| ^ n)^2 := by
    rw [← pow_mul, Nat.mul_comm n 2]
  rw [hp]
  field_simp [hm.ne', hm2.ne']

/-- Positivity and the purity upper bound follow from normalized weights. -/
theorem moment_ratio_bounds (lambda : ℕ → ℝ) (n : ℕ)
    (hs : Summable (fun i ↦ |lambda i| ^ n)) (hm : 0 < absMoment lambda n) :
    0 < absMoment lambda (2*n) / absMoment lambda n ^ 2 ∧
      absMoment lambda (2*n) / absMoment lambda n ^ 2 ≤ 1 := by
  rw [← moment_purity_ratio]
  exact ⟨countablePurity_pos (momentWeight lambda n)
      (momentWeight_nonneg lambda n hm) (momentWeight_summable lambda n hs)
      (momentWeight_sum lambda n hm),
    countablePurity_le_one (momentWeight lambda n)
      (momentWeight_nonneg lambda n hm) (momentWeight_summable lambda n hs)
      (momentWeight_sum lambda n hm)⟩

/-- Own-direction spatial purity squaring, proved from the supplied summable
spectrum rather than taken as a recurrence hypothesis. -/
theorem moment_ratio_squaring (lambda : ℕ → ℝ) (n : ℕ)
    (hs : Summable (fun i ↦ |lambda i| ^ n)) (hm : 0 < absMoment lambda n) :
    1 - absMoment lambda (2*(2*n)) / absMoment lambda (2*n) ^ 2 ≤
      (1 - absMoment lambda (2*n) / absMoment lambda n ^ 2) ^ 2 /
        (2 * (absMoment lambda (2*n) / absMoment lambda n ^ 2) ^ 2) := by
  have hp := countable_purity_squaring (momentWeight lambda n)
    (momentWeight_nonneg lambda n hm) (momentWeight_summable lambda n hs)
    (momentWeight_sum lambda n hm)
  have heq : momentWeight lambda (2*n) = fun i ↦ momentWeight lambda n i ^ 2 /
      countablePurity (momentWeight lambda n) := by
    funext i
    exact momentWeight_double lambda n hs hm i
  rw [← heq, moment_purity_ratio, moment_purity_ratio] at hp
  exact hp

#print axioms moment_purity_ratio
#print axioms momentWeight_double
#print axioms moment_ratio_bounds
#print axioms moment_ratio_squaring
end BilayerGap
