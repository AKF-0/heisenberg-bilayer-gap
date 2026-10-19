import Gap.Squaring
import Mathlib

/-!
# Purity squaring for summable countable probability distributions

The weights are indexed by natural numbers. Summability is explicit, rather
than relying on the default value of `tsum` for a divergent series. The proof
passes the finite fourth-moment inequality to partial-sum limits.
This does not construct the spatial-transfer spectral weights of a model.
-/
noncomputable section
namespace BilayerGap
open scoped BigOperators Topology
open Filter

/-- Countable version of the finite fourth-moment inequality. -/
theorem countable_moment_squaring_inequality (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (hs2 : Summable (fun i ↦ p i ^ 2))
    (hs4 : Summable (fun i ↦ p i ^ 4)) :
    2 * ((∑' i, p i ^ 2) ^ 2 - ∑' i, p i ^ 4) ≤
      ((∑' i, p i) ^ 2 - ∑' i, p i ^ 2) ^ 2 := by
  have hS := hs.hasSum.tendsto_sum_nat
  have hP := hs2.hasSum.tendsto_sum_nat
  have hQ := hs4.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto (((hP.pow 2).sub hQ).const_mul 2)
    (((hS.pow 2).sub hP).pow 2)
    (Filter.Eventually.of_forall (fun n ↦
      finite_moment_squaring_inequality (Finset.range n) p (fun i _ ↦ hp i)))

/-- A normalized nonnegative summable list has every entry at most one. -/
theorem probability_entry_le_one (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) (i : ℕ) : p i ≤ 1 := by
  simpa [hnorm] using hs.le_tsum i (fun j _ ↦ hp j)

/-- The squared probabilities are dominated by the probabilities themselves. -/
theorem probability_square_le (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) (i : ℕ) : p i ^ 2 ≤ p i := by
  have hi := probability_entry_le_one p hp hs hnorm i
  nlinarith [mul_nonneg (hp i) (sub_nonneg.mpr hi)]

/-- Squared and fourth-power probabilities are summable; these are conclusions,
not extra model assumptions in the final probability theorem. -/
theorem probability_power_summability (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) :
    Summable (fun i ↦ p i ^ 2) ∧ Summable (fun i ↦ p i ^ 4) := by
  have hsq := probability_square_le p hp hs hnorm
  have hs2 : Summable (fun i ↦ p i ^ 2) :=
    Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _) hsq hs
  refine ⟨hs2, Summable.of_nonneg_of_le (fun i ↦ by positivity) ?_ hs2⟩
  intro i
  have hi : p i ^ 2 ≤ 1 := (hsq i).trans (probability_entry_le_one p hp hs hnorm i)
  nlinarith [mul_nonneg (sq_nonneg (p i)) (sub_nonneg.mpr hi)]

/-- Countable collision purity. -/
def countablePurity (p : ℕ → ℝ) : ℝ := ∑' i, p i ^ 2

/-- Positive normalized total mass forces positive collision purity. -/
theorem countablePurity_pos (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) : 0 < countablePurity p := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
    by_contra! hn
    have hz : ∀ i, p i = 0 := fun i ↦ le_antisymm (hn i) (hp i)
    simp only [hz, tsum_zero] at hnorm
    norm_num at hnorm
  exact Summable.tsum_pos (probability_power_summability p hp hs hnorm).1
    (fun i ↦ sq_nonneg _) i (sq_pos_of_pos hi)

/-- Countable probability purity is at most one. -/
theorem countablePurity_le_one (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) : countablePurity p ≤ 1 := by
  have h := Summable.tsum_le_tsum (probability_square_le p hp hs hnorm)
    (probability_power_summability p hp hs hnorm).1 hs
  simpa [countablePurity, hnorm] using h

/-- Squared and renormalized countable weights form a genuine summable
probability distribution. -/
theorem countable_squared_weights_probability (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) :
    (∀ i, 0 ≤ p i ^ 2 / countablePurity p) ∧
    Summable (fun i ↦ p i ^ 2 / countablePurity p) ∧
    (∑' i, p i ^ 2 / countablePurity p) = 1 := by
  have hP := countablePurity_pos p hp hs hnorm
  refine ⟨fun i ↦ div_nonneg (sq_nonneg _) hP.le,
    (probability_power_summability p hp hs hnorm).1.div_const _, ?_⟩
  rw [tsum_div_const]
  change countablePurity p / countablePurity p = 1
  exact div_self hP.ne'

/-- The purity-defect squaring inequality holds for summable countable
probabilities, with no finite-support hypothesis. -/
theorem countable_purity_squaring (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (hnorm : ∑' i, p i = 1) :
    1 - countablePurity (fun i ↦ p i ^ 2 / countablePurity p) ≤
      (1 - countablePurity p) ^ 2 / (2 * countablePurity p ^ 2) := by
  have hP := countablePurity_pos p hp hs hnorm
  have hpowers := probability_power_summability p hp hs hnorm
  have hm := countable_moment_squaring_inequality p hp hs hpowers.1 hpowers.2
  have hm' : 2 * (countablePurity p ^ 2 - ∑' i, p i ^ 4) ≤
      (1 - countablePurity p) ^ 2 := by
    simpa [countablePurity, hnorm] using hm
  have hformula : countablePurity (fun i ↦ p i ^ 2 / countablePurity p) =
      (∑' i, p i ^ 4) / countablePurity p ^ 2 := by
    simp only [countablePurity, div_pow, ← pow_mul, tsum_div_const]
  rw [hformula]
  apply (le_div_iff₀ (by positivity : 0 < 2 * countablePurity p ^ 2)).2
  have hcancel : (1 - (∑' i, p i ^ 4) / countablePurity p ^ 2) *
      (2 * countablePurity p ^ 2) =
      2 * (countablePurity p ^ 2 - ∑' i, p i ^ 4) := by
    field_simp [ne_of_gt hP]
  rwa [hcancel]

#print axioms countable_moment_squaring_inequality
#print axioms probability_power_summability
#print axioms countablePurity_pos
#print axioms countable_squared_weights_probability
#print axioms countable_purity_squaring
end BilayerGap
