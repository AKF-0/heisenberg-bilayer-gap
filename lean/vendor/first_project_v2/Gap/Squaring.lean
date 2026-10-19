import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite probability purity under squaring

This file proves a genuine finite-distribution statement, not a statement about
an assumed recurrence. It does not supply the countable spatial-transfer case.
-/

noncomputable section

namespace BilayerGap

open Finset

/-- A nonnegative finite list satisfies the fourth-moment inequality needed for
purity squaring. No normalization or upper bounds on the entries are assumed. -/
theorem finite_moment_squaring_inequality {ι : Type*} (s : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    2 * ((∑ i ∈ s, p i ^ 2) ^ 2 - ∑ i ∈ s, p i ^ 4) ≤
      ((∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2) ^ 2 := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert a s ha ih =>
    intro hp
    have hpa : 0 ≤ p a := hp a (by simp)
    have hps : ∀ i ∈ s, 0 ≤ p i := fun i hi ↦ hp i (by simp [hi])
    have hs : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hps
    have hsq : (∑ i ∈ s, p i ^ 2) ≤ (∑ i ∈ s, p i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg hps
    have hdiff : 0 ≤ (∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2 := sub_nonneg.mpr hsq
    have hprod : 0 ≤ 4 * ((∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2) *
        p a * ((∑ i ∈ s, p i) + p a) := by positivity
    have hind := ih hps
    simp only [Finset.sum_insert ha]
    nlinarith [hprod]

/-- The usual purity of a finite probability distribution. -/
def finitePurity {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, p i ^ 2

/-- Normalization forces strictly positive purity. -/
theorem finitePurity_pos {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 < finitePurity p := by
  classical
  have hsum : 0 < ∑ i, p i := by rw [hs]; norm_num
  obtain ⟨i, hi, hpi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hp i)).mp hsum
  exact Finset.sum_pos' (fun i _ ↦ sq_nonneg (p i))
    ⟨i, hi, sq_pos_of_pos hpi⟩

/-- Probability purity is at most one. -/
theorem finitePurity_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    finitePurity p ≤ 1 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := p) (fun i _ ↦ hp i)
  simpa [finitePurity, hs] using h

/-- The squared weights are nonnegative and normalized, so the next purity
really belongs to another probability distribution. -/
theorem squared_weights_probability {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∀ i, 0 ≤ p i ^ 2 / finitePurity p) ∧
      (∑ i, p i ^ 2 / finitePurity p) = 1 := by
  have hP := finitePurity_pos p hp hs
  constructor
  · intro i
    exact div_nonneg (sq_nonneg _) hP.le
  · rw [← Finset.sum_div]
    change finitePurity p / finitePurity p = 1
    exact div_self hP.ne'

/-- Squaring and renormalizing a finite probability distribution gives the
nonlinear purity-defect bound used in the analytic manuscript. -/
theorem finite_purity_squaring {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    1 - finitePurity (fun i ↦ p i ^ 2 / finitePurity p) ≤
      (1 - finitePurity p) ^ 2 / (2 * finitePurity p ^ 2) := by
  have hP : 0 < finitePurity p := finitePurity_pos p hp hs
  have hP2 : 0 < finitePurity p ^ 2 := sq_pos_of_pos hP
  have hm := finite_moment_squaring_inequality Finset.univ p (fun i _ ↦ hp i)
  have hm' : 2 * (finitePurity p ^ 2 - ∑ i, p i ^ 4) ≤
      (1 - finitePurity p) ^ 2 := by
    simpa [finitePurity, hs] using hm
  have hformula : finitePurity (fun i ↦ p i ^ 2 / finitePurity p) =
      (∑ i, p i ^ 4) / finitePurity p ^ 2 := by
    simp only [finitePurity, div_pow, ← pow_mul, ← Finset.sum_div]

  rw [hformula]
  apply (le_div_iff₀ (by positivity : 0 < 2 * finitePurity p ^ 2)).2
  have hcancel : (1 - (∑ i, p i ^ 4) / finitePurity p ^ 2) *
      (2 * finitePurity p ^ 2) =
      2 * (finitePurity p ^ 2 - ∑ i, p i ^ 4) := by
    field_simp [ne_of_gt hP]
  rwa [hcancel]

#print axioms finite_moment_squaring_inequality
#print axioms finitePurity_pos
#print axioms finitePurity_le_one
#print axioms squared_weights_probability
#print axioms finite_purity_squaring

end BilayerGap
