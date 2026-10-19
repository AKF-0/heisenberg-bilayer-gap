import Mathlib

/-!
# Finite spectral-measure Temple inequality

This proves the spectral inequality from explicit finite energies and
nonnegative normalized weights. It does not assume the conclusion as a gap
hypothesis. The concrete Hermitian-operator and bilayer instantiations are
separate obligations and are not asserted by this module.
-/

noncomputable section
open scoped BigOperators

namespace BilayerDressed

variable {ι : Type*} [Fintype ι]

def spectralMean (p energy : ι → ℝ) : ℝ := ∑ i, p i * energy i

def spectralVariance (p energy : ι → ℝ) : ℝ :=
  ∑ i, p i * (energy i - spectralMean p energy) ^ 2

theorem spectralVariance_nonneg (p energy : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) : 0 ≤ spectralVariance p energy := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)

theorem ground_le_spectralMean (p energy : ι → ℝ) (ground : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hground : ∀ i, ground ≤ energy i) : ground ≤ spectralMean p energy := by
  calc
    ground = ∑ i, p i * ground := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ spectralMean p energy := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hground i) (hp i)

theorem temple_variance_identity (p energy : ι → ℝ) (ground threshold : ℝ)
    (hsum : ∑ i, p i = 1) :
    spectralVariance p energy -
        (spectralMean p energy - ground) * (threshold - spectralMean p energy) =
      ∑ i, p i * (energy i - ground) * (energy i - threshold) := by
  let μ := spectralMean p energy
  have hfirst : (∑ i, p i * energy i) = μ := rfl
  have hpoint (i : ι) :
      p i * (energy i - μ)^2 -
          p i * (μ-ground) * (threshold-μ) =
        p i * (energy i-ground) * (energy i-threshold) +
          (2*μ-ground-threshold) * (p i * (μ-energy i)) := by ring
  have hzero : ∑ i, p i * (μ-energy i) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, hfirst, sub_self]
  have hsumPoint := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsumPoint
  simp_rw [← Finset.sum_mul] at hsumPoint
  rw [hsum, one_mul, ← Finset.mul_sum, hzero, mul_zero, add_zero] at hsumPoint
  exact hsumPoint

theorem temple_variance_lower (p energy : ι → ℝ) (ground threshold : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hspectrum : ∀ i, energy i = ground ∨ threshold ≤ energy i)
    (hground : ∀ i, ground ≤ energy i) :
    (spectralMean p energy - ground) * (threshold - spectralMean p energy) ≤
      spectralVariance p energy := by
  have hnonneg : 0 ≤ ∑ i, p i * (energy i-ground) * (energy i-threshold) := by
    apply Finset.sum_nonneg
    intro i _
    rcases hspectrum i with h | h
    · simp [h]
    · exact mul_nonneg (mul_nonneg (hp i) (sub_nonneg.mpr (hground i)))
        (sub_nonneg.mpr h)
  rw [← temple_variance_identity p energy ground threshold hsum] at hnonneg
  linarith

/-- Temple's lower energy bound with its actual mean and variance. -/
theorem finite_temple (p energy : ι → ℝ) (ground threshold : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hspectrum : ∀ i, energy i = ground ∨ threshold ≤ energy i)
    (hground : ∀ i, ground ≤ energy i)
    (hmean : spectralMean p energy < threshold) :
    spectralMean p energy -
        spectralVariance p energy / (threshold-spectralMean p energy) ≤ ground := by
  have hd : 0 < threshold-spectralMean p energy := sub_pos.mpr hmean
  have h := temple_variance_lower p energy ground threshold hp hsum hspectrum hground
  have hdiv : spectralMean p energy-ground ≤
      spectralVariance p energy / (threshold-spectralMean p energy) :=
    (le_div_iff₀ hd).mpr h
  linarith

end BilayerDressed
