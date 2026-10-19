import Gap.ExponentialSeeds

/-!
# Explicit sixteen-level cluster partition bounds

This file uses the six displayed energies and their multiplicities `1,1,3,3,3,5`.
It proves bounds for their actual exponential sum. Identification of that sum
with a matrix trace, and matching/log-trace-convexity bounds for a large torus,
are separate obligations; neither is assumed or asserted here.
-/

noncomputable section
namespace BilayerGap
namespace ClusterSeed

/-- Lower energy of the two-dimensional singlet block. -/
def lowerEnergy (t : ℝ) : ℝ := 1 - t / 2 - Real.sqrt (1 - t + t ^ 2)

def upperEnergy (t : ℝ) : ℝ := 1 - t / 2 + Real.sqrt (1 - t + t ^ 2)

/-- The explicit exponential sum with all sixteen multiplicities retained. -/
def partition (t b : ℝ) : ℝ :=
  Real.exp (-b * lowerEnergy t) + Real.exp (-b * upperEnergy t) +
    3 * Real.exp (-b * (1 - t / 2)) + 3 * Real.exp (-b * (1 + t / 2)) +
    3 * Real.exp (-b * (2 - t / 2)) + 5 * Real.exp (-b * (2 + t / 2))

theorem discriminant_pos (t : ℝ) : 0 < 1 - t + t ^ 2 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- The radical energy has nonpositive lower branch and the upper branch is
in the high excited band. -/
theorem radical_energy_bands {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ -lowerEnergy t ∧ 2 - t ≤ upperEnergy t := by
  have hq0 := Real.sqrt_nonneg (1 - t + t ^ 2)
  have hqsq := Real.sq_sqrt (discriminant_pos t).le
  have hqa : 1 - t / 2 ≤ Real.sqrt (1 - t + t ^ 2) := by nlinarith [sq_nonneg t]
  unfold lowerEnergy upperEnergy
  constructor <;> linarith

/-- The rational ground-energy estimate, derived directly from the radical. -/
theorem ground_rational_bound {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -lowerEnergy t ≤ 3 * t ^ 2 / (8 - 4 * t) := by
  have hqsq := Real.sq_sqrt (discriminant_pos t).le
  have hden : 0 < 8 - 4 * t := by linarith
  apply (le_div_iff₀ hden).2
  unfold lowerEnergy
  nlinarith [sq_nonneg (Real.sqrt (1 - t + t ^ 2) - (1 - t / 2))]

theorem narrow_ground_bound {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 250) :
    -lowerEnergy t ≤ 3 / 499000 := by
  have hsq := pow_le_pow_left₀ ht0 ht 2
  calc
    -lowerEnergy t ≤ 3 * t ^ 2 / (8 - 4 * t) := ground_rational_bound ht0 (by linarith)
    _ ≤ 3 * (1 / 250 : ℝ) ^ 2 / (8 - 4 * (1 / 250 : ℝ)) :=
      div_le_div₀ (by norm_num) (by nlinarith) (by norm_num) (by linarith)
    _ = 3 / 499000 := by norm_num

theorem wide_ground_bound {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    -lowerEnergy t ≤ t ^ 2 / 2 := by
  have hden : 0 < 8 - 4 * t := by linarith
  have hcoeff : 3 / (8 - 4 * t) ≤ (1 / 2 : ℝ) := (div_le_iff₀ hden).2 (by linarith)
  calc
    -lowerEnergy t ≤ 3 * t ^ 2 / (8 - 4 * t) := ground_rational_bound ht0 (by linarith)
    _ = t ^ 2 * (3 / (8 - 4 * t)) := by ring
    _ ≤ t ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (sq_nonneg t)
    _ = t ^ 2 / 2 := by ring

/-- Group the excited contributions into six low and nine high levels. -/
theorem partition_le_envelope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    partition t 14 ≤ Real.exp (-14 * lowerEnergy t) +
      6 * Real.exp (-14 * (1 - t / 2)) + 9 * Real.exp (-14 * (2 - t)) := by
  have hu := (radical_energy_bands ht0 ht1).2
  have hplus : Real.exp (-14 * upperEnergy t) ≤ Real.exp (-14 * (2 - t)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlo : Real.exp (-14 * (1 + t / 2)) ≤ Real.exp (-14 * (1 - t / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hhi1 : Real.exp (-14 * (2 - t / 2)) ≤ Real.exp (-14 * (2 - t)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hhi2 : Real.exp (-14 * (2 + t / 2)) ≤ Real.exp (-14 * (2 - t)) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold partition
  linarith

theorem narrow_low_bound {t : ℝ} (ht : t ≤ 1 / 250) :
    Real.exp (-14 * (1 - t / 2)) ≤ (1 / 1000000 : ℝ) * (250 / 243) := by
  have hc : Real.exp (14 * t / 2) ≤ (250 / 243 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : 14 * t / 2 ≤ 14 * (1 / 250 : ℝ) / 2)).trans
      SeedAnalytic.narrow_low_correction_bound
  calc
    Real.exp (-14 * (1 - t / 2)) = Real.exp (-14) * Real.exp (14 * t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (1 / 1000000 : ℝ) * (250 / 243) :=
      mul_le_mul SeedAnalytic.exp_neg_fourteen_lt.le hc (Real.exp_pos _).le (by norm_num)

theorem narrow_high_bound {t : ℝ} (ht : t ≤ 1 / 250) :
    Real.exp (-14 * (2 - t)) ≤ (1 / 1000000000000 : ℝ) * (125 / 118) := by
  have hc : Real.exp (14 * t) ≤ (125 / 118 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : 14 * t ≤ 14 * (1 / 250 : ℝ))).trans
      SeedAnalytic.narrow_high_correction_bound
  calc
    Real.exp (-14 * (2 - t)) = Real.exp (-28) * Real.exp (14 * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (1 / 1000000000000 : ℝ) * (125 / 118) :=
      mul_le_mul SeedAnalytic.exp_neg_twenty_eight_lt.le hc (Real.exp_pos _).le (by norm_num)

/-- The narrow seed's actual cluster exponential sum is below `1.0001`. -/
theorem narrow_partition_bound {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 250) :
    partition t 14 < (10001 / 10000 : ℝ) := by
  have hg : Real.exp (-14 * lowerEnergy t) ≤ (499000 / 498958 : ℝ) :=
    (Real.exp_le_exp.mpr (by nlinarith [narrow_ground_bound ht0 ht])).trans
      SeedAnalytic.narrow_ground_exponential_bound
  have hlo := narrow_low_bound ht
  have hhi := narrow_high_bound ht
  have hrat : (SeedCertificate.narrowZUpper : ℝ) < (10001 / 10000 : ℝ) := by
    norm_num [SeedCertificate.narrowZUpper]
  apply lt_of_le_of_lt _ hrat
  calc
    partition t 14 ≤ Real.exp (-14 * lowerEnergy t) +
        6 * Real.exp (-14 * (1 - t / 2)) + 9 * Real.exp (-14 * (2 - t)) :=
      partition_le_envelope ht0 (by linarith)
    _ ≤ (SeedCertificate.narrowZUpper : ℝ) := by
      unfold SeedCertificate.narrowZUpper
      push_cast
      nlinarith

/-- The wider endpoint's actual exponential sum is controlled by the exact eta. -/
theorem wide_partition_bound {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    partition t 14 ≤ 1 + (SeedCertificate.wideEta : ℝ) := by
  have hsq := pow_le_pow_left₀ ht0 ht 2
  have hg : Real.exp (-14 * lowerEnergy t) ≤
      1 / (1 - 112 * (1 / 400 : ℝ) ^ 2) :=
    (Real.exp_le_exp.mpr (by nlinarith [wide_ground_bound ht0 ht])).trans
      SeedAnalytic.wide_ground_exponential_bound
  have hlo : Real.exp (-14 * (1 - t / 2)) ≤ (1 / 1000000 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -14 * (1 - t / 2) ≤ -(1393 / 100 : ℝ))).trans
      SeedAnalytic.exp_neg_wide_threshold_lt.le
  have hhi : Real.exp (-14 * (2 - t)) ≤ (1 / 1000000000000 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -14 * (2 - t) ≤ -(1393 / 50 : ℝ))).trans
      SeedAnalytic.exp_neg_wide_double_lt.le
  calc
    partition t 14 ≤ Real.exp (-14 * lowerEnergy t) +
        6 * Real.exp (-14 * (1 - t / 2)) + 9 * Real.exp (-14 * (2 - t)) :=
      partition_le_envelope ht0 (by linarith)
    _ ≤ 1 + (SeedCertificate.wideEta : ℝ) := by
      unfold SeedCertificate.wideEta
      push_cast
      norm_num at hg hlo hhi ⊢
      nlinarith

#print axioms ground_rational_bound
#print axioms narrow_partition_bound
#print axioms wide_partition_bound

end ClusterSeed
end BilayerGap
