import Mathlib

/-!
# Exact rational certificates for the analytic bilayer seeds

This file verifies rational arithmetic only. In particular, `taylorSum` is a
finite rational polynomial, not an assumption about the real exponential.
Connecting its value to `Real.exp`, deriving the cluster spectrum, applying
partition-function convexity, and transporting the inequalities through the
purity recursion are separate mathematical obligations.

All decimal bounds below are represented as exact fractions. The three-component
updates are sequential: the new first coordinate is used in the second update,
and both new coordinates are used in the third update. Each rounding certificate
places the exact update strictly between two consecutive grid points of size
`10⁻¹⁰`, so the displayed upper point is exactly the upward rounding.

The proofs use kernel-checked `norm_num`, not `native_decide` or numerical oracles.
-/

namespace BilayerGap
namespace SeedCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Taylor polynomial through degree `n`, evaluated exactly over the rationals. -/
def taylorSum (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℚ)

/-- The degree-18 Taylor polynomial at 14 exceeds one million. -/
theorem narrow_taylor_gt : (1000000 : ℚ) < taylorSum 14 18 := by
  norm_num [taylorSum, Finset.sum_range_succ, Nat.factorial]

/-- The degree-29 Taylor polynomial at 13.93 exceeds one million. -/
theorem wide_taylor_gt : (1000000 : ℚ) < taylorSum (1393 / 100) 29 := by
  norm_num [taylorSum, Finset.sum_range_succ, Nat.factorial]

/-- The rational expression that appears in the common-defect bootstrap at .01. -/
def commonG7 : ℚ :=
  ((∑ k ∈ Finset.range 7, ((1 - (1 / 100 : ℚ)) ^ (k + 1))⁻¹) ^ 2) / 2

/-- Exact common-bootstrap constant certificate, `G₇(.01) < 27`. -/
theorem common_G7_lt : commonG7 < 27 := by
  norm_num [commonG7, Finset.sum_range_succ]

/-- The other scalar hypotheses of the common-defect bootstrap. -/
theorem common_bootstrap_constants :
    (0 : ℚ) < 1 / 100 ∧
    (27 : ℚ) * (1 / 100) < 1 ∧
    (7 : ℚ) * (1 / 100) < 1 / 2 ∧
    (7 : ℚ) < 27 * (1 - 7 * (1 / 100)) := by
  norm_num

/-! ## The narrow coupling interval, `0 ≤ g ≤ 1/1000` -/

/-- Exact endpoint value of the rational cluster ground-energy bound. -/
theorem narrow_ground_endpoint :
    (3 : ℚ) * (1 / 250) ^ 2 / (8 - 4 * (1 / 250)) = 3 / 499000 := by
  norm_num

/-- All three geometric-series arguments are in `[0,1)`. -/
theorem narrow_geometric_arguments :
    (0 : ℚ) ≤ 14 * (3 / 499000) ∧ 14 * (3 / 499000 : ℚ) < 1 ∧
    (0 : ℚ) ≤ 14 * (1 / 250) / 2 ∧ 14 * (1 / 250 : ℚ) / 2 < 1 ∧
    (0 : ℚ) ≤ 14 * (1 / 250) ∧ 14 * (1 / 250 : ℚ) < 1 := by
  norm_num

/-- Exact rational upper bound, conditional on the separate spectral/exp lemmas. -/
def narrowZUpper : ℚ :=
  499000 / 498958 + 6 / 1000000 * (250 / 243) +
    9 / 1000000000000 * (125 / 118)

/-- The geometric-series expression is exactly the stated upper bound. -/
theorem narrow_z_expression :
    (1 : ℚ) / (1 - 14 * (3 / 499000)) +
      (6 / 1000000) / (1 - 14 * (1 / 250) / 2) +
      (9 / 1000000000000) / (1 - 14 * (1 / 250)) = narrowZUpper := by
  norm_num [narrowZUpper]

/-- The exact pair partition-function bound is below `1.0001`. -/
theorem narrow_z_lt : narrowZUpper < 10001 / 10000 := by
  norm_num [narrowZUpper]

/-- Exact finite-area Bernoulli and `.99` certificates for all three seed areas. -/
theorem narrow_area_certificate (A : ℕ) (hA : A = 16 ∨ A = 32 ∨ A = 64) :
    (1 - (A : ℚ) / 10000) ≤ (10000 / 10001 : ℚ) ^ A ∧
    (621 / 625 : ℚ) ≤ 1 - (A : ℚ) / 10000 ∧
    (99 / 100 : ℚ) < 621 / 625 := by
  rcases hA with rfl | rfl | rfl <;> norm_num

/-- The worst defect is exactly `.0064`. -/
theorem narrow_worst_defect :
    (64 / 10000 : ℚ) = 4 / 625 ∧ (1 - 64 / 10000 : ℚ) = 621 / 625 := by
  norm_num

/-! ## The wider coupling interval, `0 ≤ g ≤ 1/400` -/

/-- Exact endpoint relations for the wider interval. -/
theorem wide_endpoint_constants :
    (4 : ℚ) * (1 / 400) = 1 / 100 ∧
    (14 : ℚ) * (1 - (1 / 100) / 2) = 1393 / 100 ∧
    (3 : ℚ) / (8 - 4 * (1 / 100)) ≤ 1 / 2 ∧
    (0 : ℚ) < 112 * (1 / 400) ^ 2 ∧
    112 * (1 / 400 : ℚ) ^ 2 < 1 := by
  norm_num

/-- The exact pair defect used for the enlarged interval. -/
def wideEta : ℚ :=
  112 * (1 / 400) ^ 2 / (1 - 112 * (1 / 400) ^ 2) +
    6 / 1000000 + 9 / 1000000000000

/-- Useful simplified form of the rational geometric term. -/
theorem wide_eta_expression :
    wideEta = (7 / 9993 : ℚ) + 6 / 1000000 + 9 / 1000000000000 := by
  norm_num [wideEta]

def a0 : ℚ := 16 * wideEta
def b0 : ℚ := 32 * wideEta
def c0 : ℚ := 64 * wideEta

/-- The defect map `f(u) = u² / (2(1-u)²)` evaluated at the staircase product. -/
def unequalUpdate (a b c : ℚ) : ℚ :=
  let u := 1 - (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c)
  u ^ 2 / (2 * (1 - u) ^ 2)

/-- One unit of the exact upward-rounding grid. -/
def grid : ℚ := 1 / 10000000000

def a1 : ℚ := 108596913 / 10000000000
def b1 : ℚ := 231602432 / 10000000000
def c1 : ℚ := 335506287 / 10000000000

def a2 : ℚ := 88142477 / 10000000000
def b2 : ℚ := 173532832 / 10000000000
def c2 : ℚ := 175486299 / 10000000000

def a3 : ℚ := 42438718 / 10000000000
def b3 : ℚ := 67193773 / 10000000000
def c3 : ℚ := 40390104 / 10000000000

/-- First warm-up stage, first component, with exact upward rounding. -/
theorem warmup1_a :
    a1 - grid < unequalUpdate a0 b0 c0 ∧ unequalUpdate a0 b0 c0 < a1 := by
  norm_num [unequalUpdate, a0, b0, c0, wideEta, a1, grid]

/-- First stage, second component: uses the newly rounded first component. -/
theorem warmup1_b :
    b1 - grid < unequalUpdate b0 c0 a1 ∧ unequalUpdate b0 c0 a1 < b1 := by
  norm_num [unequalUpdate, b0, c0, wideEta, a1, b1, grid]

/-- First stage, third component: uses both newly rounded components. -/
theorem warmup1_c :
    c1 - grid < unequalUpdate c0 a1 b1 ∧ unequalUpdate c0 a1 b1 < c1 := by
  norm_num [unequalUpdate, c0, wideEta, a1, b1, c1, grid]

/-- Second warm-up stage, first component. -/
theorem warmup2_a :
    a2 - grid < unequalUpdate a1 b1 c1 ∧ unequalUpdate a1 b1 c1 < a2 := by
  norm_num [unequalUpdate, a1, b1, c1, a2, grid]

/-- Second warm-up stage, second component. -/
theorem warmup2_b :
    b2 - grid < unequalUpdate b1 c1 a2 ∧ unequalUpdate b1 c1 a2 < b2 := by
  norm_num [unequalUpdate, b1, c1, a2, b2, grid]

/-- Second warm-up stage, third component. -/
theorem warmup2_c :
    c2 - grid < unequalUpdate c1 a2 b2 ∧ unequalUpdate c1 a2 b2 < c2 := by
  norm_num [unequalUpdate, c1, a2, b2, c2, grid]

/-- Third warm-up stage, first component. -/
theorem warmup3_a :
    a3 - grid < unequalUpdate a2 b2 c2 ∧ unequalUpdate a2 b2 c2 < a3 := by
  norm_num [unequalUpdate, a2, b2, c2, a3, grid]

/-- Third warm-up stage, second component. -/
theorem warmup3_b :
    b3 - grid < unequalUpdate b2 c2 a3 ∧ unequalUpdate b2 c2 a3 < b3 := by
  norm_num [unequalUpdate, b2, c2, a3, b3, grid]

/-- Third warm-up stage, third component. -/
theorem warmup3_c :
    c3 - grid < unequalUpdate c2 a3 b3 ∧ unequalUpdate c2 a3 b3 < c3 := by
  norm_num [unequalUpdate, c2, a3, b3, c3, grid]

/-- Every initial defect is positive and strictly below `.05`. -/
theorem initial_bounds :
    0 < a0 ∧ a0 < 1 / 20 ∧ 0 < b0 ∧ b0 < 1 / 20 ∧ 0 < c0 ∧ c0 < 1 / 20 := by
  norm_num [a0, b0, c0, wideEta]

/-- All first-stage rounded defects stay strictly below `.05`. -/
theorem warmup1_bounds :
    0 < a1 ∧ a1 < 1 / 20 ∧ 0 < b1 ∧ b1 < 1 / 20 ∧ 0 < c1 ∧ c1 < 1 / 20 := by
  norm_num [a1, b1, c1]

/-- All second-stage rounded defects stay strictly below `.05`. -/
theorem warmup2_bounds :
    0 < a2 ∧ a2 < 1 / 20 ∧ 0 < b2 ∧ b2 < 1 / 20 ∧ 0 < c2 ∧ c2 < 1 / 20 := by
  norm_num [a2, b2, c2]

/-- All third-stage rounded defects are strictly below the desired `.01` seed. -/
theorem warmup3_bounds :
    0 < a3 ∧ a3 < 1 / 100 ∧ 0 < b3 ∧ b3 < 1 / 100 ∧ 0 < c3 ∧ c3 < 1 / 100 := by
  norm_num [a3, b3, c3]

/-- Scale bookkeeping after the three warm-up stages. -/
theorem warmup_scales :
    (4 : ℕ) * 2 ^ 3 = 32 ∧ (14 : ℕ) * 2 ^ 3 = 112 ∧
    (14 : ℕ) * 2 ^ 2 = 56 := by
  norm_num

/-! ## Rational comparison for the finitely many early interpolation scales -/

/-- The early-stage physical-purity lower bound. -/
def earlyPurity : ℚ := (19 / 20) ^ 7

/-- Early interpolation is above one half and has positive denominator. -/
theorem early_purity_bounds : (1 / 2 : ℚ) < earlyPurity ∧ earlyPurity < 1 := by
  norm_num [earlyPurity]

/-- The exact odds comparison used before applying monotonicity of real log. -/
theorem early_gap_comparison :
    (100 / 27 : ℚ) < (earlyPurity / (1 - earlyPurity)) ^ 2 := by
  norm_num [earlyPurity]

/-- The target logarithm has argument strictly above one. -/
theorem target_log_argument_gt_one : (1 : ℚ) < 100 / 27 := by
  norm_num

end SeedCertificate
end BilayerGap
