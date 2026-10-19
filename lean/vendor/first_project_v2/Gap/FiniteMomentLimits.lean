import Gap.SpectralFamily
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
# Spatial inequalities from limits of finite real spectra

No compact-operator spectral theorem is needed in this route. At each approximation
index, a transverse width has one finite real spectrum, independent of the varied
longitudinal length. The dimension may vary arbitrarily with approximation index.
Only convergence of the moments to the actual partition function is assumed.
All moment inequalities, purity bounds, and squaring inequalities are consequences.
The approximants need not have positive partition functions: all limits are passed
in polynomial form, and only the actual Gibbs partition function supplies positivity.
-/

noncomputable section
namespace BilayerGap
open Filter
open scoped Topology

/-- An actual finite list's absolute moment, including lists of dimension zero. -/
def finiteAbsMoment {d : ℕ} (lambda : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ i, |lambda i| ^ n

theorem finiteAbsMoment_eq_absMoment {d : ℕ} (lambda : Fin d → ℝ) (n : ℕ) :
    finiteAbsMoment lambda n = absMoment lambda n := by
  simp [finiteAbsMoment, absMoment, tsum_fintype]

theorem finiteAbsMoment_nonneg {d : ℕ} (lambda : Fin d → ℝ) (n : ℕ) :
    0 ≤ finiteAbsMoment lambda n :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (lambda i)) n)

theorem finiteAbsMoment_double_le {d : ℕ} (lambda : Fin d → ℝ) (n : ℕ) :
    finiteAbsMoment lambda (2*n) ≤ finiteAbsMoment lambda n ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => |lambda i| ^ n)
    (fun i _ => pow_nonneg (abs_nonneg _) n)
  simpa only [finiteAbsMoment, ← pow_mul, Nat.mul_comm n 2] using h

/-- The unnormalized polynomial inequality remains valid even at a zero moment. -/
theorem finiteAbsMoment_squaring {d : ℕ} (lambda : Fin d → ℝ) (n : ℕ) :
    2 * (finiteAbsMoment lambda (2*n) ^ 2 - finiteAbsMoment lambda (2*(2*n))) ≤
      (finiteAbsMoment lambda n ^ 2 - finiteAbsMoment lambda (2*n)) ^ 2 := by
  have h := finite_moment_squaring_inequality Finset.univ (fun i => |lambda i| ^ n)
    (fun i _ => pow_nonneg (abs_nonneg _) n)
  have h2 : n*2 = 2*n := by omega
  have h4 : n*4 = 2*(2*n) := by omega
  simpa only [finiteAbsMoment, ← pow_mul, h2, h4] using h

/-- A single sequence of finite spectra represents all valid moments in the limit. -/
structure FiniteMomentLimit (Z : ℕ → ℝ) where
  dim : ℕ → ℕ
  spectrum : ∀ k, Fin (dim k) → ℝ
  moment_limit : ∀ n, ValidSize n →
    Tendsto (fun k => finiteAbsMoment (spectrum k) n) atTop (𝓝 (Z n))

theorem FiniteMomentLimit.nonneg {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n : ℕ} (hn : ValidSize n) : 0 ≤ Z n :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds (D.moment_limit n hn)
    (fun k => finiteAbsMoment_nonneg (D.spectrum k) n)

theorem FiniteMomentLimit.upper {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n L : ℕ} (hn : ValidSize n) (hL : ValidSize L) (hnL : n ≤ L) :
    Z L ≤ (Z n) ^ ((L : ℝ) / n) := by
  apply le_of_tendsto_of_tendsto' (D.moment_limit L hL)
    ((D.moment_limit n hn).rpow_const (Or.inr (by positivity)))
  intro k
  simpa only [finiteAbsMoment_eq_absMoment] using
    (absMoment_upper (lambda := D.spectrum k) hn.pos hnL ((hasSum_fintype _).summable)).2

theorem FiniteMomentLimit.lower {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {L N : ℕ} (hL : ValidSize L) (hN : ValidSize N) (hLN : L ≤ N) :
    (Z N) ^ ((L : ℝ) / N) ≤ Z L := by
  apply le_of_tendsto_of_tendsto'
    ((D.moment_limit N hN).rpow_const (Or.inr (by positivity))) (D.moment_limit L hL)
  intro k
  simpa only [finiteAbsMoment_eq_absMoment] using
    (absMoment_lower (lambda := D.spectrum k) hL.pos hLN ((hasSum_fintype _).summable))

theorem FiniteMomentLimit.double_le {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n : ℕ} (hn : ValidSize n) : Z (2*n) ≤ Z n ^ 2 :=
  le_of_tendsto_of_tendsto' (D.moment_limit (2*n) hn.double)
    ((D.moment_limit n hn).pow 2) (fun k => finiteAbsMoment_double_le (D.spectrum k) n)

/-- The exact unnormalized squaring inequality passes through arbitrary changing
finite dimensions by continuity of its scalar polynomial. -/
theorem FiniteMomentLimit.squaring_polynomial {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n : ℕ} (hn : ValidSize n) :
    2 * (Z (2*n) ^ 2 - Z (2*(2*n))) ≤ (Z n ^ 2 - Z (2*n)) ^ 2 := by
  apply le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul (((D.moment_limit (2*n) hn.double).pow 2).sub
      (D.moment_limit (2*(2*n)) hn.double.double)))
    ((((D.moment_limit n hn).pow 2).sub (D.moment_limit (2*n) hn.double)).pow 2)
  intro k
  exact finiteAbsMoment_squaring (D.spectrum k) n

theorem FiniteMomentLimit.ratio_le_one {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n : ℕ} (hn : ValidSize n) (hpos : 0 < Z n) :
    Z (2*n) / Z n ^ 2 ≤ 1 := by
  exact (div_le_one (sq_pos_of_pos hpos)).2 (D.double_le hn)

/-- Denominators are only required positive in the limiting partition function. -/
theorem FiniteMomentLimit.ratio_squaring {Z : ℕ → ℝ} (D : FiniteMomentLimit Z)
    {n : ℕ} (hn : ValidSize n) (hpos : 0 < Z n) (hpos2 : 0 < Z (2*n)) :
    1 - Z (2*(2*n)) / Z (2*n) ^ 2 ≤
      (1 - Z (2*n) / Z n ^ 2) ^ 2 / (2 * (Z (2*n) / Z n ^ 2) ^ 2) := by
  have hid : (1 - Z (2*n) / Z n ^ 2) ^ 2 / (2 * (Z (2*n) / Z n ^ 2) ^ 2) =
      (Z n ^ 2 - Z (2*n)) ^ 2 / (2 * Z (2*n) ^ 2) := by
    field_simp
  rw [hid]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Z (2*n) ^ 2)).2
  have hc : (1 - Z (2*(2*n)) / Z (2*n)^2) * (2 * Z (2*n)^2) =
      2 * (Z (2*n)^2 - Z (2*(2*n))) := by
    field_simp
  rw [hc]
  exact D.squaring_polynomial hn

/-- The x and y sequences are distinct; each depends on the fixed transverse
width and approximation index, not on the exponent/varied longitudinal size. -/
structure FiniteSpatialMomentLimits (Z : ℕ → ℕ → ℝ) where
  x : ∀ M, ValidSize M → FiniteMomentLimit (fun L => Z L M)
  y : ∀ L, ValidSize L → FiniteMomentLimit (fun M => Z L M)

theorem FiniteSpatialMomentLimits.nonneg {Z : ℕ → ℕ → ℝ}
    (D : FiniteSpatialMomentLimits Z) {L M : ℕ} (hL : ValidSize L) (hM : ValidSize M) :
    0 ≤ Z L M := (D.x M hM).nonneg hL

theorem FiniteSpatialMomentLimits.rectangle_upper {Z : ℕ → ℕ → ℝ}
    (D : FiniteSpatialMomentLimits Z) {n m L M : ℕ}
    (hn : ValidSize n) (hm : ValidSize m) (hL : ValidSize L) (hM : ValidSize M)
    (hnL : n ≤ L) (hmM : m ≤ M) :
    Z L M ≤ (Z n m) ^ (((L : ℝ) * M) / ((n : ℝ) * m)) := by
  calc
    Z L M ≤ (Z n M) ^ ((L : ℝ) / n) := (D.x M hM).upper hn hL hnL
    _ ≤ ((Z n m) ^ ((M : ℝ) / m)) ^ ((L : ℝ) / n) :=
      Real.rpow_le_rpow (D.nonneg hn hM) ((D.y n hn).upper hm hM hmM) (by positivity)
    _ = (Z n m) ^ (((L : ℝ) * M) / ((n : ℝ) * m)) := by
      rw [← Real.rpow_mul (D.nonneg hn hm)]
      congr 1
      field_simp

theorem FiniteSpatialMomentLimits.rectangle_lower {Z : ℕ → ℕ → ℝ}
    (D : FiniteSpatialMomentLimits Z) {L M N Q : ℕ}
    (hL : ValidSize L) (hM : ValidSize M) (hN : ValidSize N) (hQ : ValidSize Q)
    (hLN : L ≤ N) (hMQ : M ≤ Q) :
    (Z N Q) ^ (((L : ℝ) * M) / ((N : ℝ) * Q)) ≤ Z L M := by
  calc
    (Z N Q) ^ (((L : ℝ) * M) / ((N : ℝ) * Q)) =
        ((Z N Q) ^ ((M : ℝ) / Q)) ^ ((L : ℝ) / N) := by
      rw [← Real.rpow_mul (D.nonneg hN hQ)]
      congr 1
      field_simp
    _ ≤ (Z N M) ^ ((L : ℝ) / N) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (D.nonneg hN hQ) _)
        ((D.y N hN).lower hM hQ hMQ) (by positivity)
    _ ≤ Z L M := (D.x M hM).lower hL hN hLN

/-- The full rectangular thermal-purity interpolation derived by limiting finite
spectra, without any countable spectral representation premise. -/
theorem finite_limit_spatial_purity_interpolation {Z W : ℕ → ℕ → ℝ}
    (DZ : FiniteSpatialMomentLimits Z) (DW : FiniteSpatialMomentLimits W)
    (hZpos : ∀ L M, ValidSize L → ValidSize M → 0 < Z L M)
    {n m L M : ℕ} (hn : ValidSize n) (hm : ValidSize m)
    (hL : ValidSize L) (hM : ValidSize M)
    (hnL : n ≤ L) (hL2n : L ≤ 2*n) (hmM : m ≤ M) (hM2m : M ≤ 2*m) :
    ((Z (2*n) m / Z n m ^ 2) ^ 4 *
      (Z (2*n) (2*m) / Z (2*n) m ^ 2) ^ 2 *
      (W (2*n) (2*m) / Z (2*n) (2*m) ^ 2)) ^
        (((L : ℝ) * M) / (4 * (n : ℝ) * m)) ≤ W L M / Z L M ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  rw [staircase_partition_product (hZpos n m hn hm).ne'
    (hZpos (2*n) m hn.double hm).ne' (hZpos (2*n) (2*m) hn.double hm.double).ne']
  apply interpolation_ratio_bound (hZpos n m hn hm)
    (DW.nonneg hn.double hm.double) (hZpos L M hL hM) (DW.nonneg hL hM)
  · have he : 4 * (((L : ℝ) * M) / (4 * (n : ℝ) * m)) =
        ((L : ℝ) * M) / ((n : ℝ) * m) := by field_simp
    rw [he]
    exact DZ.rectangle_upper hn hm hL hM hnL hmM
  · have he : (2 * (n : ℝ)) * (2 * (m : ℝ)) = 4 * (n : ℝ) * m := by ring
    simpa only [Nat.cast_mul, Nat.cast_ofNat, he] using
      DW.rectangle_lower hL hM hn.double hm.double hL2n hM2m

/-- Finite-dimensional spectral theorem converts a symmetric transfer matrix's
power trace to the actual real eigenvalue moment. -/
theorem symmetric_trace_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (n : ℕ) :
    Matrix.trace (A ^ n) = ∑ i, hA.eigenvalues i ^ n := by
  let U := unitary.toUnits hA.eigenvectorUnitary
  have hspec : A = (U : Matrix (Fin d) (Fin d) ℝ) * Matrix.diagonal hA.eigenvalues *
      (↑U⁻¹ : Matrix (Fin d) (Fin d) ℝ) := by
    simpa [U] using hA.spectral_theorem
  conv_lhs => rw [hspec]
  rw [Units.conj_pow, Matrix.trace_units_conj, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  rfl

theorem symmetric_trace_even_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) {n : ℕ} (hn : Even n) :
    Matrix.trace (A ^ n) = finiteAbsMoment hA.eigenvalues n := by
  rw [symmetric_trace_pow A hA n]
  unfold finiteAbsMoment
  apply Finset.sum_congr rfl
  intro i _
  exact (hn.pow_abs _).symm

/-- Concrete finite symmetric matrix approximants. Fixed width and approximation
index determine a matrix, and all valid longitudinal sizes use powers of that same
matrix. The sole analytic limit obligation is convergence of actual power traces. -/
structure FiniteSymmetricTransferLimit (Z : ℕ → ℝ) where
  dim : ℕ → ℕ
  transfer : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℝ
  symmetric : ∀ k, (transfer k).IsHermitian
  trace_limit : ∀ n, ValidSize n →
    Tendsto (fun k => Matrix.trace (transfer k ^ n)) atTop (𝓝 (Z n))

def FiniteSymmetricTransferLimit.toMomentLimit {Z : ℕ → ℝ}
    (D : FiniteSymmetricTransferLimit Z) : FiniteMomentLimit Z where
  dim := D.dim
  spectrum := fun k => (D.symmetric k).eigenvalues
  moment_limit := by
    intro n hn
    have he : (fun k => finiteAbsMoment (D.symmetric k).eigenvalues n) =
        (fun k => Matrix.trace (D.transfer k ^ n)) := by
      funext k
      exact (symmetric_trace_even_pow (D.transfer k) (D.symmetric k) hn.2).symm
    rw [he]
    exact D.trace_limit n hn

/-- Both transfer directions are required, separately at each fixed transverse width. -/
structure FiniteSymmetricSpatialLimits (Z : ℕ → ℕ → ℝ) where
  x : ∀ M, ValidSize M → FiniteSymmetricTransferLimit (fun L => Z L M)
  y : ∀ L, ValidSize L → FiniteSymmetricTransferLimit (fun M => Z L M)

def FiniteSymmetricSpatialLimits.toMomentLimits {Z : ℕ → ℕ → ℝ}
    (D : FiniteSymmetricSpatialLimits Z) : FiniteSpatialMomentLimits Z where
  x := fun M hM => (D.x M hM).toMomentLimit
  y := fun L hL => (D.y L hL).toMomentLimit

#print axioms FiniteMomentLimit.squaring_polynomial
#print axioms FiniteMomentLimit.ratio_squaring
#print axioms finite_limit_spatial_purity_interpolation
#print axioms symmetric_trace_even_pow
#print axioms FiniteSymmetricSpatialLimits.toMomentLimits

end BilayerGap
