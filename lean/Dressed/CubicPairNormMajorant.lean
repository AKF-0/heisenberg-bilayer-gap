import Dressed.FinitePairNormRecursion
import Dressed.FinitePairHomogeneousBound
import Dressed.ReferenceAdjacencyBounds
import Dressed.CubicSeedSupersolution

/-!
# Physical cubic-kernel instantiation of the finite pair majorant

The signed cubic kernel is lifted diagonally in the three colors. Its q and T
inputs are derived from actual finite row and trace bounds, not assumed norms.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicPairNorm
open Matrix BilayerGap FiniteOccupation
open CubicWick.FourRegularData CubicSeedChecks
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
section SpectralBound
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- The square PSD bound is derived from actual row sums and finite spectral
vectors, rather than left as a physical-kernel assumption. -/
theorem square_bound_of_abs_row (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (r : ℝ) (hrow : HasAbsRowBound A r) :
    ((r ^ 2) • (1 : Matrix I I ℝ) - A * A).PosSemidef := by
  let Q : Matrix I I ℝ := hA.eigenvectorUnitary
  have hQ : Q.transpose * Q = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hQQ : Q * Q.transpose = 1 := Matrix.mul_eq_one_comm.mp hQ
  have hd : Q.transpose * A * Q = Matrix.diagonal hA.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hA.star_mul_self_mul_eq_diagonal
  have hdiag : Q.transpose * ((r ^ 2) • (1 : Matrix I I ℝ) - A * A) * Q =
      Matrix.diagonal (fun i => r ^ 2 - (hA.eigenvalues i) ^ 2) := by
    rw [mul_sub, sub_mul, CoupledQuadratic.orthogonal_conjugate_mul Q A A hQQ, hd]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, hQ,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · simp [hij]
  have hp : (Q.transpose * ((r ^ 2) • (1 : Matrix I I ℝ) - A * A) * Q).PosSemidef := by
    rw [hdiag]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hb := ReferenceAdjacency.eigenvalue_abs_le_row A hA r hrow i
    have hr : 0 ≤ r := (abs_nonneg _).trans hb
    have hs := sq_le_sq₀ (abs_nonneg (hA.eigenvalues i)) hr
    have hh : (hA.eigenvalues i)^2 ≤ r^2 := by
      simpa only [sq_abs] using hs.mpr hb
    exact sub_nonneg.mpr hh
  have hh := hp.mul_mul_conjTranspose_same Q
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  have he : Q * (Q.transpose * ((r ^ 2) • (1 : Matrix I I ℝ) - A * A) * Q) * Q.transpose =
      ((r ^ 2) • (1 : Matrix I I ℝ) - A * A) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q.transpose, hQQ, Matrix.one_mul, Matrix.mul_one]
  rwa [he] at hh
end SpectralBound

/-- The actual signed cubic rung kernel, with exactly three diagonal colors. -/
def modeKernel (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ) :
    Matrix (Mode (Torus.Vertex n m)) (Mode (Torus.Vertex n m)) ℝ :=
  FiniteWick.colorLift (χ := Fin 3) (cubicKernel (SeedGraphs.graph n m h) g)

theorem modeKernel_symmetric (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ)
    (i j : Mode (Torus.Vertex n m)) : modeKernel n m h g i j = modeKernel n m h g j i := by
  simp only [modeKernel, FiniteWick.colorLift, cubicKernel_symmetric (SeedGraphs.graph n m h) g i.1 j.1]
  simp only [eq_comm]

theorem modeKernel_hermitian (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ) :
    (modeKernel n m h g).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  exact modeKernel_symmetric n m h g j i

/-- The physical row bound has no multiplicative color factor. -/
theorem modeKernel_row_bound (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    HasAbsRowBound (modeKernel n m h g) (493/4000) := by
  intro u
  simpa [absRowSum, modeKernel, FiniteWick.colorLift, Fintype.sum_prod_type, apply_ite] using
    cubicKernel_row_bound (SeedGraphs.graph n m h) (graph_signs n m total h hi hc) g hg hmax u.1

/-- The scalar q input is proved PSD for the actual signed colored cubic kernel. -/
theorem modeKernel_square_bound (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    (((493/4000 : ℝ)^2) • (1 : Matrix (Mode (Torus.Vertex n m)) (Mode (Torus.Vertex n m)) ℝ) -
      modeKernel n m h g * modeKernel n m h g).PosSemidef :=
  square_bound_of_abs_row _ (modeKernel_hermitian n m h g) _
    (modeKernel_row_bound n m total h hi hc g hg hmax)

/-- Each colored row retains the actual rung row-square bound, not three times it. -/
theorem modeKernel_row_square (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (u : Mode (Torus.Vertex n m)) :
    (∑ v, |modeKernel n m h g u v|^2) ≤ (total : ℝ)/64000^2 := by
  simpa [modeKernel, FiniteWick.colorLift, Fintype.sum_prod_type] using
    actual_kernel_row_square n m total h hi hc g hg hmax u.1

/-- The trace alone carries the three-color factor. -/
theorem modeKernel_trace_bound (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    Matrix.trace (modeKernel n m h g * modeKernel n m h g) ≤
      3 * (Fintype.card (Torus.Vertex n m) : ℝ) * ((total : ℝ)/64000^2) := by
  have he : Matrix.trace (modeKernel n m h g * modeKernel n m h g) =
      ∑ u, ∑ v, |modeKernel n m h g u v|^2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq_abs]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro v _
    rw [modeKernel_symmetric n m h g v u]
    ring
  rw [he]
  calc
    _ ≤ ∑ _u : Mode (Torus.Vertex n m), (total : ℝ)/64000^2 :=
      Finset.sum_le_sum (fun u _ => modeKernel_row_square n m total h hi hc g hg hmax u)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
      ring


/-- The exact rational row-square operator coefficient κ². -/
def coefficientQ : ℚ := (493/4000)^2

/-- The exact rational physical trace majorant, including the three colors. -/
def traceMajorant (n m total : ℕ) : ℚ :=
  3 * (Fintype.card (Torus.Vertex n m) : ℚ) * ((total : ℚ)/64000^2)

/-- The actual signed cubic pair vector obeys the exact rational majorant.
No PSD, row bound, trace bound, or pair norm remains an external premise. -/
theorem actual_finiteTrial_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) :
    ‖(TotalCutoff.PairNorm.finiteTrial (modeKernel n m h g) L :
      TotalCutoff.PairNorm.Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤
      ((∑ k ∈ Finset.range (L + 1),
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (traceMajorant n m total) k : ℚ) : ℝ) := by
  apply TotalCutoff.PairNorm.finiteTrial_norm_sq_le_rational _
    (modeKernel_symmetric n m h g) hNM
  · norm_num [coefficientQ]
  · unfold traceMajorant
    positivity
  · simpa only [coefficientQ, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using
      modeKernel_square_bound n m total h hi hc g hg hmax
  · simpa only [traceMajorant, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat] using modeKernel_trace_bound n m total h hi hc g hg hmax

theorem four_by_four_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) :
    ‖(TotalCutoff.PairNorm.finiteTrial (modeKernel 2 2 SeedGraphs.four_by_four_conditions g) L :
      TotalCutoff.PairNorm.Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤
      ((∑ k ∈ Finset.range (L + 1),
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (1087251/8000000) k : ℚ) : ℝ) := by
  have hh := actual_finiteTrial_norm_sq_le hNM 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax L
  norm_num [traceMajorant, Torus.Vertex] at hh
  simpa only [Rat.cast_sum] using hh

theorem eight_by_four_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) :
    ‖(TotalCutoff.PairNorm.finiteTrial (modeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) L :
      TotalCutoff.PairNorm.Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤
      ((∑ k ∈ Finset.range (L + 1),
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (4330737/16000000) k : ℚ) : ℝ) := by
  have hh := actual_finiteTrial_norm_sq_le hNM 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax L
  norm_num [traceMajorant, Torus.Vertex] at hh
  simpa only [Rat.cast_sum] using hh

theorem eight_by_eight_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) :
    ‖(TotalCutoff.PairNorm.finiteTrial (modeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) L :
      TotalCutoff.PairNorm.Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤
      ((∑ k ∈ Finset.range (L + 1),
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (431247/800000) k : ℚ) : ℝ) := by
  have hh := actual_finiteTrial_norm_sq_le hNM 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax L
  norm_num [traceMajorant, Torus.Vertex] at hh
  simpa only [Rat.cast_sum] using hh

/-- The physical signed cubic trial obeys the weighted homogeneous bound, with
both the operator-square coefficient and trace bound discharged from the graph. -/
theorem actual_homogeneous_finiteTrial_norm_sq_le {M N d : ℕ}
    (hNM : N ≤ M) (hseed : d ≤ N)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex n m) → ℕ) → ℝ) (L : ℕ) :
    ‖TotalCutoff.PairHomogeneous.homogeneousAction d r
      (TotalCutoff.PairNorm.finiteTrial (modeKernel n m h g) L :
        TotalCutoff.PairNorm.Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤
      ‖TotalCutoff.PairHomogeneous.homogeneousAction d r
        (TotalCutoff.PairNorm.vacuumVector :
          TotalCutoff.PairNorm.Hilbert (Torus.Vertex n m) M N)‖ ^ 2 *
      ((∑ k ∈ Finset.range (L + 1), ((2*k+d).choose d : ℚ) *
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (traceMajorant n m total) k : ℚ) : ℝ) := by
  apply TotalCutoff.PairHomogeneous.homogeneous_finiteTrial_norm_sq_le_rational _
    (modeKernel_symmetric n m h g) hNM hseed
  · norm_num [coefficientQ]
  · unfold traceMajorant
    positivity
  · simpa only [coefficientQ, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using
      modeKernel_square_bound n m total h hi hc g hg hmax
  · simpa only [traceMajorant, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat] using modeKernel_trace_bound n m total h hi hc g hg hmax

/-- The positive cubic comparison kernel. This is not the signed trial kernel;
its norm bound is proved separately from the same row data. -/
def absoluteModeKernel (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ) :
    Matrix (Mode (Torus.Vertex n m)) (Mode (Torus.Vertex n m)) ℝ :=
  FiniteWick.colorLift (χ := Fin 3) (CubicSeedChecks.positiveKernel n m h g)

theorem absoluteModeKernel_apply (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ)
    (i j : Mode (Torus.Vertex n m)) :
    absoluteModeKernel n m h g i j = |modeKernel n m h g i j| := by
  simp only [absoluteModeKernel, modeKernel, FiniteWick.colorLift,
    CubicSeedChecks.positiveKernel]
  split_ifs <;> simp

theorem absoluteModeKernel_symmetric (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ)
    (i j : Mode (Torus.Vertex n m)) :
    absoluteModeKernel n m h g i j = absoluteModeKernel n m h g j i := by
  rw [absoluteModeKernel_apply, absoluteModeKernel_apply, modeKernel_symmetric n m h g i j]

theorem absoluteModeKernel_hermitian (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ) :
    (absoluteModeKernel n m h g).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  exact absoluteModeKernel_symmetric n m h g j i

theorem absoluteModeKernel_row_bound (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    HasAbsRowBound (absoluteModeKernel n m h g) (493/4000) := by
  intro i
  simpa only [absRowSum, absoluteModeKernel_apply, abs_abs] using
    modeKernel_row_bound n m total h hi hc g hg hmax i

theorem absoluteModeKernel_square_bound (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    (((493/4000 : ℝ)^2) • (1 : Matrix (Mode (Torus.Vertex n m)) (Mode (Torus.Vertex n m)) ℝ) -
      absoluteModeKernel n m h g * absoluteModeKernel n m h g).PosSemidef :=
  square_bound_of_abs_row _ (absoluteModeKernel_hermitian n m h g) _
    (absoluteModeKernel_row_bound n m total h hi hc g hg hmax)

/-- Only the square traces coincide; no equality of signed and unsigned pair
state norms is used or claimed. -/
theorem absoluteModeKernel_trace_eq (n m : ℕ) (h : SeedGraphs.Conditions n m) (g : ℝ) :
    Matrix.trace (absoluteModeKernel n m h g * absoluteModeKernel n m h g) =
      Matrix.trace (modeKernel n m h g * modeKernel n m h g) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [absoluteModeKernel_apply, absoluteModeKernel_apply, modeKernel_symmetric n m h g j i]
  simpa only [← pow_two, sq_abs]

/-- The actual positive comparison Taylor vector has the same proved numerical
majorant as the signed trial, without identifying the two vectors. -/
theorem actual_absolute_finiteTrial_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) :
    ‖(TotalCutoff.PairNorm.finiteTrial (absoluteModeKernel n m h g) L :
      TotalCutoff.PairNorm.Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤
      ((∑ k ∈ Finset.range (L + 1),
        TotalCutoff.PairNorm.rationalMajorant coefficientQ (traceMajorant n m total) k : ℚ) : ℝ) := by
  apply TotalCutoff.PairNorm.finiteTrial_norm_sq_le_rational _
    (absoluteModeKernel_symmetric n m h g) hNM
  · norm_num [coefficientQ]
  · unfold traceMajorant
    positivity
  · simpa only [coefficientQ, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using
      absoluteModeKernel_square_bound n m total h hi hc g hg hmax
  · rw [absoluteModeKernel_trace_eq]
    simpa only [traceMajorant, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat] using modeKernel_trace_bound n m total h hi hc g hg hmax

end BilayerDressed.CubicPairNorm
