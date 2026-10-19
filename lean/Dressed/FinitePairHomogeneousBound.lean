import Dressed.FinitePairNormRecursion
import Dressed.FiniteHomogeneousCreationNorm

/-!
# Actual homogeneous residual amplification of the finite pair vector

This combines the independently proved occupation-convolution bound with the
actual finite pair-power recurrence. Every norm is a genuine finite Euclidean
norm, and different pair grades stay orthogonal after a homogeneous creator.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOccupation.TotalCutoff.PairHomogeneous
open Matrix PairNorm
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual homogeneous creation matrix acting on the finite Hilbert space. -/
def homogeneousAction {M N : ℕ} (d : ℕ) (r : (Mode V → ℕ) → ℝ) :
    Hilbert V M N →ₗ[ℝ] Hilbert V M N := (Homogeneous.homogeneousOperator d r).toEuclideanLin

lemma dot_self_eq_norm_sq {M N : ℕ} (x : Hilbert V M N) :
    dotProduct (WithLp.ofLp x) (WithLp.ofLp x) = ‖x‖ ^ 2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    real_inner_self_eq_norm_sq x

theorem grade_homogeneousAction {M N n : ℕ} (d : ℕ) (r : (Mode V → ℕ) → ℝ)
    {x : Hilbert V M N} (hx : HasGrade n x) :
    HasGrade (n + d) (homogeneousAction d r x) := by
  have hh := Homogeneous.homogeneousOperator_grade d r
    (x := WithLp.ofLp x) hx
  intro μ hμ
  exact hh μ hμ

/-- The homogeneous bound in genuine Hilbert norms. Only the vacuum seed must
fit the cutoff; any higher output truncation can only decrease its norm. -/
theorem homogeneousAction_norm_sq_le {M N n d : ℕ} (hNM : N ≤ M) (hseed : d ≤ N)
    (r : (Mode V → ℕ) → ℝ) {x : Hilbert V M N} (hx : HasGrade n x) :
    ‖homogeneousAction d r x‖ ^ 2 ≤
      ((n + d).choose d : ℝ) * ‖homogeneousAction d r (PairNorm.vacuumVector : Hilbert V M N)‖ ^ 2 * ‖x‖ ^ 2 := by
  have hh := Homogeneous.actual_homogeneous_vacuum_bound_truncated hNM hseed r
    (x := WithLp.ofLp x) hx
  change dotProduct
      ((Homogeneous.homogeneousOperator d r).mulVec (WithLp.ofLp x))
      ((Homogeneous.homogeneousOperator d r).mulVec (WithLp.ofLp x)) ≤
    ((n+d).choose d : ℝ) *
      dotProduct ((Homogeneous.homogeneousOperator d r).mulVec
        (WithLp.ofLp (PairNorm.vacuumVector : Hilbert V M N)))
        ((Homogeneous.homogeneousOperator d r).mulVec
        (WithLp.ofLp (PairNorm.vacuumVector : Hilbert V M N))) *
      dotProduct (WithLp.ofLp x) (WithLp.ofLp x) at hh
  have ha (A : Op V M N) (y : Hilbert V M N) :
      dotProduct (A.mulVec (WithLp.ofLp y)) (A.mulVec (WithLp.ofLp y)) =
        ‖A.toEuclideanLin y‖ ^ 2 := by
    simpa only [Matrix.ofLp_toEuclideanLin_apply] using
      dot_self_eq_norm_sq (A.toEuclideanLin y)
  rw [ha, ha, dot_self_eq_norm_sq] at hh
  exact hh

/-- Every fixed homogeneous residual preserves orthogonality between pair powers. -/
theorem homogeneous_pairVector_orthogonal {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (d : ℕ) (r : (Mode V → ℕ) → ℝ)
    (m n : ℕ) (hmn : m ≠ n) :
    ⟪homogeneousAction d r (pairVector B m : Hilbert V M N),
      homogeneousAction d r (pairVector B n)⟫ = 0 :=
  inner_eq_zero_of_grades
    (grade_homogeneousAction d r (grade_pairVector B m))
    (grade_homogeneousAction d r (grade_pairVector B n)) (by omega)

/-- Exact Pythagoras after applying one homogeneous residual to the finite trial. -/
theorem homogeneous_finiteTrial_norm_sq {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (d : ℕ) (r : (Mode V → ℕ) → ℝ) (L : ℕ) :
    ‖homogeneousAction d r (finiteTrial B L : Hilbert V M N)‖ ^ 2 =
      ∑ m ∈ Finset.range (L + 1), ‖homogeneousAction d r (pairVector B m : Hilbert V M N)‖ ^ 2 := by
  rw [finiteTrial, map_sum]
  exact orthogonal_sum_norm_sq _ _
    (fun m _ n _ hmn => homogeneous_pairVector_orthogonal B d r m n hmn)

/-- The finite weighted residual majorant, derived from actual homogeneous
operators and actual normalized pair powers, not a supplied amplification bound. -/
theorem homogeneous_finiteTrial_norm_sq_le {M N d : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (hseed : d ≤ N) (r : (Mode V → ℕ) → ℝ)
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ T) (L : ℕ) :
    ‖homogeneousAction d r (finiteTrial B L : Hilbert V M N)‖ ^ 2 ≤
      ‖homogeneousAction d r (PairNorm.vacuumVector : Hilbert V M N)‖ ^ 2 *
        ∑ m ∈ Finset.range (L + 1), ((2*m+d).choose d : ℝ) * majorant q T m := by
  rw [homogeneous_finiteTrial_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hh := homogeneousAction_norm_sq_le hNM hseed r
    (x := (pairVector B m : Hilbert V M N)) (grade_pairVector B m)
  have hb := pairVector_norm_sq_le_majorant B hB hNM q T hq hT hbound htrace m
  calc
    _ ≤ ((2*m+d).choose d : ℝ) * ‖homogeneousAction d r (PairNorm.vacuumVector : Hilbert V M N)‖ ^ 2 *
        ‖(pairVector B m : Hilbert V M N)‖ ^ 2 := hh
    _ ≤ ((2*m+d).choose d : ℝ) * ‖homogeneousAction d r (PairNorm.vacuumVector : Hilbert V M N)‖ ^ 2 *
        majorant q T m := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Exact rational weighted sum, including the binomial amplification factor. -/
theorem homogeneous_finiteTrial_norm_sq_le_rational {M N d : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (hseed : d ≤ N) (r : (Mode V → ℕ) → ℝ)
    (q T : ℚ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : ((q : ℝ) • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ (T : ℝ)) (L : ℕ) :
    ‖homogeneousAction d r (finiteTrial B L : Hilbert V M N)‖ ^ 2 ≤
      ‖homogeneousAction d r (PairNorm.vacuumVector : Hilbert V M N)‖ ^ 2 *
        ((∑ m ∈ Finset.range (L + 1), ((2*m+d).choose d : ℚ) * rationalMajorant q T m : ℚ) : ℝ) := by
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, rationalMajorant_cast] using
    homogeneous_finiteTrial_norm_sq_le B hB hNM hseed r (q : ℝ) (T : ℝ)
      (by exact_mod_cast hq) (by exact_mod_cast hT) hbound htrace L
end BilayerDressed.FiniteOccupation.TotalCutoff.PairHomogeneous
