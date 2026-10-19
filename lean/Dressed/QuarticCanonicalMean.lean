import Dressed.QuarticMeanTransport
import Dressed.QuarticActualCoefficients
import Dressed.CubicResidualPair

/-! The literal global quartic residual is identified with its signed canonical
coefficient dictionary. Its endpoint covariance weight has exact A/4 rooted
counting, using actual kernel/neighbor translations rather than an invariant
ordering assumption. Numerical polynomial envelopes are a separate layer.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticCanonicalMean
open Matrix FiniteOccupation FinitePhysicalWick QuarticPhysicalMean
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (enum : ∀ S : QuarticCanonical.Support V,Fin 4≃↥S.val)

def coefficients (K : V→V→ℝ) (ex ey : V≃V) (g : ℝ)
    (p : (QuarticCanonical.Support V×Fin 3)×(Fin 3×Fin 3)) : ℝ :=
  familyCoefficients (fun k : QuarticCanonical.Support V×Fin 3 =>
    QuarticActualCoefficients.coefficient enum K ex ey g k.1 k.2) p

def words (p : (QuarticCanonical.Support V×Fin 3)×(Fin 3×Fin 3)) : List (Mode V) :=
  familyWords (fun k : QuarticCanonical.Support V×Fin 3 =>QuarticCanonical.tuple enum k.1)
    Prod.snd p

def meanCoefficient (K : V→V→ℝ) (ex ey : V≃V) (g : ℝ) (L : V→V→ℝ) : ℝ :=
  ∑ S,canonicalMeanWeight enum L (QuarticActualCoefficients.coefficient enum K ex ey g) S

/-- This is the actual physical residual matrix, not a matching coefficient ansatz. -/
theorem physicalPolynomial_eq_residual4 (K : V→V→ℝ) (ex ey : V≃V) (g : ℝ) :
    physicalPolynomial (coefficients enum K ex ey g) (words enum)=
      ((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) :
        ConfigurationMatrix V) := by
  unfold coefficients words
  rw [family_physicalPolynomial,Fintype.sum_prod_type]
  exact (QuarticActualCoefficients.residual4_eq_canonical enum K ex ey g).symm

/-- Absolute values are taken only after the literal canonical signed fibers sum. -/
theorem wick_coefficient_eq (K : V→V→ℝ) (ex ey : V≃V) (g : ℝ) (L : V→V→ℝ) :
    (∑ p,|coefficients enum K ex ey g p| *
      FiniteWickPairings.wick (FiniteWick.colorLift (χ := Fin 3) L) (words enum p))=
        meanCoefficient enum K ex ey g L := by
  unfold coefficients words
  rw [family_wick_coefficient,Fintype.sum_prod_type]
  rfl

/-- Actual covariance symmetry of the endpoint absolute cubic kernel. -/
theorem endpoint_symmetric (n m : ℕ) (h : Conditions n m) (τ : ℝ) :
    ∀ u v,FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ u v=
      FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ v u := by
  apply FiniteWick.covarianceMajorant_symmetric
  intro u v
  simp only [positiveKernel,cubicKernel_symmetric]

/-- The actual coefficient and covariance transform together under the canonical
matching permutation. No site-ordering or free-action premise survives. -/
theorem cubic_mean_total_rooted (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (h : Conditions n m)
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex n m),Fin 4≃↥S.val)
    (g τ : ℝ) :
    meanCoefficient enum (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g
      (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ)=
      (Fintype.card (Torus.Vertex n m):ℝ)/4 *
        QuarticRootCounting.rootedMass
          (canonicalMeanWeight enum
            (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ)
            (QuarticActualCoefficients.coefficient enum (cubicKernel (graph n m h) g)
              (Torus.xNext n m) (Torus.yNext n m) g)) 0 := by
  unfold meanCoefficient
  apply canonicalMeanWeight_total_rooted enum _ (endpoint_symmetric n m h τ)
  · intro t u v
    exact CubicResidualPair.covarianceMajorant_translation n m h (1/10) τ u v t
  · intro t S j
    exact QuarticActualCoefficients.coefficient_equiv enum (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight t)
      (fun u=>xNext_add n m u t) (fun u=>yNext_add n m u t)
      (fun u v=>CubicResidualPair.kernel_translation n m h g u v t) g S j

end BilayerDressed.QuarticCanonicalMean
