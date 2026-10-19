import Dressed.QuarticActualCoefficients
import Dressed.QuarticSupportNorm

/-! Exact vacuum norm of the literal global quartic residual, expressed in its
actual signed canonical support fibers. This contains no numerical coefficient
estimate and no assumed identification with an external coefficient table. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticResidualSupportNorm
open GlobalResidual QuarticCanonical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The literal R4 is exactly the support-sum operator with its true fibers. -/
theorem residual_eq_operator (enum : ∀ S : Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) =
      QuarticSupportNorm.operator enum
        (QuarticActualCoefficients.coefficient enum K ex ey g) :=
  QuarticActualCoefficients.residual4_eq_canonical enum K ex ey g

/-- Exact physical norm formula, including the non-diagonal 9/3 matching Gram. -/
theorem residual_vacuum_norm_sq (enum : ∀ S : Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ‖((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V).toEuclideanLin
      vacuumVector‖^2 =
      ∑ S : Support V,
        (6*(∑ m : Fin 3,(QuarticActualCoefficients.coefficient enum K ex ey g S m)^2)+
          3*(∑ m : Fin 3,QuarticActualCoefficients.coefficient enum K ex ey g S m)^2) := by
  rw [residual_eq_operator]
  exact QuarticSupportNorm.operator_vacuum_norm_sq enum _

/-- A genuine finite coefficient-sum certificate transfers to the actual
physical quartic vacuum norm. The finite sum remains explicitly displayed. -/
theorem residual_vacuum_norm_sq_le (enum : ∀ S : Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g F : ℝ)
    (h : (∑ S : Support V,
        (6*(∑ m : Fin 3,(QuarticActualCoefficients.coefficient enum K ex ey g S m)^2)+
          3*(∑ m : Fin 3,QuarticActualCoefficients.coefficient enum K ex ey g S m)^2)) ≤ F) :
    ‖((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V).toEuclideanLin
      vacuumVector‖^2 ≤ F := by
  rw [residual_vacuum_norm_sq enum]
  exact h


/-- Exact physical vacuum norm as a rooted mass, with the actual source
translation used to derive weight invariance. Periodic supports are not
assumed to have trivial stabilizers. -/
theorem residual_vacuum_norm_sq_rooted [AddGroup V]
    (enum : ∀ S : Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V)
    (hx : ∀ u t, ex (u+t)=ex u+t) (hy : ∀ u t, ey (u+t)=ey u+t)
    (hK : ∀ a b t, K (a+t) (b+t)=K a b) (g : ℝ) :
    ‖((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V).toEuclideanLin
      vacuumVector‖^2 =
      (Fintype.card V : ℝ)/4 * QuarticRootCounting.rootedMass
        (fun S => QuarticRootCounting.matchingWeight
          (QuarticActualCoefficients.coefficient enum K ex ey g S)) 0 := by
  rw [residual_vacuum_norm_sq enum]
  simpa only [QuarticRootCounting.matchingWeight] using
    QuarticActualCoefficients.actual_rooted_weight enum K ex ey hx hy hK g

end BilayerDressed.QuarticResidualSupportNorm
