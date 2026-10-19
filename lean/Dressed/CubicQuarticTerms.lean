import Dressed.QuarticBondRegrouping
import Dressed.CubicResidualPair

noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicQuarticTerms
open BilayerGap GlobalResidual QuarticBondRegrouping
open SeedGraphs CubicWick.FourRegularData
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Term (n m : ℕ) := GlobalTerm (Torus.xNext n m) (Torus.yNext n m)
abbrev DistinctTerm (n m : ℕ) := DistinctGlobalTerm (Torus.xNext n m) (Torus.yNext n m)

instance termFintype (n m : ℕ) : Fintype (Term n m) := Fintype.ofFinite _
instance distinctTermFintype (n m : ℕ) : Fintype (DistinctTerm n m) := Fintype.ofFinite _

def sites (n m : ℕ) (a : Term n m) : Fin 4 → Torus.Vertex n m :=
  globalTermSites (Torus.xNext n m) (Torus.yNext n m) a

def coefficient (n m : ℕ) (h : Conditions n m) (g : ℝ) (a : Term n m) : ℝ :=
  globalTermCoefficient (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g a

/-- The literal physical cubic-kernel quartic residual is this finite faithful sum. -/
theorem actual_residual4_eq_terms (n m : ℕ) (h : Conditions n m) (g : ℝ) :
    residual4 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g =
      ∑ a : Term n m, coefficient n m h g a • faithfulWord (sites n m a) :=
by
  classical
  exact (residual4_eq_global_terms (cubicKernel (graph n m h) g)
    (Torus.xNext n m) (Torus.yNext n m) g).trans
      (Finset.sum_congr (by ext; simp) (by intro a _; rfl))

/-- Actual physical matrix residual, on precisely the faithful source subtype. -/
theorem actual_matrix_residual4_eq_distinct_terms (n m : ℕ) (h : Conditions n m) (g : ℝ) :
    ((residual4 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g :
      creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m)) =
      ∑ a : DistinctTerm n m, coefficient n m h g a.val •
        (pairCreate (sites n m a.val 0) (sites n m a.val 1) *
          pairCreate (sites n m a.val 2) (sites n m a.val 3)) :=
by
  classical
  exact (coe_residual4_eq_distinct_terms (cubicKernel (graph n m h) g)
    (Torus.xNext n m) (Torus.yNext n m) g).trans
      (Finset.sum_congr (by ext; simp) (by intro a _; rfl))

section Translation
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def translateTerm (t : Torus.Vertex n m) : Term n m ≃ Term n m :=
  globalTermEquiv (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight t)
    (fun u => CubicSeedChecks.xNext_add n m u t)
    (fun u => CubicSeedChecks.yNext_add n m u t)

theorem sites_translate (t : Torus.Vertex n m) (a : Term n m) (i : Fin 4) :
    sites n m (translateTerm n m t a) i = sites n m a i + t :=
  globalTermSites_equiv _ _ _ _ _ a i

/-- Actual coefficient covariance is discharged from the frozen cubic kernel,
not assumed as a translation-invariant norm or a numerical certificate. -/
theorem coefficient_translate (h : Conditions n m) (g : ℝ)
    (t : Torus.Vertex n m) (a : Term n m) :
    coefficient n m h g (translateTerm n m t a) = coefficient n m h g a := by
  apply globalTermCoefficient_equiv
  exact fun u v => CubicResidualPair.kernel_translation n m h g u v t

def translateDistinctTerm (t : Torus.Vertex n m) : DistinctTerm n m ≃ DistinctTerm n m :=
  distinctGlobalTermEquiv (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight t)
    (fun u => CubicSeedChecks.xNext_add n m u t)
    (fun u => CubicSeedChecks.yNext_add n m u t)

theorem distinctSites_translate (t : Torus.Vertex n m) (a : DistinctTerm n m) (i : Fin 4) :
    sites n m (translateDistinctTerm n m t a).val i = sites n m a.val i + t :=
  distinctGlobalTermSites_equiv _ _ _ _ _ a i

theorem distinctCoefficient_translate (h : Conditions n m) (g : ℝ)
    (t : Torus.Vertex n m) (a : DistinctTerm n m) :
    coefficient n m h g (translateDistinctTerm n m t a).val = coefficient n m h g a.val := by
  apply distinctGlobalTermCoefficient_equiv
  exact fun u v => CubicResidualPair.kernel_translation n m h g u v t

end Translation
end BilayerDressed.CubicQuarticTerms
