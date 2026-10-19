import Dressed.QuarticIntegerDirect
import Dressed.QuarticIntegerKernelCache
import Dressed.QuarticRootedRowTable
import Dressed.QuarticIntegerNormEvaluation
import Dressed.CubicQuarticVacuumFormula

/-! A checked signed integer table is connected to the actual physical residual.
All rows are covered by the proved concrete rooted-support bijection. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerTable
open BilayerGap SeedGraphs CubicWick.FourRegularData
open QuarticIntegerArrays QuarticRootedRowTable
set_option maxHeartbeats 1500000

def expected (dictionary : Array Coefficients) (ids : Array (Fin 3→ℕ))
    {R : ℕ} (i : Fin R) (a : Fin 3) : Coefficients :=
  dictionary.getD ((ids.getD i.val 0) a) 0

/-- This certificate compares each actual signed coefficient array, including
zero rows, with the dictionary entry used by all later aggregates. -/
def Checked (n m R : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (kernelData : Array KernelCoefficients) (raw : Array Row)
    (dictionary : Array Coefficients) (ids : Array (Fin 3→ℕ)) : Prop :=
  ∀ i : Fin R,∀ a : Fin 3,
    QuarticIntegerDirect.forward (cachedKernel n m kernelData)
      (Torus.xNext n m) (Torus.yNext n m) (matchingSites n m raw R i a)=
        expected dictionary ids i a

variable (n m R : ℕ) [NeZero (2*n)] [NeZero (2*m)]
variable (kernelData : Array KernelCoefficients) (raw : Array Row)
variable (dictionary : Array Coefficients) (ids : Array (Fin 3→ℕ))
variable (hkernel : cachedKernel n m kernelData=kernel n m)
variable (hvalid : ∀ i : Fin R,Valid (area n m) (row raw i))
variable (hchecked : Checked n m R kernelData raw dictionary ids)

include hkernel hchecked in
/-- Actual canonical real coefficients, valid for every real coupling. -/
theorem actual_coefficient (h : Conditions n m) (hi : IncidenceIdentity n m)
    (g : ℝ) (i : Fin R) (a : Fin 3) :
    CubicQuarticCoefficientCount.coefficient n m h g
      (supportRow n m raw R hvalid i) a=
        QuarticIntegerArrays.evaluate (expected dictionary ids i a) g/524288 := by
  rw [QuarticIntegerDirect.actual_coefficient_evaluate n m h hi,
    actual_matchingTuple_eq n m raw R hvalid]
  have he := hchecked i a
  rw [hkernel] at he
  rw [QuarticIntegerDirect.coefficients,he]

/-- Integer coefficients of the complete rooted Gram polynomial. -/
def normCoefficients (b : ℕ) : QuarticIntegerNorm.NormCoefficients :=
  b • ∑ i : Fin R,QuarticIntegerNorm.gram (expected dictionary ids i)

theorem normCoefficients_evaluate (b : ℕ) (g : ℝ) :
    QuarticIntegerNorm.evaluate (normCoefficients R dictionary ids b) g/524288^2=
      (b:ℝ)*∑ i : Fin R,QuarticRootCounting.matchingWeight
        (fun a=>QuarticIntegerArrays.evaluate (expected dictionary ids i a) g/524288) := by
  rw [normCoefficients,QuarticIntegerNorm.evaluate_nsmul,
    QuarticIntegerNorm.evaluate_sum,mul_div_assoc,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact QuarticIntegerNorm.gram_evaluate_div _ _ _

include hkernel hvalid hchecked in
/-- Exact literal physical norm, not an independent polynomial ansatz. -/
theorem physical_norm_eq (h : Conditions n m) (hi : IncidenceIdentity n m)
    (hcode : StrictMono (fun i : Fin R=>code (area n m) (row raw i)))
    (hcard : R=(area n m-1).choose 3) (b : ℕ) (harea : area n m=4*b) (g : ℝ) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g :
      ConfigurationMatrix (Torus.Vertex n m)).toEuclideanLin vacuumVector‖^2=
      QuarticIntegerNorm.evaluate (normCoefficients R dictionary ids b) g/524288^2 := by
  rw [CubicQuarticVacuum.norm_sq_eq_rooted,
    rootedMass_eq_sum_rows n m raw R hvalid hcode hcard,
    normCoefficients_evaluate]
  have hc : (Fintype.card (Torus.Vertex n m):ℝ)/4=(b:ℝ) := by
    have hh : Fintype.card (Torus.Vertex n m)=4*b := by
      simpa [area,Fintype.card_prod] using harea
    rw [hh]
    push_cast
    ring
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext a
  exact actual_coefficient n m R kernelData raw dictionary ids hkernel hvalid hchecked h hi g i a

end BilayerDressed.QuarticIntegerTable
