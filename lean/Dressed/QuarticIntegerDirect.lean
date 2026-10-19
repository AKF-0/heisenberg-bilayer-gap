import Dressed.QuarticIntegerArrays
import Dressed.QuarticDirectCoefficient
import Dressed.CubicQuarticCoefficientCount

/-! Exact common-denominator integer arrays for the actual R4 coefficient.
The eight matching orientations and both physical forward-edge families are
preserved. Signed coefficients are collected before any absolute value. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerDirect
open BilayerGap SeedGraphs CubicWick.FourRegularData
open QuarticIntegerArrays QuarticCoefficientFibers
set_option maxHeartbeats 1000000
variable {V : Type*} [DecidableEq V]

/-- Scaling a degree-two term requires q in addition to its two kernel factors. -/
theorem scaledOrderedWeight_scaling {R : Type*} [CommRing R]
    (q : R) (K : V→V→R) (u v a b c d : V) :
    scaledOrderedWeight q (fun x y=>q*K x y) u v a b c d =
      q^3*QuarticDirectCoefficient.orderedWeight K u v a b c d := by
  simp only [scaledOrderedWeight,QuarticDirectCoefficient.orderedWeight]
  split_ifs <;> ring

/-- Signed matching coefficient numerator before the physical edge sum. -/
def direct (K : V→V→KernelCoefficients) (u v : V) (s : Fin 4→V) : Coefficients :=
  ∑ i : Fin 8, ordered K u v
    (orientations s i 0) (orientations s i 1) (orientations s i 2) (orientations s i 3)

theorem direct_evaluate (Kz : V→V→KernelCoefficients) (Kr : V→V→ℝ) (g : ℝ)
    (hK : ∀ u v,evaluateKernel (Kz u v) g=64*Kr u v) (u v : V) (s : Fin 4→V) :
    evaluate (direct Kz u v s) g =
      (g*64^3)*QuarticDirectCoefficient.directCoefficient Kr u v s := by
  have ho (a b c d : V) : evaluate (ordered Kz u v a b c d) g =
      (g*64^3)*QuarticDirectCoefficient.orderedWeight Kr u v a b c d := by
    rw [ordered_evaluate]
    simp_rw [hK]
    rw [scaledOrderedWeight_scaling]
    ring
  rw [direct,evaluate_sum]
  simp_rw [ho]
  rw [←Finset.mul_sum]
  rfl

/-- Only sources incident to the displayed support are evaluated. -/
def forward (K : V→V→KernelCoefficients) (ex ey : V≃V) (s : Fin 4→V) : Coefficients :=
  (∑ u∈QuarticDirectCoefficient.incidentSources ex s,direct K u (ex u) s)+
  ∑ u∈QuarticDirectCoefficient.incidentSources ey s,direct K u (ey u) s

/-- The common denominator is exactly2*64^3=524288. -/
theorem forward_evaluate [Fintype V]
    (Kz : V→V→KernelCoefficients) (Kr : V→V→ℝ) (g : ℝ)
    (hK : ∀ u v,evaluateKernel (Kz u v) g=64*Kr u v)
    (ex ey : V≃V) (s : Fin 4→V) :
    evaluate (forward Kz ex ey s) g/524288 = (g/2)*
      ((∑ u,QuarticDirectCoefficient.directCoefficient Kr u (ex u) s)+
       ∑ u,QuarticDirectCoefficient.directCoefficient Kr u (ey u) s) := by
  rw [forward,evaluate_add,evaluate_sum,evaluate_sum]
  simp_rw [direct_evaluate Kz Kr g hK]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  rw [←QuarticDirectCoefficient.sum_directCoefficient_eq_incident,
    ←QuarticDirectCoefficient.sum_directCoefficient_eq_incident]
  ring

/-- Actual integer numerator array for a displayed torus matching tuple. -/
def coefficients (n m : ℕ) (s : Fin 4→Torus.Vertex n m) : Coefficients :=
  forward (kernel n m) (Torus.xNext n m) (Torus.yNext n m) s

theorem coefficients_evaluate (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) (s : Fin 4→Torus.Vertex n m) :
    evaluate (coefficients n m s) g/524288 = (g/2)*
      ((∑ u,QuarticDirectCoefficient.directCoefficient (cubicKernel (graph n m h) g)
        u (Torus.xNext n m u) s)+
       ∑ u,QuarticDirectCoefficient.directCoefficient (cubicKernel (graph n m h) g)
        u (Torus.yNext n m u) s) :=
  forward_evaluate _ _ g (fun u v=>kernel_evaluate n m h hi u v g) _ _ s

/-- The integer arithmetic evaluates to the actual signed physical coefficient,
not a separately supplied polynomial or coefficient table. -/
theorem actual_coefficient_evaluate (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ)
    (S : QuarticRootCounting.Support (Torus.Vertex n m)) (a : Fin 3) :
    CubicQuarticCoefficientCount.coefficient n m h g S a =
      evaluate (coefficients n m (CubicQuarticCoefficientCount.matchingTuple n m S a)) g/524288 := by
  rw [CubicQuarticCoefficientCount.coefficient_eq_forward_direct]
  exact (coefficients_evaluate n m h hi g _).symm

end BilayerDressed.QuarticIntegerDirect
