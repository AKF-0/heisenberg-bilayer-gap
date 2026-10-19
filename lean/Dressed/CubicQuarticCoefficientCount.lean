import Dressed.QuarticActualCoefficients
import Dressed.QuarticDirectCoefficient
import Dressed.QuarticRowMajorEnumeration
import Dressed.CubicQuarticTerms
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicQuarticCoefficientCount
open BilayerGap SeedGraphs CubicWick.FourRegularData
open QuarticRootCounting
set_option maxHeartbeats 3000000

/-- Actual signed cubic quartic coefficient in deterministic row-major matching order. -/
def coefficient (n m : ℕ) (h : Conditions n m) (g : ℝ)
    (S : Support (Torus.Vertex n m)) (a : Fin 3) : ℝ :=
  QuarticActualCoefficients.coefficient (QuarticRowMajor.enumeration n m)
    (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g S a

def matchingTuple (n m : ℕ) (S : Support (Torus.Vertex n m)) (a : Fin 3) :=
  QuarticActualCoefficients.matchingTuple (QuarticRowMajor.enumeration n m) S a

/-- Exact finite direct-coefficient formula with actual forward torus edges. -/
theorem coefficient_eq_forward_direct (n m : ℕ) (h : Conditions n m) (g : ℝ)
    (S : Support (Torus.Vertex n m)) (a : Fin 3) :
    coefficient n m h g S a = (g/2)*
      ((∑ u, QuarticDirectCoefficient.directCoefficient (cubicKernel (graph n m h) g)
        u (Torus.xNext n m u) (matchingTuple n m S a)) +
       ∑ u, QuarticDirectCoefficient.directCoefficient (cubicKernel (graph n m h) g)
        u (Torus.yNext n m u) (matchingTuple n m S a)) := by
  have hi := QuarticActualCoefficients.matchingTuple_injective
    (QuarticRowMajor.enumeration n m) S a
  unfold coefficient
  rw [QuarticActualCoefficients.coefficient_eq_bond_matching_sum
    (QuarticRowMajor.enumeration n m) _ _ _ g _ hi S a
    (QuarticActualCoefficients.matchingTuple_support _ S a)
    (QuarticActualCoefficients.matchingTuple_pairing _ S a)]
  simp only [QuarticDirectCoefficient.matchingCoefficient_eq_directCoefficient _ _ _ _ hi] <;> rfl

/-- Exact graph-size factor for the actual signed canonical quartic Gram weight.
This counts every rooted support, including periodic supports with stabilizers. -/
theorem actual_weight_eq_rooted (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (h : Conditions n m) (g : ℝ) :
    (∑ S : Support (Torus.Vertex n m), matchingWeight (coefficient n m h g S)) =
      (Fintype.card (Torus.Vertex n m) : ℝ)/4 *
        rootedMass (fun S => matchingWeight (coefficient n m h g S)) 0 := by
  apply QuarticActualCoefficients.actual_rooted_weight
  · exact fun u t => CubicSeedChecks.xNext_add n m u t
  · exact fun u t => CubicSeedChecks.yNext_add n m u t
  · exact fun u v t => CubicResidualPair.kernel_translation n m h g u v t

end BilayerDressed.CubicQuarticCoefficientCount

namespace BilayerDressed.QuarticRowMajor
open BilayerGap QuarticRootCounting

/-- A concrete increasing tuple is the actual deterministic support enumeration.
Arithmetic table proofs can use this instead of evaluating a bundled inverse. -/
theorem sites_eq_of_increasing (n m : ℕ) (S : Support (Torus.Vertex n m))
    (v : Fin 4 → Torus.Vertex n m) (hmem : ∀ i, v i ∈ S.val)
    (hinc : StrictMono (fun i => index n m (v i))) : sites n m S = v := by
  letI := vertexOrder n m
  have hm : @StrictMono (Fin 4) (Torus.Vertex n m) _ (vertexOrder n m).toPreorder v := hinc
  exact (Finset.orderEmbOfFin_unique S.property (f := v) hmem hm).symm
end BilayerDressed.QuarticRowMajor
