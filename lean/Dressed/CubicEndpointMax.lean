import Dressed.CubicSexticMass
import Dressed.CubicPhysicalMeans

/-! Actual whole-graph endpoint covariance maxima for the sextic Wick bound.
Only short rooted graph counts are checked; no many-body space is enumerated. -/
noncomputable section
namespace BilayerDressed.CubicEndpointMax
open BilayerGap SeedGraphs CubicSeedChecks CubicSexticMass CubicWick.FourRegularData
open FiniteOccupation
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

 theorem endpoint_rooted (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (u v : Torus.Vertex n m) :
    endpointNumerator n m u v=endpointNumerator n m 0 (v-u) := by
  simp only [endpointNumerator,adjacency_rooted n m u,offWalk2_rooted n m u,
    walk3_rooted n m u]

 theorem maximum16 : ∀ q : Torus.Vertex 2 2,endpointNumerator 2 2 0 q ≤ 1690 := by
  decide +kernel
 theorem maximum32 : ∀ q : Torus.Vertex 4 2,endpointNumerator 4 2 0 q ≤ 1690 := by
  decide +kernel
 theorem maximum64 : ∀ q : Torus.Vertex 4 4,endpointNumerator 4 4 0 q ≤ 1685 := by
  decide +kernel

 theorem endpoint_abs_le (n m total : ℕ) [NeZero (2*n)] [NeZero (2*m)] (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total) (B : ℕ)
    (hB : ∀ q : Torus.Vertex n m,endpointNumerator n m 0 q ≤ B)
    (u v : Torus.Vertex n m) :
    |cubicKernel (graph n m h) (1/10) u v| ≤ (B:ℝ)/64000 := by
  rw [cubicKernel_abs _ (graph_signs n m total h hi hc) _ (by norm_num),
    graph_endpoint_entry n m h hi]
  change (endpointNumerator n m u v:ℝ)/64000 ≤ _
  rw [endpoint_rooted]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hB (v-u)) (by norm_num)

 theorem endpoint_mode_le (n m total : ℕ) [NeZero (2*n)] [NeZero (2*m)] (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total) (B : ℕ)
    (hB : ∀ q : Torus.Vertex n m,endpointNumerator n m 0 q ≤ B)
    (u v : Mode (Torus.Vertex n m)) :
    modeCovariance n m total h (1/10) u v ≤ (B:ℝ)/64000+tau total := by
  have ht : 0 ≤ tau total := by
    unfold tau
    exact div_nonneg (by positivity) (by norm_num)
  unfold modeCovariance FiniteWick.colorLift FiniteWick.covarianceMajorant positiveKernel
  split_ifs
  · exact add_le_add_right (endpoint_abs_le n m total h hi hc B hB _ _) _
  · positivity

 theorem mode16_le (u v : Mode (Torus.Vertex 2 2)) :
    modeCovariance 2 2 11597344 four_by_four_conditions (1/10) u v ≤
      1690/64000+tau 11597344 :=
  endpoint_mode_le 2 2 11597344 four_by_four_conditions four_by_four_incidence
    four_by_four_cubic 1690 maximum16 u v
 theorem mode32_le (u v : Mode (Torus.Vertex 4 2)) :
    modeCovariance 4 2 11548632 eight_by_four_conditions (1/10) u v ≤
      1690/64000+tau 11548632 :=
  endpoint_mode_le 4 2 11548632 eight_by_four_conditions eight_by_four_incidence
    eight_by_four_cubic 1690 maximum32 u v
 theorem mode64_le (u v : Mode (Torus.Vertex 4 4)) :
    modeCovariance 4 4 11499920 eight_by_eight_conditions (1/10) u v ≤
      1685/64000+tau 11499920 :=
  endpoint_mode_le 4 4 11499920 eight_by_eight_conditions eight_by_eight_incidence
    eight_by_eight_cubic 1685 maximum64 u v

end BilayerDressed.CubicEndpointMax
