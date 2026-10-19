import Dressed.SexticFaithfulLift
import Dressed.CubicSeedSupersolution
import Dressed.ScalarTrialMajorants

/-! Actual cubic sextic mass bounds on the entire interval 0 ≤ g ≤ 1/10.
Entrywise monotonicity is proved upstream; exact rooted edge checks provide
only the endpoint constants. No finite-sample inference is used. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicSexticMass
open BilayerGap SeedGraphs CubicSeedChecks SexticFaithfulLift
open CubicWick.FourRegularData
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
section Generic
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem outsideRow_nonneg (K : V → V → ℝ) (r s u : V) :
    0 ≤ outsideRow K r s u := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem outsideRow_le_full_sub_second (K : V → V → ℝ) (r s u : V) (hrs : r ≠ s) :
    outsideRow K r s u ≤ (∑ w, |K u w|) - |K u s| := by
  have h := GlobalResidual.sum_two_sites r s hrs (fun w => |K u w|)
  change (∑ w, |K u w|) = |K u r| + |K u s| + outsideRow K r s u at h
  linarith [abs_nonneg (K u r)]

theorem outsideRow_le_full_sub_first (K : V → V → ℝ) (r s u : V) (hrs : r ≠ s) :
    outsideRow K r s u ≤ (∑ w, |K u w|) - |K u r| := by
  have h := GlobalResidual.sum_two_sites r s hrs (fun w => |K u w|)
  change (∑ w, |K u w|) = |K u r| + |K u s| + outsideRow K r s u at h
  linarith [abs_nonneg (K u s)]

theorem outsideRow_cubic_le_endpoint (G : FourRegularData V) (hs : SeedSigns G)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (r s u : V) :
    outsideRow (cubicKernel G g) r s u ≤ outsideRow (cubicKernel G (1/10)) r s u := by
  apply Finset.sum_le_sum
  intro w hw
  rw [cubicKernel_abs G hs g hg, cubicKernel_abs G hs (1/10) (by norm_num)]
  exact cubicEnvelope_monotone G hs g (1/10) hg hmax u w

theorem endpoint_full_row (G : FourRegularData V) (hs : SeedSigns G) (u : V) :
    (∑ w, |cubicKernel G (1/10) u w|) = (493/4000 : ℝ) := by
  simp_rw [cubicKernel_abs G hs (1/10) (by norm_num)]
  rw [cubicEnvelope_row_sum]
  norm_num

theorem outsideRows_cubic_le (G : FourRegularData V) (hs : SeedSigns G)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (r s : V) (hrs : r ≠ s)
    (b : ℝ) (hb : |cubicKernel G (1/10) r s| = b) :
    outsideRow (cubicKernel G g) r s r ≤ 493/4000 - b ∧
    outsideRow (cubicKernel G g) r s s ≤ 493/4000 - b := by
  constructor
  · apply (outsideRow_cubic_le_endpoint G hs g hg hmax r s r).trans
    have h := outsideRow_le_full_sub_second (cubicKernel G (1/10)) r s r hrs
    simpa only [endpoint_full_row G hs, hb] using h
  · apply (outsideRow_cubic_le_endpoint G hs g hg hmax r s s).trans
    have h := outsideRow_le_full_sub_first (cubicKernel G (1/10)) r s s hrs
    simpa only [endpoint_full_row G hs, cubicKernel_symmetric G (1/10) s r, hb] using h

theorem ell6_le_uniform (K : V → V → ℝ) (ex ey : V → V) (g : ℝ)
    (hg : 0 ≤ g) (hmax : g ≤ 1/10) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxr : ∀ r, outsideRow K r (ex r) r ≤ x)
    (hxs : ∀ r, outsideRow K r (ex r) (ex r) ≤ x)
    (hyr : ∀ r, outsideRow K r (ey r) r ≤ y)
    (hys : ∀ r, outsideRow K r (ey r) (ey r) ≤ y) :
    ell6 K ex ey g ≤ (Fintype.card V : ℝ) / 20 * (x^4 + y^4) := by
  have he (r s : V) (z : ℝ) (hz : 0 ≤ z)
      (hr : outsideRow K r s r ≤ z) (hs : outsideRow K r s s ≤ z) :
      outsideRow K r s r ^ 2 * outsideRow K r s s ^ 2 ≤ z ^ 4 := by
    have h1 := pow_le_pow_left₀ (outsideRow_nonneg K r s r) hr 2
    have h2 := pow_le_pow_left₀ (outsideRow_nonneg K r s s) hs 2
    have h := mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg z)
    nlinarith
  have hsum :
      (∑ r, outsideRow K r (ex r) r ^ 2 * outsideRow K r (ex r) (ex r) ^ 2) +
        (∑ r, outsideRow K r (ey r) r ^ 2 * outsideRow K r (ey r) (ey r) ^ 2) ≤
      (Fintype.card V : ℝ) * (x^4+y^4) := by
    have h1 := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset V)) =>
      he r (ex r) x hx (hxr r) (hxs r))
    have h2 := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset V)) =>
      he r (ey r) y hy (hyr r) (hys r))
    simpa [mul_add] using add_le_add h1 h2
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ g/2)
  have hc := mul_le_mul_of_nonneg_right (show g/2 ≤ (1/20 : ℝ) by linarith)
    (show 0 ≤ (Fintype.card V : ℝ) * (x^4+y^4) by positivity)
  unfold ell6
  exact hm.trans (by nlinarith [hc])
end Generic
section ConcreteEdges
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- Exact natural numerator of the endpoint absolute cubic entry. -/
def endpointNumerator (u v : Torus.Vertex n m) : ℕ :=
  1640*adjacencyNat n m u v + 84*offWalk2 n m u v + 5*walk3 n m u v

theorem endpointNumerator_x_rooted (u : Torus.Vertex n m) :
    endpointNumerator n m u (Torus.xNext n m u) =
      endpointNumerator n m 0 (Torus.xNext n m 0) := by
  have hx : Torus.xNext n m u - u = Torus.xNext n m 0 := by
    simpa using congrArg (fun v : Torus.Vertex n m => v-u) (xNext_add n m 0 u)
  simp only [endpointNumerator, adjacency_rooted n m u, offWalk2_rooted n m u,
    walk3_rooted n m u, hx]

theorem endpointNumerator_y_rooted (u : Torus.Vertex n m) :
    endpointNumerator n m u (Torus.yNext n m u) =
      endpointNumerator n m 0 (Torus.yNext n m 0) := by
  have hy : Torus.yNext n m u - u = Torus.yNext n m 0 := by
    simpa using congrArg (fun v : Torus.Vertex n m => v-u) (yNext_add n m 0 u)
  simp only [endpointNumerator, adjacency_rooted n m u, offWalk2_rooted n m u,
    walk3_rooted n m u, hy]

theorem endpoint_bond_abs_x (total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total) (B : ℕ)
    (hB : endpointNumerator n m 0 (Torus.xNext n m 0) = B) (u : Torus.Vertex n m) :
    |cubicKernel (graph n m h) (1/10) u (Torus.xNext n m u)| = (B : ℝ)/64000 := by
  rw [cubicKernel_abs _ (graph_signs n m total h hi hc) _ (by norm_num),
    graph_endpoint_entry n m h hi]
  change (endpointNumerator n m u (Torus.xNext n m u) : ℝ)/64000 = _
  rw [endpointNumerator_x_rooted, hB]

theorem endpoint_bond_abs_y (total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total) (B : ℕ)
    (hB : endpointNumerator n m 0 (Torus.yNext n m 0) = B) (u : Torus.Vertex n m) :
    |cubicKernel (graph n m h) (1/10) u (Torus.yNext n m u)| = (B : ℝ)/64000 := by
  rw [cubicKernel_abs _ (graph_signs n m total h hi hc) _ (by norm_num),
    graph_endpoint_entry n m h hi]
  change (endpointNumerator n m u (Torus.yNext n m u) : ℝ)/64000 = _
  rw [endpointNumerator_y_rooted, hB]

theorem actual_ell6_le (total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (Bx By : ℕ) (hBx : endpointNumerator n m 0 (Torus.xNext n m 0) = Bx)
    (hBy : endpointNumerator n m 0 (Torus.yNext n m 0) = By)
    (hx : 0 ≤ (493/4000 : ℝ) - Bx/64000)
    (hy : 0 ≤ (493/4000 : ℝ) - By/64000)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ell6 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g ≤
      (Fintype.card (Torus.Vertex n m) : ℝ)/20 *
        (((493/4000 : ℝ)-Bx/64000)^4 + ((493/4000 : ℝ)-By/64000)^4) := by
  have hn : 0 < n := by have hh := NeZero.ne (2*n); omega
  have hm : 0 < m := by have hh := NeZero.ne (2*m); omega
  have hxx (u : Torus.Vertex n m) := outsideRows_cubic_le (graph n m h)
    (graph_signs n m total h hi hc) g hg hmax u (Torus.xNext n m u)
    (Torus.xNext_ne n m hn u).symm _ (endpoint_bond_abs_x n m total h hi hc Bx hBx u)
  have hyy (u : Torus.Vertex n m) := outsideRows_cubic_le (graph n m h)
    (graph_signs n m total h hi hc) g hg hmax u (Torus.yNext n m u)
    (Torus.yNext_ne n m hm u).symm _ (endpoint_bond_abs_y n m total h hi hc By hBy u)
  exact ell6_le_uniform _ _ _ g hg hmax _ _ hx hy
    (fun u => (hxx u).1) (fun u => (hxx u).2)
    (fun u => (hyy u).1) (fun u => (hyy u).2)
end ConcreteEdges

/-- Only three tiny rooted graph checks; no many-body space is enumerated. -/
theorem endpoint_numerators16 :
    endpointNumerator 2 2 0 (Torus.xNext 2 2 0) = 1690 ∧
    endpointNumerator 2 2 0 (Torus.yNext 2 2 0) = 1690 := by decide +kernel

theorem endpoint_numerators32 :
    endpointNumerator 4 2 0 (Torus.xNext 4 2 0) = 1685 ∧
    endpointNumerator 4 2 0 (Torus.yNext 4 2 0) = 1690 := by decide +kernel

theorem endpoint_numerators64 :
    endpointNumerator 4 4 0 (Torus.xNext 4 4 0) = 1685 ∧
    endpointNumerator 4 4 0 (Torus.yNext 4 4 0) = 1685 := by decide +kernel

/-- Actual 4×4 sextic mass bound uniformly on the full physical interval. -/
theorem ell16_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ell6 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g ≤ (ScalarTrial.ell16_6 : ℝ) := by
  have h := actual_ell6_le 2 2 11597344 four_by_four_conditions four_by_four_incidence
    four_by_four_cubic 1690 1690 endpoint_numerators16.1 endpoint_numerators16.2
    (by norm_num) (by norm_num) g hg hmax
  norm_num [Torus.Vertex, ScalarTrial.ell16_6] at h ⊢
  exact h

/-- Actual 8×4 bound retains its distinct x/y wrapping counts. -/
theorem ell32_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ell6 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g ≤ (ScalarTrial.ell32_6 : ℝ) := by
  have h := actual_ell6_le 4 2 11548632 eight_by_four_conditions eight_by_four_incidence
    eight_by_four_cubic 1685 1690 endpoint_numerators32.1 endpoint_numerators32.2
    (by norm_num) (by norm_num) g hg hmax
  norm_num [Torus.Vertex, ScalarTrial.ell32_6] at h ⊢
  exact h

/-- Actual 8×8 mass bound, also consumed by the degree-six Wick405 mean. -/
theorem ell64_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ell6 (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g ≤ (ScalarTrial.ell64_6 : ℝ) := by
  have h := actual_ell6_le 4 4 11499920 eight_by_eight_conditions eight_by_eight_incidence
    eight_by_eight_cubic 1685 1685 endpoint_numerators64.1 endpoint_numerators64.2
    (by norm_num) (by norm_num) g hg hmax
  norm_num [Torus.Vertex, ScalarTrial.ell64_6] at h ⊢
  exact h


/-- Actual faithful 16-rung vacuum seed, with the frozen sextic scalar constant. -/
theorem vacuum16_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖vacuumImage (faithfulResidual6 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : FiniteOccupation.TotalCutoff.Op
        (Torus.Vertex 2 2) M N)‖ ^ 2 ≤ (ScalarTrial.F16_6 : ℝ) := by
  have h := faithfulResidual6_vacuum_norm_sq_le_envelope hNM hN
    (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2)
    g hg (ell16_le g hg hmax)
  simpa [ScalarTrial.F16_6] using h

/-- Actual faithful 32-rung vacuum seed, with the frozen sextic scalar constant. -/
theorem vacuum32_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖vacuumImage (faithfulResidual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : FiniteOccupation.TotalCutoff.Op
        (Torus.Vertex 4 2) M N)‖ ^ 2 ≤ (ScalarTrial.F32_6 : ℝ) := by
  have h := faithfulResidual6_vacuum_norm_sq_le_envelope hNM hN
    (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2)
    g hg (ell32_le g hg hmax)
  simpa [ScalarTrial.F32_6] using h

/-- Actual faithful 64-rung vacuum seed, with the frozen sextic scalar constant. -/
theorem vacuum64_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖vacuumImage (faithfulResidual6 (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g : FiniteOccupation.TotalCutoff.Op
        (Torus.Vertex 4 4) M N)‖ ^ 2 ≤ (ScalarTrial.F64_6 : ℝ) := by
  have h := faithfulResidual6_vacuum_norm_sq_le_envelope hNM hN
    (cubicKernel (graph 4 4 eight_by_eight_conditions) g) (Torus.xNext 4 4) (Torus.yNext 4 4)
    g hg (ell64_le g hg hmax)
  simpa [ScalarTrial.F64_6] using h

end BilayerDressed.CubicSexticMass
