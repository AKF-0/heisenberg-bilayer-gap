import Dressed.CubicKernelSupersolution
import Dressed.CubicSeedGraphChecks

/-! Whole-interval covariance supersolutions for the actual cubic kernels on
4×4, 8×4, 8×8 ordinary seed tori. This does not assert the physical Wick
moment recurrence; that separate operator bridge remains explicit. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicSeedChecks
open BilayerGap BilayerDressed.SeedGraphs
open BilayerDressed.CubicWick.FourRegularData

 theorem graph_square_cast (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) :
    ((graph n m h).adjacency*(graph n m h).adjacency) u v=(walk2 n m u v : ℝ) := by
  rw [walk2_eq n m hi]
  simp [graph,Matrix.mul_apply,Nat.cast_sum,Nat.cast_mul]

 theorem graph_off_square_cast (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) :
    offDiagonal ((graph n m h).adjacency*(graph n m h).adjacency) u v=
      (offWalk2 n m u v : ℝ) := by
  by_cases huv : u=v
  · simp [offDiagonal,offWalk2,huv]
  · simp [offDiagonal,offWalk2,huv,graph_square_cast n m h hi]

 theorem graph_cube_cast (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) : cube (graph n m h) u v=(walk3 n m u v : ℝ) := by
  rw [walk3_eq n m hi]
  simp [cube,graph,Matrix.mul_apply,Nat.cast_sum,Nat.cast_mul]

 theorem graph_signs (n m total : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (hc : CubicConditions n m total) : SeedSigns (graph n m h) := by
  constructor
  · intro u v huv
    change (adjacencyNat n m u v : ℝ)=1 at huv
    have hn : adjacencyNat n m u v=1 := by exact_mod_cast huv
    rw [graph_cube_cast n m h hi]
    exact_mod_cast hc.1 u v hn
  · intro u v
    rw [graph_off_square_cast n m h hi,graph_cube_cast n m h hi]
    rcases hc.2.1 u v with hzero | hzero
    · left; exact_mod_cast hzero
    · right; exact_mod_cast hzero

 theorem graph_endpoint_entry (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) :
    cubicEnvelope (graph n m h) (1/10) u v =
      ((1640*adjacencyNat n m u v+84*offWalk2 n m u v+5*walk3 n m u v : ℕ) : ℝ)/64000 := by
  simp only [cubicEnvelope,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [graph_cube_cast n m h hi,graph_off_square_cast n m h hi]
  change (1/10/4 : ℝ)*(adjacencyNat n m u v : ℝ) +
    ((1/10 : ℝ)^2/8)*((offWalk2 n m u v : ℝ)+(adjacencyNat n m u v : ℝ)) +
    ((1/10 : ℝ)^3/64)*(5*(walk3 n m u v : ℝ)+4*(offWalk2 n m u v : ℝ)-40*(adjacencyNat n m u v : ℝ)) = _
  push_cast
  ring

 theorem graph_endpoint_row_square (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (u : Torus.Vertex n m) :
    (∑ v, (cubicEnvelope (graph n m h) (1/10) u v)^2)=(total : ℝ)/64000^2 := by
  simp_rw [graph_endpoint_entry n m h hi,div_pow]
  rw [←Finset.sum_div]
  have hs : (∑ v, ((1640*adjacencyNat n m u v+84*offWalk2 n m u v+5*walk3 n m u v : ℕ) : ℝ)^2)=(total : ℝ) := by
    exact_mod_cast hc.2.2 u
  rw [hs]

/-- No norm-data oracle: the row-square input is proved from the actual graph. -/
theorem actual_kernel_row_square (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ∀ u, ∑ v, |cubicKernel (graph n m h) g u v|^2≤(total : ℝ)/64000^2 := by
  apply cubicKernel_rowSquare_bound (graph n m h) (graph_signs n m total h hi hc) g _ hg hmax
  exact fun u => (graph_endpoint_row_square n m total h hi hc u).le

/-- The concrete positive kernel, retaining its exact cubic g-dependence. -/
def positiveKernel (n m : ℕ) (h : Conditions n m) (g : ℝ) :
    Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℝ :=
  fun u v => |cubicKernel (graph n m h) g u v|

def tau (total : ℕ) : ℝ :=
  (493/4000)*((total : ℝ)/64000^2)/(1-(493/4000 : ℝ)^2)

/-- The .1 whole-interval supersolution is attached to the actual rung kernel. -/
theorem actual_kernel_supersolution (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    let B := positiveKernel n m h g
    let L := FiniteWick.covarianceMajorant B (tau total)
    ∀ u v, B u v+((B*B)*L) u v≤L u v := by
  dsimp only
  apply FiniteWick.exact_covariance_correction (positiveKernel n m h g)
    (493/4000) ((total : ℝ)/64000^2)
  · exact fun _ _ => abs_nonneg _
  · intro u v; unfold positiveKernel
    rw [cubicKernel_symmetric]
  · norm_num
  · norm_num
  · positivity
  · exact cubicKernel_row_bound (graph n m h) (graph_signs n m total h hi hc) g hg hmax
  · exact actual_kernel_row_square n m total h hi hc g hg hmax

/-- Actual 4×4 specialization, no external row-square assumption. -/
theorem four_by_four_supersolution (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    let B := positiveKernel 2 2 four_by_four_conditions g
    let L := FiniteWick.covarianceMajorant B (178671581/504222432000)
    ∀ u v, B u v+((B*B)*L) u v≤L u v := by
  have hh := actual_kernel_supersolution 2 2 11597344 four_by_four_conditions
    four_by_four_incidence four_by_four_cubic g hg hmax
  norm_num [tau] at hh ⊢
  exact hh

/-- Actual 8×4 specialization, preserving its distinct wrapping coefficient. -/
theorem eight_by_four_supersolution (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    let B := positiveKernel 4 2 eight_by_four_conditions g
    let L := FiniteWick.covarianceMajorant B (237228149/672296576000)
    ∀ u v, B u v+((B*B)*L) u v≤L u v := by
  have hh := actual_kernel_supersolution 4 2 11548632 eight_by_four_conditions
    eight_by_four_incidence eight_by_four_cubic g hg hmax
  norm_num [tau] at hh ⊢
  exact hh

/-- Actual 8×8 specialization, no external row-square assumption. -/
theorem eight_by_eight_supersolution (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    let B := positiveKernel 4 4 eight_by_eight_conditions g
    let L := FiniteWick.covarianceMajorant B (70868257/201688972800)
    ∀ u v, B u v+((B*B)*L) u v≤L u v := by
  have hh := actual_kernel_supersolution 4 4 11499920 eight_by_eight_conditions
    eight_by_eight_incidence eight_by_eight_cubic g hg hmax
  norm_num [tau] at hh ⊢
  exact hh

/-- Preserve the three Cartesian triplet colors with zero cross-color covariance. -/
theorem actual_three_color_supersolution (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    let B := positiveKernel n m h g
    let L := FiniteWick.covarianceMajorant B (tau total)
    let BC := FiniteWick.colorLift (χ := Fin 3) B
    let LC := FiniteWick.colorLift (χ := Fin 3) L
    ∀ u v, BC u v+((BC*BC)*LC) u v≤LC u v := by
  dsimp only
  exact FiniteWick.colorLift_supersolution _ _
    (actual_kernel_supersolution n m total h hi hc g hg hmax)

 theorem actual_three_color_row_bound (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10)
    (u : Torus.Vertex n m × Fin 3) :
    (∑ v, FiniteWick.colorLift (positiveKernel n m h g) u v)≤(493/4000 : ℝ) := by
  rw [FiniteWick.colorLift_row_sum]
  exact cubicKernel_row_bound (graph n m h) (graph_signs n m total h hi hc) g hg hmax u.1

 theorem actual_three_color_row_square (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10)
    (u : Torus.Vertex n m × Fin 3) :
    (∑ v, (FiniteWick.colorLift (positiveKernel n m h g) u v)^2)≤(total : ℝ)/64000^2 := by
  simpa [FiniteWick.colorLift,Fintype.sum_prod_type,positiveKernel] using
    actual_kernel_row_square n m total h hi hc g hg hmax u.1

end BilayerDressed.CubicSeedChecks
