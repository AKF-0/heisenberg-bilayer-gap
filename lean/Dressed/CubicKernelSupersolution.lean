import Dressed.QuadraticResidualKernel
import Dressed.ConcreteSeedGraphs
import Dressed.FiniteWickSupersolution

/-!
# The actual cubic rung kernel and its covariance supersolution

All row-square bounds refer to squared row-l2 norms. The graph certificate
below is separate from the finite physical creation-moment recurrence.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicWick
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Scalar sign separation on the bipartite seed graphs. -/
theorem cubic_scalar_abs (g a b c : ℝ) (hg : 0≤g)
    (ha : a=0 ∨ a=1) (hb : 0≤b) (hc : 0≤c)
    (hedge : a=1 → b=0 ∧ 8≤c) (hsep : b=0 ∨ c=0) :
    |-(g*a/4)+g^2*(b-a)/8-g^3*(5*c-4*b-40*a)/64| =
      g*a/4+g^2*(b+a)/8+g^3*(5*c+4*b-40*a)/64 := by
  rcases ha with ha | ha
  · subst a
    rcases hsep with hb0 | hc0
    · rw [hb0]
      have hh : -(g*0/4)+g^2*(0-0)/8-g^3*(5*c-4*0-40*0)/64 ≤ 0 := by
        have : 0≤g^3*c := mul_nonneg (by positivity) hc
        nlinarith
      rw [abs_of_nonpos hh]
      ring
    · rw [hc0]
      have hh : 0≤-(g*0/4)+g^2*(b-0)/8-g^3*(5*0-4*b-40*0)/64 := by
        have : 0≤g^3*b := mul_nonneg (by positivity) hb
        have : 0≤g^2*b := mul_nonneg (sq_nonneg g) hb
        nlinarith
      rw [abs_of_nonneg hh]
      ring
  · obtain ⟨hb0,hc8⟩ := hedge ha
    rw [ha,hb0]
    have hh : -(g*1/4)+g^2*(0-1)/8-g^3*(5*c-4*0-40*1)/64 ≤ 0 := by
      have : 0≤g^3*(5*c-40) := mul_nonneg (by positivity) (by linarith)
      nlinarith [sq_nonneg g]
    rw [abs_of_nonpos hh]
    ring

namespace FourRegularData
variable (G : BilayerDressed.FourRegularData V)

def cube : Matrix V V ℝ := G.adjacency*G.adjacency*G.adjacency

def cubicKernel (g : ℝ) : Matrix V V ℝ :=
  (-(g/4)) • G.adjacency + (g^2/8) •
      (offDiagonal (G.adjacency*G.adjacency)-G.adjacency) -
    (g^3/64) • ((5 : ℝ) • cube G -
      (4 : ℝ) • offDiagonal (G.adjacency*G.adjacency)-(40 : ℝ) • G.adjacency)

def cubicEnvelope (g : ℝ) : Matrix V V ℝ :=
  (g/4) • G.adjacency + (g^2/8) •
      (offDiagonal (G.adjacency*G.adjacency)+G.adjacency) +
    (g^3/64) • ((5 : ℝ) • cube G +
      (4 : ℝ) • offDiagonal (G.adjacency*G.adjacency)-(40 : ℝ) • G.adjacency)

def SeedSigns : Prop :=
  (∀ i j, G.adjacency i j=1 → 8≤cube G i j) ∧
  (∀ i j, offDiagonal (G.adjacency*G.adjacency) i j=0 ∨ cube G i j=0)

theorem cube_nonneg (i j : V) : 0≤cube G i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg (G.square_entry_nonneg i k) (G.entry_nonneg k j)

theorem cube_symmetric (i j : V) : cube G i j=cube G j i := by
  have hD : G.adjacency.transpose=G.adjacency := by
    ext i j; exact G.symmetric j i
  have h : (cube G).transpose=cube G := by simp [cube, Matrix.transpose_mul,hD,mul_assoc]
  exact congrFun (congrFun h j) i

theorem cube_row_sum (i : V) : (∑ j, cube G i j)=64 := by
  simp only [cube, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.degree]
  rw [← Finset.sum_mul]
  change (∑ k, (G.adjacency*G.adjacency) i k)*4=64
  rw [G.square_row_sum]
  norm_num

theorem envelope_cubic_coefficient_nonneg (h : SeedSigns G) (i j : V) :
    0≤5*cube G i j + 4*offDiagonal (G.adjacency*G.adjacency) i j -40*G.adjacency i j := by
  rcases G.binary i j with hD | hD
  · rw [hD]
    nlinarith [cube_nonneg G i j, G.off_square_nonneg i j]
  · have hc := h.1 i j hD
    rw [hD]
    nlinarith [G.off_square_nonneg i j]

theorem cubicKernel_abs (h : SeedSigns G) (g : ℝ) (hg : 0≤g) (i j : V) :
    |cubicKernel G g i j|=cubicEnvelope G g i j := by
  have hh := cubic_scalar_abs g (G.adjacency i j)
    (offDiagonal (G.adjacency*G.adjacency) i j) (cube G i j) hg
    (G.binary i j) (G.off_square_nonneg i j) (cube_nonneg G i j)
    (fun he => ⟨by simp [offDiagonal,G.triangle_free i j he], h.1 i j he⟩) (h.2 i j)
  simpa only [cubicKernel, cubicEnvelope, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, neg_mul, div_mul_eq_mul_div] using hh

theorem cubicEnvelope_row_sum (g : ℝ) (i : V) :
    (∑ j, cubicEnvelope G g i j)=g+2*g^2+(13/4 : ℝ)*g^3 := by
  simp only [cubicEnvelope, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    G.degree, G.off_square_row_sum, cube_row_sum]
  ring

theorem cubicKernel_symmetric (g : ℝ) (i j : V) :
    cubicKernel G g i j=cubicKernel G g j i := by
  simp only [cubicKernel, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, offDiagonal]
  rw [G.symmetric i j, G.square_symmetric i j, cube_symmetric G i j]
  simp only [eq_comm]

theorem cubicEnvelope_monotone (h : SeedSigns G) (g t : ℝ)
    (hg : 0≤g) (hgt : g≤t) (i j : V) :
    cubicEnvelope G g i j≤cubicEnvelope G t i j := by
  have ht : 0≤t := le_trans hg hgt
  have h2 : g^2≤t^2 := pow_le_pow_left₀ hg hgt 2
  have h3 : g^3≤t^3 := pow_le_pow_left₀ hg hgt 3
  have hc1 := mul_le_mul_of_nonneg_right hgt (G.entry_nonneg i j)
  have hc2 := mul_le_mul_of_nonneg_right h2
    (add_nonneg (G.off_square_nonneg i j) (G.entry_nonneg i j))
  have hc3 := mul_le_mul_of_nonneg_right h3 (envelope_cubic_coefficient_nonneg G h i j)
  simp only [cubicEnvelope, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  nlinarith

/-- Whole-interval row mass of the actual cubic kernel. -/
theorem cubicKernel_row_bound (h : SeedSigns G) (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ∀ i, ∑ j, |cubicKernel G g i j|≤(493/4000 : ℝ) := by
  intro i
  simp_rw [cubicKernel_abs G h g hg]
  calc
    _ ≤ ∑ j, cubicEnvelope G (1/10) i j := Finset.sum_le_sum fun j _ =>
      cubicEnvelope_monotone G h g (1/10) hg hmax i j
    _ = _ := by rw [cubicEnvelope_row_sum]; norm_num

/-- Actual squared-row norms reduce monotonically to the exact endpoint. -/
theorem cubicKernel_rowSquare_bound (h : SeedSigns G) (g rowSquare : ℝ)
    (hg : 0≤g) (hmax : g≤1/10)
    (he : ∀ i, ∑ j, (cubicEnvelope G (1/10) i j)^2≤rowSquare) :
    ∀ i, ∑ j, |cubicKernel G g i j|^2≤rowSquare := by
  intro i
  apply le_trans (Finset.sum_le_sum fun j _ => ?_) (he i)
  rw [cubicKernel_abs G h g hg]
  apply pow_le_pow_left₀ _ (cubicEnvelope_monotone G h g (1/10) hg hmax i j)
  rw [← cubicKernel_abs G h g hg]
  exact abs_nonneg _

end FourRegularData
end BilayerDressed.CubicWick
