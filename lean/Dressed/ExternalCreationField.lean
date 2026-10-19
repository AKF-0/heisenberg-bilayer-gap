import Dressed.FourRegularKernel
import Dressed.CreationNorms
import Dressed.GlobalResidualSplit

/-! Direct finite hard-core external-field bounds, in the genuine Hilbert norm. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
open PhysicalGram
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace FourRegularData
variable (G : FourRegularData V)

 theorem edge_ne (u v : V) (huv : G.adjacency u v=1) : u≠v := by
  intro h
  subst v
  rw [G.diagonal] at huv
  norm_num at huv

/-- Exact remaining row mass after deleting the two endpoints of an actual edge. -/
 theorem kernel_outside_mass (g : ℝ) (hg : 0≤g) (u v : V)
    (huv : G.adjacency u v=1) :
    (∑ w : Outside u v, |G.kernel g u w|) = 3*g/4+15*g^2/8 := by
  have hh := GlobalResidual.sum_two_sites u v (G.edge_ne u v huv)
    (fun w => |G.kernel g u w|)
  have hr := G.kernel_abs_row_sum g hg u
  unfold absRowSum at hr
  rw [G.kernel_diagonal, G.kernel_on_edge g u v huv, abs_zero,
    abs_neg, abs_of_nonneg (by positivity : 0≤g/4+g^2/8)] at hh
  rw [hr] at hh
  linarith

 theorem kernel_outside_mass_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (u v : V) (huv : G.adjacency u v=1) :
    (∑ w : Outside u v, |G.kernel g u w|) ≤ (39/50 : ℝ)*g := by
  rw [G.kernel_outside_mass g hg u v huv]
  nlinarith [mul_le_mul_of_nonneg_right hmax hg]

end FourRegularData

/-- An actual creation field on a specified finite set of sites. -/
def finiteCreationField {I : Type*} [Fintype I]
    (site : I → V) (a : I → ℝ) (α : Fin 3) : ConfigurationMatrix V :=
  ∑ i, a i • globalCreate (site i) α

 theorem finiteCreationField_opNorm_le {I : Type*} [Fintype I]
    (site : I → V) (a : I → ℝ) (α : Fin 3) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (finiteCreationField site a α)‖ ≤ ∑ i, |a i| := by
  simp only [finiteCreationField, map_sum, map_smul]
  calc
    _ ≤ ∑ i, ‖a i • Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (globalCreate (site i) α)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      simpa using mul_le_mul_of_nonneg_left
        (globalCreate_opNorm_le_one (site i) α) (abs_nonneg (a i))

/-- The actual outside field appearing in the transformed bond. -/
def outsideCreationField (K : V → V → ℝ) (u v r : V) (α : Fin 3) :
    ConfigurationMatrix V := finiteCreationField (fun w : Outside u v => (w : V))
      (fun w => K r w) α

 theorem outsideCreationField_left_bound (G : FourRegularData V)
    (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (u v : V)
    (huv : G.adjacency u v=1) (α : Fin 3) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (outsideCreationField (G.kernel g) u v u α)‖ ≤ (39/50 : ℝ)*g :=
  (finiteCreationField_opNorm_le _ _ α).trans
    (G.kernel_outside_mass_small g hg hmax u v huv)

 theorem outsideCreationField_right_bound (G : FourRegularData V)
    (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (u v : V)
    (huv : G.adjacency u v=1) (α : Fin 3) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (outsideCreationField (G.kernel g) u v v α)‖ ≤ (39/50 : ℝ)*g := by
  have hmass : (∑ w : Outside u v, |G.kernel g v w|) =
      ∑ w : Outside v u, |G.kernel g v w| := by
    let e : Outside u v ≃ Outside v u :=
      { toFun := fun w => ⟨w, w.property.2, w.property.1⟩
        invFun := fun w => ⟨w, w.property.2, w.property.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.sum_comp (fun w : Outside v u => |G.kernel g v w|)
  apply (finiteCreationField_opNorm_le _ _ α).trans
  rw [hmass]
  exact G.kernel_outside_mass_small g hg hmax v u (by rw [G.symmetric v u]; exact huv)

end BilayerDressed
