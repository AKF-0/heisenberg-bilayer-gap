import Dressed.ConcreteSeedGraphs

/-! Exact regrouping of physical forward bonds and the ordinary adjacency. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.SeedGraphs
open BilayerGap
variable {R : Type*} [AddCommGroup R] [Module ℝ R]

 theorem incidence_weighted_sum (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (f : Torus.Vertex n m → Torus.Vertex n m → R) :
    (∑ u,∑ v,(graph n m h).adjacency u v • f u v) =
      (∑ u,f u (Torus.xNext n m u))+(∑ u,f (Torus.xNext n m u) u)+
      (∑ u,f u (Torus.yNext n m u))+(∑ u,f (Torus.yNext n m u) u) := by
  simp_rw [graph_incidence n m h hi,add_smul]
  simp only [ite_smul,one_smul,zero_smul,Finset.sum_add_distrib]
  have hx : (∑ u,∑ v,if u=Torus.xNext n m v then f u v else 0) =
      ∑ v,f (Torus.xNext n m v) v := by
    rw [Finset.sum_comm]
    simp
  have hy : (∑ u,∑ v,if u=Torus.yNext n m v then f u v else 0) =
      ∑ v,f (Torus.yNext n m v) v := by
    rw [Finset.sum_comm]
    simp
  rw [hx,hy]
  simp

/-- A symmetric ordered bond sum is twice the actual forward-bond sum. -/
 theorem incidence_symmetric_sum (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (f : Torus.Vertex n m → Torus.Vertex n m → R)
    (hf : ∀ u v,f u v=f v u) :
    (∑ u,∑ v,(graph n m h).adjacency u v • f u v) =
      (2 : ℝ) • ((∑ u,f u (Torus.xNext n m u))+(∑ u,f u (Torus.yNext n m u))) := by
  rw [incidence_weighted_sum n m h hi]
  simp_rw [hf (Torus.xNext n m _) _,hf (Torus.yNext n m _) _]
  rw [show (2 : ℝ)=1+1 by norm_num,add_smul,one_smul]
  abel

end BilayerDressed.SeedGraphs
