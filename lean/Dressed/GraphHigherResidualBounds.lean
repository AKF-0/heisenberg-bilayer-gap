import Dressed.ExternalCreationField
import Dressed.QuarticSexticBounds

/-! The higher residual norm bounds with every coefficient premise discharged
by the explicit physical kernel and actual edge condition. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace FourRegularData
variable (G : FourRegularData V)

/-- Actual quartic edge operator for the explicit kernel. -/
def quarticEdge (g : ℝ) (u v : V) : ConfigurationMatrix V :=
  QuarticSextic.literalR4 u v (outsideCreationField (G.kernel g) u v u)
    (outsideCreationField (G.kernel g) u v v) (G.kernel g u v)

/-- Actual sextic edge operator; no high-order term has been discarded. -/
def sexticEdge (g : ℝ) (u v : V) : ConfigurationMatrix V :=
  QuarticSextic.literalR6 u v (outsideCreationField (G.kernel g) u v u)
    (outsideCreationField (G.kernel g) u v v)

 theorem quarticEdge_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (u v : V)
    (huv : G.adjacency u v=1) :
    QuarticSextic.hnorm ((g/2) • G.quarticEdge g u v) ≤ (9/2 : ℝ)*g^3 :=
  QuarticSextic.literalR4_scaled_norm_le u v _ _ g _ ((39/50 : ℝ)*g)
    hg hmax (by positivity) le_rfl (G.kernel_entry_bound_small g hg hmax u v)
    (outsideCreationField_left_bound G g hg hmax u v huv)
    (outsideCreationField_right_bound G g hg hmax u v huv)

 theorem sexticEdge_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (u v : V)
    (huv : G.adjacency u v=1) :
    QuarticSextic.hnorm ((g/2) • G.sexticEdge g u v) ≤ 2*g^5 :=
  QuarticSextic.literalR6_scaled_norm_le u v _ _ g ((39/50 : ℝ)*g)
    hg (by positivity) le_rfl
    (outsideCreationField_left_bound G g hg hmax u v huv)
    (outsideCreationField_right_bound G g hg hmax u v huv)

/-- Exactly the two forward-direction quartic sums of the concrete graph. -/
def quarticGraph (g : ℝ) (ex ey : V → V) : ConfigurationMatrix V :=
  (g/2) • ((∑ u,G.quarticEdge g u (ex u))+(∑ u,G.quarticEdge g u (ey u)))

def sexticGraph (g : ℝ) (ex ey : V → V) : ConfigurationMatrix V :=
  (g/2) • ((∑ u,G.sexticEdge g u (ex u))+(∑ u,G.sexticEdge g u (ey u)))

 theorem quarticGraph_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (ex ey : V → V) (hx : ∀ u,G.adjacency u (ex u)=1)
    (hy : ∀ u,G.adjacency u (ey u)=1) :
    QuarticSextic.hnorm (G.quarticGraph g ex ey) ≤
      9*(Fintype.card V : ℝ)*g^3 := by
  rw [quarticGraph,smul_add,Finset.smul_sum,Finset.smul_sum]
  apply (QuarticSextic.hnorm_add_le _ _).trans
  apply (add_le_add (QuarticSextic.hnorm_sum_le _) (QuarticSextic.hnorm_sum_le _)).trans
  have hhx := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset V)) =>
    G.quarticEdge_bound g hg hmax u (ex u) (hx u))
  have hhy := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset V)) =>
    G.quarticEdge_bound g hg hmax u (ey u) (hy u))
  have hh := add_le_add hhx hhy
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    hh.trans_eq (by simp; ring)

 theorem sexticGraph_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (ex ey : V → V) (hx : ∀ u,G.adjacency u (ex u)=1)
    (hy : ∀ u,G.adjacency u (ey u)=1) :
    QuarticSextic.hnorm (G.sexticGraph g ex ey) ≤
      4*(Fintype.card V : ℝ)*g^5 := by
  rw [sexticGraph,smul_add,Finset.smul_sum,Finset.smul_sum]
  apply (QuarticSextic.hnorm_add_le _ _).trans
  apply (add_le_add (QuarticSextic.hnorm_sum_le _) (QuarticSextic.hnorm_sum_le _)).trans
  have hhx := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset V)) =>
    G.sexticEdge_bound g hg hmax u (ex u) (hx u))
  have hhy := Finset.sum_le_sum (fun u (_ : u∈(Finset.univ : Finset V)) =>
    G.sexticEdge_bound g hg hmax u (ey u) (hy u))
  have hh := add_le_add hhx hhy
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    hh.trans_eq (by simp; ring)

end FourRegularData
end BilayerDressed
