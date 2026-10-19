import Dressed.QuarticRootCounting
import Dressed.ConcreteSeedGraphs
import Mathlib.Data.Finset.Sort

/-!
# Deterministic row-major enumeration of four-site torus supports

This uses the explicit finite product equivalence and sorted finite sets, not
choice of a support enumeration. It matches the row-major labels of the frozen
finite graph checker and can be passed to the generic canonical matching proof.
-/
namespace BilayerDressed.QuarticRowMajor
open BilayerGap QuarticRootCounting

/-- The checker labels (x,y) by y+(2m)x. -/
def index (n m : ℕ) : Torus.Vertex n m ≃ Fin ((2*n)*(2*m)) := finProdFinEquiv

@[simp] theorem index_val (n m : ℕ) (v : Torus.Vertex n m) :
    (index n m v).val = v.2.val + (2*m)*v.1.val := rfl

/-- The linear order is used locally, so no existing product-order instance is changed. -/
def vertexOrder (n m : ℕ) : LinearOrder (Torus.Vertex n m) :=
  LinearOrder.lift' (index n m) (index n m).injective

/-- Increasing deterministic enumeration, parameter-compatible with the
canonical three-matching regrouping theorem. -/
def enumeration (n m : ℕ) (s : Support (Torus.Vertex n m)) : Fin 4 ≃ s.val := by
  letI := vertexOrder n m
  exact (s.val.orderIsoOfFin s.property).toEquiv

def sites (n m : ℕ) (s : Support (Torus.Vertex n m)) : Fin 4 → Torus.Vertex n m :=
  fun i => (enumeration n m s i).val

theorem sites_injective (n m : ℕ) (s : Support (Torus.Vertex n m)) :
    Function.Injective (sites n m s) :=
  Subtype.val_injective.comp (enumeration n m s).injective

theorem sites_range (n m : ℕ) (s : Support (Torus.Vertex n m)) :
    Set.range (sites n m s) = (s.val : Set (Torus.Vertex n m)) := by
  ext v
  constructor
  · rintro ⟨i,rfl⟩
    exact (enumeration n m s i).property
  · intro hv
    obtain ⟨i,hi⟩ := (enumeration n m s).surjective ⟨v,hv⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem sites_increasing (n m : ℕ) (s : Support (Torus.Vertex n m)) :
    StrictMono (fun i => index n m (sites n m s i)) := by
  letI := vertexOrder n m
  intro i j hij
  exact @OrderEmbedding.strictMono (Fin 4) (Torus.Vertex n m) inferInstance
    (vertexOrder n m).toPreorder (s.val.orderEmbOfFin s.property) i j hij

end BilayerDressed.QuarticRowMajor
