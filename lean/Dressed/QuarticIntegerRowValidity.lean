import Dressed.QuarticRootedRowTable
import Mathlib.Data.List.Chain

/-! Linear list certificates imply the unchanged actual rooted-table hypotheses.
The proof uses the exact array length and literal lookup order; no powerset order
or assumption that a supplied array is already a bijection is introduced.
-/
namespace BilayerDressed.QuarticIntegerRowValidity
open QuarticRootedRowTable
set_option maxHeartbeats 800000

/-- Exact in-bounds array lookup is an element of the same witness list. -/
theorem row_mem_toList {R : ℕ} (raw : Array Row) (hsize : raw.size=R) (i : Fin R) :
    row raw i ∈ raw.toList := by
  have hi : i.val<raw.size := by omega
  simpa [row,Array.getD,hi] using (Array.getElem_mem_toList (xs:=raw) hi)

/-- One linear Boolean `all` check supplies validity of every actual finite row. -/
theorem valid_of_all {A R : ℕ} (raw : Array Row) (hsize : raw.size=R)
    (hvalid : raw.toList.all (fun r=>decide (Valid A r))=true) :
    ∀ i : Fin R,Valid A (row raw i) := by
  intro i
  have hh := List.all_eq_true.mp hvalid (row raw i) (row_mem_toList raw hsize i)
  exact of_decide_eq_true hh

/-- Only adjacent numeric codes are checked. Strict monotonicity of every pair
of finite indices follows mathematically, without a quadratic comparison check. -/
theorem strictMono_of_isChain {A R : ℕ} (raw : Array Row) (hsize : raw.size=R)
    (hcode : List.IsChain (fun r s=>code A r<code A s) raw.toList) :
    StrictMono (fun i : Fin R=>code A (row raw i)) := by
  cases R with
  | zero => exact fun i=>Fin.elim0 i
  | succ R =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hnext : i.val+1<raw.toList.length := by
      simp only [Array.length_toList,hsize]
      omega
    have hi : i.val<raw.size := by omega
    have hj : i.val+1<raw.size := by simpa only [Array.length_toList] using hnext
    have hh := hcode.getElem i.val hnext
    simpa [row,Array.getD,hi,hj] using hh

/-- Bundled interface for the frozen row-table bijection and physical sum APIs. -/
theorem hypotheses_of_linear_checks {A R : ℕ} (raw : Array Row) (hsize : raw.size=R)
    (hvalid : raw.toList.all (fun r=>decide (Valid A r))=true)
    (hcode : List.IsChain (fun r s=>code A r<code A s) raw.toList) :
    (∀ i : Fin R,Valid A (row raw i)) ∧
      StrictMono (fun i : Fin R=>code A (row raw i)) :=
  ⟨valid_of_all raw hsize hvalid,strictMono_of_isChain raw hsize hcode⟩

end BilayerDressed.QuarticIntegerRowValidity
