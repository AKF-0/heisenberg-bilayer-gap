import Dressed.QuarticRootedEnumeration
import Dressed.CubicQuarticCoefficientCount

/-!
# Explicit integer rows enumerate actual rooted four-site supports

The first R entries of an array are interpreted literally. Valid increasing
triples, strictly increasing numeric row codes, and the exact binomial row count
prove a bijection. No equality with a powersetCard enumeration order is assumed.
Computational site tuples use Fin.ofNat, so evaluating a witness never reduces
validity proof terms. Validity proves that the modular conversion changes nothing.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticRootedRowTable
open BilayerGap QuarticRootCounting
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

abbrev Row := Fin 3 → ℕ

/-- A valid root-zero row contains exactly three increasing positive indices. -/
def Valid (A : ℕ) (r : Row) : Prop :=
  0 < r 0 ∧ r 0 < r 1 ∧ r 1 < r 2 ∧ r 2 < A

instance validDecidable (A : ℕ) (r : Row) : Decidable (Valid A r) :=
  inferInstanceAs (Decidable (0 < r 0 ∧ r 0 < r 1 ∧ r 1 < r 2 ∧ r 2 < A))

/-- The checked numeric code is used only to establish distinct array rows. -/
def code (A : ℕ) (r : Row) : ℕ := (r 0 * A + r 1) * A + r 2

/-- The first R array entries, with the same total lookup convention as witnesses. -/
def row (raw : Array Row) {R : ℕ} (i : Fin R) : Row := raw.getD i.val 0

/-- A valid row cannot come from the zero default beyond the array length. -/
theorem row_index_lt_size {A R : ℕ} (raw : Array Row) (i : Fin R)
    (hv : Valid A (row raw i)) : i.val < raw.size := by
  by_contra hn
  have hz : row raw i=0 := by simp [row,Array.getD,hn]
  have hp := hv.1
  simp [hz] at hp

/-- Root zero followed by the three literal row entries. -/
def values (r : Row) : Fin 4 → ℕ := ![0,r 0,r 1,r 2]

theorem values_lt {A : ℕ} {r : Row} (hv : Valid A r) (i : Fin 4) : values r i < A := by
  rcases hv with ⟨ha,hab,hbc,hc⟩
  fin_cases i
  · change 0 < A; omega
  · change r 0 < A; omega
  · change r 1 < A; omega
  · change r 2 < A; exact hc

theorem values_strictMono {A : ℕ} {r : Row} (hv : Valid A r) : StrictMono (values r) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  rcases hv with ⟨ha,hab,hbc,hc⟩
  fin_cases i
  · simpa [values] using ha
  · simpa [values] using hab
  · simpa [values] using hbc

section Torus
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- The graph's exact row-major size. -/
abbrev area : ℕ := (2*n)*(2*m)

/-- A proof-free computational site tuple, including the root at index zero. -/
def sites (r : Row) : Fin 4 → Torus.Vertex n m :=
  fun i => (QuarticRowMajor.index n m).symm (Fin.ofNat (area n m) (values r i))

/-- Validity prevents any modular change in the raw indices. -/
theorem index_sites_val (r : Row) (hv : Valid (area n m) r) (i : Fin 4) :
    (QuarticRowMajor.index n m (sites n m r i)).val = values r i := by
  simp [sites,Fin.ofNat,Nat.mod_eq_of_lt (values_lt hv i)]

theorem sites_strictMono (r : Row) (hv : Valid (area n m) r) :
    StrictMono (fun i => QuarticRowMajor.index n m (sites n m r i)) := by
  intro i j hij
  change (QuarticRowMajor.index n m (sites n m r i)).val <
    (QuarticRowMajor.index n m (sites n m r j)).val
  rw [index_sites_val n m r hv,index_sites_val n m r hv]
  exact values_strictMono hv hij

theorem sites_injective (r : Row) (hv : Valid (area n m) r) :
    Function.Injective (sites n m r) := by
  intro i j hij
  exact (sites_strictMono n m r hv).injective (congrArg (QuarticRowMajor.index n m) hij)

@[simp] theorem sites_zero (r : Row) : sites n m r 0 = 0 := by
  apply (QuarticRowMajor.index n m).injective
  apply Fin.ext
  simp [sites,values,Fin.ofNat,QuarticRowMajor.index_val]

/-- The actual support, whose four-element cardinality follows from validity. -/
def support (r : Row) (hv : Valid (area n m) r) : Support (Torus.Vertex n m) :=
  QuarticCanonical.tupleSupport (sites n m r) (sites_injective n m r hv)

@[simp] theorem mem_support (r : Row) (hv : Valid (area n m) r) (v : Torus.Vertex n m) :
    v ∈ (support n m r hv).val ↔ ∃ i, sites n m r i=v := by
  simp [support,QuarticCanonical.tupleSupport]

@[simp] theorem zero_mem_support (r : Row) (hv : Valid (area n m) r) :
    (0 : Torus.Vertex n m) ∈ (support n m r hv).val := by
  rw [mem_support]
  exact ⟨0,sites_zero n m r⟩

/-- The actual sorted enumeration equals the literal computational site tuple. -/
theorem rowMajor_sites_eq (r : Row) (hv : Valid (area n m) r) :
    QuarticRowMajor.sites n m (support n m r hv) = sites n m r := by
  apply QuarticRowMajor.sites_eq_of_increasing
  · intro i
    exact (mem_support n m r hv _).mpr ⟨i,rfl⟩
  · exact sites_strictMono n m r hv

/-- Equal supports give equal increasing integer rows, not just equal unordered sets. -/
theorem row_eq_of_support_eq (r s : Row) (hr : Valid (area n m) r) (hs : Valid (area n m) s)
    (he : support n m r hr=support n m s hs) : r=s := by
  have ht : sites n m r=sites n m s := by
    rw [←rowMajor_sites_eq n m r hr,←rowMajor_sites_eq n m s hs,he]
  have hv (i : Fin 4) : values r i=values s i := by
    have hh := congrArg (fun v => (QuarticRowMajor.index n m v).val) (congrFun ht i)
    simpa only [index_sites_val n m r hr,index_sites_val n m s hs] using hh
  funext i
  fin_cases i
  · simpa [values] using hv 1
  · simpa [values] using hv 2
  · simpa [values] using hv 3

variable (raw : Array Row) (R : ℕ) (hvalid : ∀ i : Fin R, Valid (area n m) (row raw i))

/-- The support attached to the exact array row used by coefficient lookup. -/
def supportRow (i : Fin R) : Support (Torus.Vertex n m) :=
  support n m (row raw i) (hvalid i)

/-- A row viewed as an actual support containing the physical root. -/
def rootedSupportRow (i : Fin R) : {S : Support (Torus.Vertex n m) // (0 : Torus.Vertex n m) ∈ S.val} :=
  ⟨supportRow n m raw R hvalid i,zero_mem_support n m (row raw i) (hvalid i)⟩

theorem supportRow_injective
    (hcode : StrictMono (fun i : Fin R => code (area n m) (row raw i))) :
    Function.Injective (supportRow n m raw R hvalid) := by
  intro i j hij
  apply hcode.injective
  have hr := row_eq_of_support_eq n m (row raw i) (row raw j) (hvalid i) (hvalid j) hij
  exact congrArg (code (area n m)) hr

theorem rootedSupportRow_injective
    (hcode : StrictMono (fun i : Fin R => code (area n m) (row raw i))) :
    Function.Injective (rootedSupportRow n m raw R hvalid) := by
  intro i j hij
  exact supportRow_injective n m raw R hvalid hcode (congrArg Subtype.val hij)

/-- Exact target cardinality from insertion/erasure, not from a chosen order. -/
theorem card_rooted_supports :
    Fintype.card {S : Support (Torus.Vertex n m) // (0 : Torus.Vertex n m) ∈ S.val} =
      (area n m-1).choose 3 := by
  rw [←Fintype.card_congr (QuarticRootedEnumeration.equivRooted (0 : Torus.Vertex n m)),
    QuarticRootedEnumeration.card_triples]
  simp [area,Fintype.card_prod]

/-- Valid rows with distinct codes and the exact binomial count cover every
rooted support once, including supports whose coefficient happens to be zero. -/
def equivRooted
    (hcode : StrictMono (fun i : Fin R => code (area n m) (row raw i)))
    (hcard : R=(area n m-1).choose 3) :
    Fin R ≃ {S : Support (Torus.Vertex n m) // (0 : Torus.Vertex n m) ∈ S.val} :=
  Equiv.ofBijective (rootedSupportRow n m raw R hvalid)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨rootedSupportRow_injective n m raw R hvalid hcode,by
        simpa only [Fintype.card_fin] using hcard.trans (card_rooted_supports n m).symm⟩)

/-- Exact rooted sum in the concrete witness row order. -/
theorem rootedMass_eq_sum_rows
    (hcode : StrictMono (fun i : Fin R => code (area n m) (row raw i)))
    (hcard : R=(area n m-1).choose 3) (w : Support (Torus.Vertex n m) → ℝ) :
    rootedMass w (0 : Torus.Vertex n m) = ∑ i : Fin R,w (supportRow n m raw R hvalid i) := by
  calc
    _ = ∑ t : QuarticRootedEnumeration.Triples (0 : Torus.Vertex n m),
        w (QuarticRootedEnumeration.support 0 t) := QuarticRootedEnumeration.rootedMass_eq_sum w 0
    _ = ∑ S : {S : Support (Torus.Vertex n m) // (0 : Torus.Vertex n m) ∈ S.val},w S.val :=
      (QuarticRootedEnumeration.equivRooted (0 : Torus.Vertex n m)).sum_comp (fun S => w S.val)
    _ = _ := ((equivRooted n m raw R hvalid hcode hcard).sum_comp (fun S => w S.val)).symm

/-- Literal matching tuples in the same order as the integer witness columns. -/
def matchingSites (i : Fin R) (a : Fin 3) : Fin 4 → Torus.Vertex n m :=
  let s := sites n m (row raw i)
  (![![s 0,s 1,s 2,s 3],![s 0,s 2,s 1,s 3],![s 0,s 3,s 1,s 2]]) a

/-- Canonical matching columns are exactly the three displayed raw permutations. -/
theorem actual_matchingTuple_eq (i : Fin R) (a : Fin 3) :
    CubicQuarticCoefficientCount.matchingTuple n m (supportRow n m raw R hvalid i) a =
      matchingSites n m raw R i a := by
  have he : QuarticCanonical.tuple (QuarticRowMajor.enumeration n m)
      (supportRow n m raw R hvalid i)=sites n m (row raw i) :=
    rowMajor_sites_eq n m (row raw i) (hvalid i)
  unfold CubicQuarticCoefficientCount.matchingTuple QuarticActualCoefficients.matchingTuple matchingSites
  rw [he]
end Torus
end BilayerDressed.QuarticRootedRowTable
