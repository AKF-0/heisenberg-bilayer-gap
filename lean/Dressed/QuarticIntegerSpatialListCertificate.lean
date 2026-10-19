import Dressed.QuarticIntegerSeedSymmetries
import Dressed.QuarticIntegerListCertificate

/-!
# Linear structural certificates for exact signed spatial reuse

Only small integer witnesses are evaluated for original table rows. A successful
bounded representative lookup, its accepted signed coefficient, and a complete
four-coordinate spatial/translation/orientation identity imply the unchanged
`Matches` relation. All bounds are checked explicitly. The three-list checker
rejects length mismatches, so no original row or matching can be dropped.
-/
namespace BilayerDressed.QuarticIntegerSpatialListCertificate
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticCoefficientFibers
open QuarticRootedRowTable QuarticIntegerListCertificate
open QuarticIntegerSpatialTransport QuarticIntegerSeedSymmetries
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

/-- A representative stores all four literal row-major coordinates and its exact label. -/
structure Rep where
  sites : Fin 4 → ℕ
  label : ℕ

/-- Untrusted natural-number fields; every range is checked before soundness is used. -/
structure Witness where
  representative : ℕ
  spatialCode : ℕ
  shift : ℕ
  orientation : ℕ

abbrev WitnessRow := Fin 3 → Witness

variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- Total computational decoding. Checked ranges exclude modular aliases. -/
def decode (i : ℕ) : Torus.Vertex n m :=
  (QuarticRowMajor.index n m).symm (Fin.ofNat (area n m) i)

def repTuple (rep : Rep) : Fin 4 → Torus.Vertex n m :=
  fun j => decode n m (rep.sites j)

/-- This hypothesis is supplied by the separately accepted representative tree.
It gives no permission to use an absent or out-of-range lookup entry. -/
def Accepted (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
    (repCount : ℕ) (repLookup : ℕ → Option Rep) : Prop :=
  ∀ i, i < repCount → ∀ rep, repLookup i = some rep →
    forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m)
      (repTuple n m rep) = dictionary.getD rep.label 0

variable {C : ℕ} [NeZero C]
variable (maps : Fin C → (Torus.Vertex n m ≃ Torus.Vertex n m))

/-- A failed lookup is false, never a default representative. Besides exact
labels, all four tuple coordinates are compared, including the root coordinate. -/
def WitnessValid (dictionarySize repCount : ℕ) (repLookup : ℕ → Option Rep)
    (s : Fin 4 → Torus.Vertex n m) (label : ℕ) (w : Witness) : Prop :=
  w.representative < repCount ∧ w.spatialCode < C ∧ w.shift < area n m ∧
  w.orientation < 8 ∧ label < dictionarySize ∧
  match repLookup w.representative with
  | none => False
  | some rep => rep.label = label ∧ (∀ j, rep.sites j < area n m) ∧
      ∀ j, repTuple n m rep j =
        orientations (fun k => maps (Fin.ofNat C w.spatialCode) (s k) + decode n m w.shift)
          (Fin.ofNat 8 w.orientation) j

instance (dictionarySize repCount : ℕ) (repLookup : ℕ → Option Rep)
    (s : Fin 4 → Torus.Vertex n m) (label : ℕ) (w : Witness) :
    Decidable (WitnessValid n m maps dictionarySize repCount repLookup s label w) := by
  unfold WitnessValid
  split <;> infer_instance

/-- No coefficient arithmetic occurs in this check. -/
def witnessCheck (dictionarySize repCount : ℕ) (repLookup : ℕ → Option Rep)
    (s : Fin 4 → Torus.Vertex n m) (label : ℕ) (w : Witness) : Bool :=
  decide (WitnessValid n m maps dictionarySize repCount repLookup s label w)

/-- Raw row validity supplies actual input injectivity for every matching column. -/
def rowCheck (dictionarySize repCount : ℕ) (repLookup : ℕ → Option Rep)
    (r labels : Row) (ws : WitnessRow) : Bool :=
  decide (Valid (area n m) r) &&
    (witnessCheck n m maps dictionarySize repCount repLookup (matching n m r 0) (labels 0) (ws 0) &&
     witnessCheck n m maps dictionarySize repCount repLookup (matching n m r 1) (labels 1) (ws 1) &&
     witnessCheck n m maps dictionarySize repCount repLookup (matching n m r 2) (labels 2) (ws 2))

/-- Linear lockstep traversal. Extra or missing rows, labels, or witnesses fail. -/
def checkRows (dictionarySize repCount : ℕ) (repLookup : ℕ → Option Rep) :
    List Row → List Row → List WitnessRow → Bool
  | [], [], [] => true
  | r::rs, labels::ls, ws::wss =>
      rowCheck n m maps dictionarySize repCount repLookup r labels ws &&
        checkRows dictionarySize repCount repLookup rs ls wss
  | _, _, _ => false

/-- The three fixed matching columns are actual permutations of a valid site tuple. -/
theorem matching_injective (r : Row) (hv : Valid (area n m) r) (a : Fin 3) :
    Function.Injective (matching n m r a) := by
  have hs := sites_injective n m r hv
  intro i j hij
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp_all [matching, hs.eq_iff, -sites_zero]

variable (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
variable (repCount : ℕ) (repLookup : ℕ → Option Rep)
variable (hrep : Accepted n m kd dictionary repCount repLookup)
variable (hmaps : ∀ c, PreservesForward (cachedKernel n m kd)
  (Torus.xNext n m) (Torus.yNext n m) (maps c))

include hrep hmaps

/-- A checked witness transports the complete signed coefficient vector. -/
theorem witnessCheck_sound (s : Fin 4 → Torus.Vertex n m) (hs : Function.Injective s)
    (label : ℕ) (w : Witness)
    (hw : witnessCheck n m maps dictionary.size repCount repLookup s label w = true) :
    forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m) s =
      dictionary.getD label 0 := by
  have hv : WitnessValid n m maps dictionary.size repCount repLookup s label w := of_decide_eq_true hw
  rcases hv with ⟨hi, hc, ht, ho, hl, hv⟩
  cases he : repLookup w.representative with
  | none => simp only [he] at hv
  | some rep =>
    simp only [he] at hv
    rcases hv with ⟨hlab, hsites, heq⟩
    have htransport := forward_eq_of_spatial_witness n m (cachedKernel n m kd)
      (maps (Fin.ofNat C w.spatialCode)) (hmaps _) s hs (decode n m w.shift)
      (Fin.ofNat 8 w.orientation) (repTuple n m rep)
      (cached_translation n m kd _) (funext heq)
    exact htransport.symm.trans (by simpa only [hlab] using hrep _ hi rep he)

/-- One generic theorem handles all three matching columns, with no concrete
operator or dictionary elaboration repeated at each original row. -/
theorem rowCheck_sound (r labels : Row) (ws : WitnessRow)
    (hw : rowCheck n m maps dictionary.size repCount repLookup r labels ws = true) :
    Matches n m kd dictionary r labels := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hw
  rcases hw with ⟨hr, ⟨h0,h1⟩,h2⟩
  intro a
  apply witnessCheck_sound n m maps kd dictionary repCount repLookup hrep hmaps
    (matching n m r a) (matching_injective n m r hr a) (labels a) (ws a)
  fin_cases a
  · exact h0
  · exact h1
  · exact h2

/-- Successful linear certification preserves all original rows in order. -/
theorem matches_of_checkRows (rows labels : List Row) (ws : List WitnessRow)
    (hw : checkRows n m maps dictionary.size repCount repLookup rows labels ws = true) :
    List.Forall₂ (Matches n m kd dictionary) rows labels := by
  induction rows generalizing labels ws with
  | nil =>
    cases labels <;> cases ws <;> simp_all [checkRows]
  | cons r rs ih =>
    cases labels with
    | nil => simp [checkRows] at hw
    | cons l ls =>
      cases ws with
      | nil => simp [checkRows] at hw
      | cons w wss =>
        simp only [checkRows, Bool.and_eq_true] at hw
        have hh := hw
        exact List.Forall₂.cons
          (rowCheck_sound n m maps kd dictionary repCount repLookup hrep hmaps r l w hh.1)
          (ih ls wss hh.2)

/-- Alternative structural certificate for a paired row/label stream. -/
theorem matches_of_forall₂ (pairs : List (Row × Row)) (ws : List WitnessRow)
    (hw : List.Forall₂ (fun p w =>
      rowCheck n m maps dictionary.size repCount repLookup p.1 p.2 w = true) pairs ws) :
    List.Forall₂ (Matches n m kd dictionary) (pairs.map Prod.fst) (pairs.map Prod.snd) := by
  induction hw with
  | nil => exact List.Forall₂.nil
  | @cons p w ps wss hp ht ih =>
    exact List.Forall₂.cons
      (rowCheck_sound n m maps kd dictionary repCount repLookup hrep hmaps p.1 p.2 w hp) ih

end BilayerDressed.QuarticIntegerSpatialListCertificate
