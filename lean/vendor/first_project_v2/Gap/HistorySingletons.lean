import Gap.HistoryPolynomial
import Gap.TorusLifts

/-!
# Exactly one event is exactly one labelled bond

This finite bijection removes the event-count filter in the linear coefficient
of the actual one-step polynomial. No generator identity is assumed.
-/
noncomputable section
namespace BilayerGap.History
open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {S B : Type*} [Fintype S] [DecidableEq S] [Fintype B]

/-- A single labelled event, with all other bonds empty. -/
def singleEvent (s : S) (label : B) : S → Option B :=
  Function.update (fun _ => none) s (some label)

@[simp] theorem singleEvent_at (s : S) (label : B) :
    singleEvent s label s = some label := by simp [singleEvent]

@[simp] theorem singleEvent_other (s t : S) (label : B) (h : t ≠ s) :
    singleEvent s label t = none := by simp [singleEvent, h]

@[simp] theorem eventCount_singleEvent (s : S) (label : B) :
    eventCount (singleEvent s label) = 1 := by
  classical
  unfold eventCount
  rw [Finset.sum_eq_single s]
  · simp [occupation]
  · intro t _ ht
    simp [singleEvent_other s t label ht, occupation]
  · simp

/-- The event count is the cardinality of its occupied support. -/
theorem eventCount_eq_support_card (x : S → Option B) :
    eventCount x = (Finset.univ.filter (fun s => x s ≠ none)).card := by
  classical
  rw [Finset.card_filter]
  unfold eventCount
  apply Finset.sum_congr rfl
  intro s _
  cases x s <;> simp [occupation]

/-- Every one-event configuration has a site and its unique nonempty label. -/
theorem eventCount_one_exists (x : S → Option B) (hx : eventCount x = 1) :
    ∃ s label, x = singleEvent s label := by
  classical
  rw [eventCount_eq_support_card, Finset.card_eq_one] at hx
  obtain ⟨s, hs⟩ := hx
  have hxs : x s ≠ none := by
    have hm : s ∈ Finset.univ.filter (fun t => x t ≠ none) := by rw [hs]; simp
    simpa using hm
  cases he : x s with
  | none => exact (hxs he).elim
  | some label =>
    refine ⟨s, label, ?_⟩
    funext t
    by_cases ht : t = s
    · subst t; simpa using he
    · have hn : x t = none := by
        by_contra hh
        have hm : t ∈ Finset.univ.filter (fun t => x t ≠ none) := by simp [hh]
        rw [hs] at hm
        exact ht (by simpa using hm)
      simp [singleEvent_other s t label ht, hn]

/-- The site and label are recovered uniquely from the single-event function. -/
theorem singleEvent_injective :
    Function.Injective (fun p : S × B => singleEvent p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨s,l⟩
  rcases q with ⟨t,m⟩
  have hst : s = t := by
    by_contra hne
    have h := congrFun hpq s
    simpa [singleEvent_other t s m hne] using h
  subst t
  have hlm : l = m := by
    have h := congrFun hpq s
    simpa using h
  simp [hlm]

/-- The exact finite index equivalence underlying the first-order generator. -/
def oneEventEquiv : (S × B) ≃ {x : S → Option B // eventCount x = 1} :=
  Equiv.ofBijective (fun p => ⟨singleEvent p.1 p.2, eventCount_singleEvent p.1 p.2⟩)
    ⟨by
      intro p q h
      exact singleEvent_injective (congrArg Subtype.val h), by
      intro x
      obtain ⟨s,l,h⟩ := eventCount_one_exists x.val x.property
      refine ⟨(s,l), ?_⟩
      apply Subtype.ext
      exact h.symm⟩

/-- A filtered sum over all histories reduces exactly to a site-and-label sum. -/
theorem sum_one_event (f : (S → Option B) → ℝ) :
    (∑ x : S → Option B, if eventCount x = 1 then f x else 0) =
      ∑ s : S, ∑ label : B, f (singleEvent s label) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun x : S → Option B => eventCount x = 1) _ (by simp) f]
  rw [← Equiv.sum_comp (oneEventEquiv (S := S) (B := B)) (fun x => f x.val)]
  rw [Fintype.sum_prod_type]
  rfl

/-- The linear interaction coefficient is the sum of one-event insertions. -/
theorem oneEventGenerator_eq_single_events {V : Type*} [Fintype V] [DecidableEq V]
    (next : Equiv.Perm S) (G : B → Matrix V V ℝ) (a b : S → V) :
    oneEventGenerator next G a b =
      ∑ s : S, ∑ label : B,
        ∏ t : S, insertionVertex G (singleEvent s label t)
          (singleEvent s label (next t)) (a t) (b t) := by
  exact sum_one_event _

/-- A single event inserts the same generator at its two distinct endpoints.
The endpoints are `s` and `next.symm s`, because a vertex reads its outgoing
bond `x t` and the incoming index `x (next t)`. -/
theorem single_event_product_eq_pairLift {V : Type*} [Fintype V] [DecidableEq V]
    (next : Equiv.Perm S) (hnext : ∀ s, next s ≠ s)
    (G : B → Matrix V V ℝ) (s : S) (label : B) (a b : S → V) :
    (∏ t : S, insertionVertex G (singleEvent s label t)
        (singleEvent s label (next t)) (a t) (b t)) =
      Torus.pairLift (Matrix.kronecker (G label) (G label)) s (next.symm s) a b := by
  classical
  let f : S → ℝ := fun t => insertionVertex G (singleEvent s label t)
    (singleEvent s label (next t)) (a t) (b t)
  have hp : next.symm s ≠ s := by
    intro h
    have he : s = next s := by simpa using congrArg next h
    exact hnext s he.symm
  have hfs : f s = G label (a s) (b s) := by
    simp [f, singleEvent_other s (next s) label (hnext s), insertionVertex]
  have hfp : f (next.symm s) = G label (a (next.symm s)) (b (next.symm s)) := by
    simp [f, singleEvent_other s (next.symm s) label hp, insertionVertex]
  have hfo (t : S) (hts : t ≠ s) (htp : t ≠ next.symm s) :
      f t = if a t = b t then 1 else 0 := by
    have hnt : next t ≠ s := by
      intro h
      apply htp
      simpa using congrArg next.symm h
    simp [f, singleEvent_other s t label hts,
      singleEvent_other s (next t) label hnt, insertionVertex, Matrix.one_apply]
  change (∏ t, f t) = _
  rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ s)]
  rw [← Finset.prod_erase_mul (Finset.univ.erase s) f (a := next.symm s) (by simp [hp])]
  rw [hfs, hfp, Torus.pairLift_eq_delta_product]
  have hrest : (∏ t ∈ (Finset.univ.erase s).erase (next.symm s), f t) =
      ∏ t ∈ (Finset.univ.erase s).erase (next.symm s),
        (if a t = b t then 1 else 0 : ℝ) := by
    apply Finset.prod_congr rfl
    intro t ht
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ht
    exact hfo t ht.2 ht.1
  rw [hrest]
  change (_ * G label (a (next.symm s)) (b (next.symm s))) * G label (a s) (b s) =
    _ * (G label (a s) (b s) * G label (a (next.symm s)) (b (next.symm s)))
  ring

/-- The derived one-event generator is exactly the usual sum of two-site
Kronecker insertions. Fixed points are explicitly excluded rather than silently
interpreting a length-one cycle as a two-site bond. -/
theorem oneEventGenerator_eq_pair_sum {V : Type*} [Fintype V] [DecidableEq V]
    (next : Equiv.Perm S) (hnext : ∀ s, next s ≠ s)
    (G : B → Matrix V V ℝ) :
    oneEventGenerator next G =
      ∑ s : S, ∑ label : B,
        Torus.pairLift (Matrix.kronecker (G label) (G label)) s (next.symm s) := by
  ext a b
  simp only [Matrix.sum_apply, oneEventGenerator_eq_single_events]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro label _
  exact single_event_product_eq_pairLift next hnext G s label a b

/-- The on-site coefficient is exactly the sum of genuine one-site lifts. -/
theorem onSiteGenerator_eq_site_sum {V : Type*} [Fintype V] [DecidableEq V]
    (h : Matrix V V ℝ) :
    onSiteGenerator (S := S) h = ∑ s : S, Torus.siteLift h s := by
  ext a b
  simp only [onSiteGenerator, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [Torus.siteLift_eq_delta_product]
  simp only [Matrix.one_apply]

/-- Equivalently, the interaction sums positive-neighbor bonds, with each
successor edge indexed once. Endpoint reversal is proved by tensor symmetry. -/
theorem oneEventGenerator_eq_neighbor_sum {V : Type*} [Fintype V] [DecidableEq V]
    (next : Equiv.Perm S) (hnext : ∀ s, next s ≠ s)
    (G : B → Matrix V V ℝ) :
    oneEventGenerator next G =
      ∑ s : S, ∑ label : B,
        Torus.siteLift (G label) s * Torus.siteLift (G label) (next s) := by
  rw [oneEventGenerator_eq_pair_sum next hnext]
  rw [← Equiv.sum_comp next (fun s => ∑ label : B,
    Torus.pairLift (Matrix.kronecker (G label) (G label)) s (next.symm s))]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro label _
  rw [next.symm_apply_apply]
  exact (Torus.pairLift_tensor_swap (G label) (next s) s).trans
    (Torus.siteLift_mul_distinct (G label) (G label) (hnext s).symm).symm

end BilayerGap.History
