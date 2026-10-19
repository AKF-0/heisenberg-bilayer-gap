import Mathlib.Data.Option.Basic

/-! A balanced, exact lookup for already proved representative entries. No tree
ordering or completeness assertion is needed: every successful lookup returns
one of the entries carrying the same proved predicate. Concrete member checks
still verify bounds, successful lookup and the complete tuple/label witness. -/
namespace BilayerDressed.QuarticIntegerRepresentativeTree

inductive Tree (α : Type*) where
  | empty
  | leaf (key : ℕ) (value : α)
  | branch (cutoff : ℕ) (left right : Tree α)

def lookup {α : Type*} : Tree α → ℕ → Option α
  | .empty, _ => none
  | .leaf key value, i => if i=key then some value else none
  | .branch cutoff left right, i =>
      if i<cutoff then lookup left i else lookup right i

def All {α : Type*} (P : α → Prop) : Tree α → Prop
  | .empty => True
  | .leaf _ value => P value
  | .branch _ left right => All P left ∧ All P right

theorem all_empty {α : Type*} (P : α→Prop) : All P .empty := trivial

theorem all_leaf {α : Type*} {P : α→Prop} (key : ℕ) (value : α) (h : P value) :
    All P (.leaf key value) := h

theorem all_branch {α : Type*} {P : α→Prop} (cutoff : ℕ)
    (left right : Tree α) (hl : All P left) (hr : All P right) :
    All P (.branch cutoff left right) := ⟨hl,hr⟩

theorem property_of_lookup {α : Type*} {P : α→Prop} (t : Tree α)
    (h : All P t) (i : ℕ) (value : α) (hv : lookup t i=some value) : P value := by
  induction t with
  | empty => simp [lookup] at hv
  | leaf key v =>
      by_cases he : i=key
      · simp only [lookup,if_pos he,Option.some.injEq] at hv
        exact hv ▸ h
      · simp only [lookup,if_neg he] at hv
        cases hv
  | branch cutoff left right ihl ihr =>
      by_cases hi : i<cutoff
      · exact ihl h.1 (by simpa only [lookup,if_pos hi] using hv)
      · exact ihr h.2 (by simpa only [lookup,if_neg hi] using hv)

end BilayerDressed.QuarticIntegerRepresentativeTree
