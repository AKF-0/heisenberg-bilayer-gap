import Dressed.QuarticRootCounting

/-! Computable rooted four-site enumeration without the ambient powerset.
A rooted support is obtained uniquely by inserting its root into a three-element
subset of the remaining sites. Thus the arithmetic domain has choose(A-1,3)
elements, rather than enumerating the2^A ambient finite-set type. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticRootedEnumeration
open QuarticRootCounting
set_option maxHeartbeats 500000
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coercion of this explicit finite set supplies its small computational Fintype. -/
abbrev Triples (r : V) := ↥((Finset.univ.erase r).powersetCard 3)

lemma triple_card (r : V) (t : Triples r) : t.val.card=3 :=
  (Finset.mem_powersetCard.mp t.property).2

lemma root_not_mem (r : V) (t : Triples r) : r∉t.val := by
  intro hr
  have hh := (Finset.mem_powersetCard.mp t.property).1 hr
  simpa using hh

/-- The actual four-site support, with its cardinality proved. -/
def support (r : V) (t : Triples r) : Support V :=
  ⟨insert r t.val,by rw [Finset.card_insert_of_notMem (root_not_mem r t),triple_card]⟩

@[simp] theorem root_mem_support (r : V) (t : Triples r) : r∈(support r t).val := by
  simp [support]

/-- Erasure and insertion give the exact rooted-support bijection. -/
def equivRooted (r : V) : Triples r ≃ {S : Support V // r∈S.val} where
  toFun t := ⟨support r t,root_mem_support r t⟩
  invFun S := ⟨S.val.val.erase r,Finset.mem_powersetCard.mpr ⟨by
    intro x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,Finset.mem_univ x⟩,by
    have hh := Finset.card_erase_add_one S.property
    have hc := S.val.property
    omega⟩⟩
  left_inv t := by
    apply Subtype.ext
    change (insert r t.val).erase r=t.val
    exact Finset.erase_insert (root_not_mem r t)
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    change insert r (S.val.val.erase r)=S.val.val
    exact Finset.insert_erase S.property

/-- The actual rooted sum is exactly the small three-subset sum. -/
theorem rootedMass_eq_sum (w : Support V→ℝ) (r : V) :
    rootedMass w r=∑ t : Triples r,w (support r t) := by
  classical
  calc
    rootedMass w r=(∑ S : {S : Support V // r∈S.val},w S.val) := by
      unfold rootedMass
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro S; simp) _
    _ = _ := ((equivRooted r).sum_comp (fun S=>w S.val)).symm

/-- This small computational domain has the expected binomial size. -/
theorem card_triples (r : V) : Fintype.card (Triples r)=(Fintype.card V-1).choose 3 := by
  rw [Fintype.card_coe,Finset.card_powersetCard]
  simp

end BilayerDressed.QuarticRootedEnumeration
