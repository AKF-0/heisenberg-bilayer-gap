import Dressed.QuarticSexticBounds
import Mathlib.Data.Finset.Powerset

/-!
# Four-site rooted double counting without a stabilizer assumption

A rooted support means every four-site set containing the designated root,
not a representative of a translation orbit. Periodic supports with nontrivial
stabilizers are therefore counted correctly.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticRootCounting
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Support (V : Type*) [Fintype V] := {s : Finset V // s.card = 4}

/-- Every four-site support containing the root is included once. -/
def rootedMass (w : Support V → ℝ) (r : V) : ℝ :=
  ∑ s : Support V, if r ∈ s.val then w s else 0

/-- Each support has exactly four incident choices of root. -/
theorem sum_rootedMass (w : Support V → ℝ) :
    ∑ r : V, rootedMass w r = 4 * ∑ s : Support V, w s := by
  unfold rootedMass
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, s.property, nsmul_eq_mul, Nat.cast_ofNat]

/-- A site permutation induces a genuine bijection on four-site supports. -/
def supportEquiv (e : V ≃ V) : Support V ≃ Support V where
  toFun s := ⟨s.val.map e.toEmbedding, by simpa using s.property⟩
  invFun s := ⟨s.val.map e.symm.toEmbedding, by simpa using s.property⟩
  left_inv s := by apply Subtype.ext; ext x; simp
  right_inv s := by apply Subtype.ext; ext x; simp

@[simp] theorem mem_supportEquiv (e : V ≃ V) (s : Support V) (r : V) :
    e r ∈ (supportEquiv e s).val ↔ r ∈ s.val := by
  simp [supportEquiv]

/-- Rooted masses are transported by actual site bijections preserving weights. -/
theorem rootedMass_equiv (w : Support V → ℝ) (e : V ≃ V)
    (hw : ∀ s, w (supportEquiv e s) = w s) (r : V) :
    rootedMass w (e r) = rootedMass w r := by
  unfold rootedMass
  rw [← Equiv.sum_comp (supportEquiv e)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mem_supportEquiv, hw]

/-- Exact A/4 factor by double counting. No freeness of the site action or of
its induced support action is assumed. -/
theorem totalMass_eq_card_div_four_rooted (w : Support V → ℝ) (origin : V)
    (translate : V → V ≃ V) (hroot : ∀ r, translate r origin = r)
    (hw : ∀ r s, w (supportEquiv (translate r) s) = w s) :
    (∑ s : Support V, w s) = (Fintype.card V : ℝ) / 4 * rootedMass w origin := by
  have hc (r : V) : rootedMass w r = rootedMass w origin := by
    simpa only [hroot] using rootedMass_equiv w (translate r) (hw r) origin
  have hh := sum_rootedMass w
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  linarith

/-- Translation-invariant weights on a finite additive group. Periodic supports
with nontrivial stabilizers are included automatically. -/
theorem additive_totalMass_eq_card_div_four_rooted [AddGroup V]
    (w : Support V → ℝ)
    (hw : ∀ t s, w (supportEquiv (Equiv.addRight t) s) = w s) :
    (∑ s : Support V, w s) = (Fintype.card V : ℝ) / 4 * rootedMass w 0 :=
  totalMass_eq_card_div_four_rooted w 0 Equiv.addRight (by intro r; simp) hw

/-- The exact Gram weight of the three colored perfect matchings. -/
def matchingWeight (c : Fin 3 → ℝ) : ℝ :=
  6 * (∑ m, (c m)^2) + 3 * (∑ m, c m)^2

/-- Relabeling the three matchings changes no Gram weight. -/
theorem matchingWeight_equiv (c : Fin 3 → ℝ) (e : Fin 3 ≃ Fin 3) :
    matchingWeight (fun m => c (e m)) = matchingWeight c := by
  unfold matchingWeight
  rw [e.sum_comp (fun m => (c m)^2), e.sum_comp c]

/-- Coefficients may be permuted by translation, as happens when a translated
four-site set is sorted again. Rooted counting needs no invariant ordering. -/
theorem matching_total_eq_card_div_four_rooted [AddGroup V]
    (c : Support V → Fin 3 → ℝ)
    (hc : ∀ t s, ∃ e : Fin 3 ≃ Fin 3,
      ∀ m, c (supportEquiv (Equiv.addRight t) s) m = c s (e m)) :
    (∑ s : Support V, matchingWeight (c s)) =
      (Fintype.card V : ℝ) / 4 * rootedMass (fun s => matchingWeight (c s)) 0 := by
  apply additive_totalMass_eq_card_div_four_rooted
  intro t s
  obtain ⟨e,he⟩ := hc t s
  have hf : c (supportEquiv (Equiv.addRight t) s) = fun m => c s (e m) := funext he
  rw [hf, matchingWeight_equiv]

end BilayerDressed.QuarticRootCounting
