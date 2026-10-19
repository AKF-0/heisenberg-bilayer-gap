import Dressed.QuarticPhysicalMean
import Dressed.QuarticCanonicalTransport

/-! Covariance-weighted canonical quartic transport and rooted A/4 counting.
The support enumeration can change under translation. The actual induced
bijection of the three matchings transports both the signed coefficient and its
covariance weight, so no order-invariance assumption is introduced.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticPhysicalMean
open QuarticCanonical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Product of the two covariance entries selected by a matching. -/
def matchingProduct (L : V→V→ℝ) (v : Fin 4→V) (m : Fin 3) : ℝ :=
  (![L (v 0) (v 1)*L (v 2) (v 3),
     L (v 0) (v 2)*L (v 1) (v 3),
     L (v 0) (v 3)*L (v 1) (v 2)]) m

/-- A finite permutation proof uses only the actual symmetry of the covariance. -/
theorem matchingProduct_permutation_zero (L : V→V→ℝ)
    (hL : ∀ u v,L u v=L v u) (v : Fin 4→V) (σ : Equiv.Perm (Fin 4)) :
    matchingProduct L (fun i=>v (σ i)) 0 = matchingProduct L v (label σ) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h03 : σ 0 ≠ σ 3 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h13 : σ 1 ≠ σ 3 := σ.injective.ne (by decide)
  have h23 : σ 2 ≠ σ 3 := σ.injective.ne (by decide)
  generalize h0 : σ 0 = a at *
  generalize h1 : σ 1 = b at *
  generalize h2 : σ 2 = c at *
  generalize h3 : σ 3 = d at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first | contradiction | skip
  all_goals simp_all [matchingProduct,label,partner,hL,mul_comm]
  all_goals exact Or.inl (hL (v 1) (v 0))

theorem matchingProduct_representative (L : V→V→ℝ)
    (hL : ∀ u v,L u v=L v u) (v : Fin 4→V) (m : Fin 3) :
    matchingProduct L (fun i=>v (representative m i)) 0=matchingProduct L v m := by
  fin_cases m <;> simp [matchingProduct,representative,Equiv.swap_apply_def,hL]

/-- Every matching is transported by the proved three-label permutation. -/
theorem matchingProduct_permutation (L : V→V→ℝ)
    (hL : ∀ u v,L u v=L v u) (v : Fin 4→V)
    (σ : Equiv.Perm (Fin 4)) (m : Fin 3) :
    matchingProduct L (fun i=>v (σ i)) m=
      matchingProduct L v (actionEquiv σ m) := by
  rw [←matchingProduct_representative L hL (fun i=>v (σ i)) m]
  change matchingProduct L (fun i=>v ((σ*representative m) i)) 0=
    matchingProduct L v (label (σ*representative m))
  exact matchingProduct_permutation_zero L hL v (σ*representative m)

/-- 9/3/3 is six copies of the chosen pairing plus three of all pairings. -/
theorem matchingWeight_eq (L : V→V→ℝ) (hL : ∀ u v,L u v=L v u)
    (v : Fin 4→V) (m : Fin 3) :
    matchingWeight L v m=6*matchingProduct L v m+3*∑ j,matchingProduct L v j := by
  fin_cases m <;> simp [matchingWeight,pairedSites,matchingProduct,Fin.sum_univ_succ,hL] <;> ring

theorem matchingWeight_permutation (L : V→V→ℝ) (hL : ∀ u v,L u v=L v u)
    (v : Fin 4→V) (σ : Equiv.Perm (Fin 4)) (m : Fin 3) :
    matchingWeight L (fun i=>v (σ i)) m=matchingWeight L v (actionEquiv σ m) := by
  rw [matchingWeight_eq L hL,matchingWeight_eq L hL]
  simp_rw [matchingProduct_permutation L hL]
  rw [Equiv.sum_comp (actionEquiv σ)]

theorem matchingWeight_site_equiv (L : V→V→ℝ) (e : V≃V)
    (hL : ∀ u v,L (e u) (e v)=L u v) (v : Fin 4→V) (m : Fin 3) :
    matchingWeight L (fun i=>e (v i)) m=matchingWeight L v m := by
  fin_cases m <;> simp [matchingWeight,pairedSites,hL]

variable (enum : ∀ S : Support V,Fin 4≃↥S.val)

/-- Joint transport uses the actual transition of support enumerations. -/
theorem canonical_matchingWeight_transport (L : V→V→ℝ)
    (hLs : ∀ u v,L u v=L v u) (e : V≃V)
    (hLe : ∀ u v,L (e u) (e v)=L u v) (S : Support V) (m : Fin 3) :
    matchingWeight L (tuple enum (QuarticRootCounting.supportEquiv e S))
      (matchingEquiv enum e S m)=matchingWeight L (tuple enum S) m := by
  rw [matchingEquiv,←matchingWeight_permutation L hLs]
  have hh : (fun i=>tuple enum (QuarticRootCounting.supportEquiv e S)
      (transition enum e S i))=(fun i=>e (tuple enum S i)) :=
    funext (tuple_transition enum e S)
  rw [hh]
  exact matchingWeight_site_equiv L e hLe (tuple enum S) m

/-- The signed canonical fiber is combined before the absolute value. -/
def canonicalMeanWeight (L : V→V→ℝ) (c : Support V→Fin 3→ℝ) (S : Support V) : ℝ :=
  ∑ m,|c S m| * matchingWeight L (tuple enum S) m

theorem canonicalMeanWeight_transport (L : V→V→ℝ)
    (hLs : ∀ u v,L u v=L v u) (c : Support V→Fin 3→ℝ) (e : V≃V)
    (hLe : ∀ u v,L (e u) (e v)=L u v)
    (hc : ∀ S m,c (QuarticRootCounting.supportEquiv e S) (matchingEquiv enum e S m)=c S m)
    (S : Support V) :
    canonicalMeanWeight enum L c (QuarticRootCounting.supportEquiv e S)=
      canonicalMeanWeight enum L c S := by
  unfold canonicalMeanWeight
  rw [←Equiv.sum_comp (matchingEquiv enum e S)]
  apply Finset.sum_congr rfl
  intro m _
  rw [hc,canonical_matchingWeight_transport enum L hLs e hLe]

/-- Rooted A/4 counting is valid even for supports with translation stabilizers. -/
theorem canonicalMeanWeight_total_rooted [AddGroup V] (L : V→V→ℝ)
    (hLs : ∀ u v,L u v=L v u) (c : Support V→Fin 3→ℝ)
    (hLe : ∀ t u v,L (u+t) (v+t)=L u v)
    (hc : ∀ t S m,c (QuarticRootCounting.supportEquiv (Equiv.addRight t) S)
      (matchingEquiv enum (Equiv.addRight t) S m)=c S m) :
    (∑ S,canonicalMeanWeight enum L c S)=
      (Fintype.card V:ℝ)/4 *
        QuarticRootCounting.rootedMass (canonicalMeanWeight enum L c) 0 := by
  apply QuarticRootCounting.additive_totalMass_eq_card_div_four_rooted
  intro t S
  exact canonicalMeanWeight_transport enum L hLs c (Equiv.addRight t) (hLe t) (hc t) S

end BilayerDressed.QuarticPhysicalMean
