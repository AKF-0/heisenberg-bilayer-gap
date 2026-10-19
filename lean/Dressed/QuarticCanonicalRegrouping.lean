import Dressed.QuarticMatchingNorm
import Dressed.QuarticPairingCombinatorics
import Mathlib.Tactic

/-! Actual canonical support/matching classification and finite coefficient
regrouping. No translation-freeness or numerical coefficient premise is used. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticCanonical
open QuarticMatching
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem pair_symm (u v : V) : pairCreate u v=pairCreate v u := by
  unfold pairCreate
  apply Finset.sum_congr rfl
  intro α _
  exact (global_creation_commute u v α α).eq

theorem pair_product_comm (u v r s : V) :
    pairCreate u v * pairCreate r s = pairCreate r s * pairCreate u v :=
  (pair_creation_commute u v r s).eq

/-- This is an exhaustive finite permutation proof over opaque actual operators,
not an expansion of the physical Hilbert space. -/
theorem matching_permutation (v : Fin 4 → V) (σ : Equiv.Perm (Fin 4)) :
    matchingOperator (fun i => v (σ i)) 0 = matchingOperator v (label σ) := by
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
    simp_all [matchingOperator, label, partner, pair_symm, pair_product_comm]
  all_goals rw [pair_symm (v 1) (v 0)]

abbrev Support (V : Type*) [DecidableEq V] := {s : Finset V // s.card=4}

variable (enum : ∀ S : Support V, Fin 4 ≃ ↥S.val)

def tuple (S : Support V) (i : Fin 4) : V := enum S i

theorem tuple_injective (S : Support V) : Function.Injective (tuple enum S) := by
  intro i j hij
  exact (enum S).injective (Subtype.ext hij)

def tupleSupport (v : Fin 4 → V) (hv : Function.Injective v) : Support V :=
  ⟨Finset.univ.image v, by rw [Finset.card_image_of_injective _ hv]; simp⟩

def intoSupport (v : Fin 4 → V) (hv : Function.Injective v) :
    Fin 4 ≃ ↥(tupleSupport v hv).val :=
  Equiv.ofBijective (fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hv (congrArg Subtype.val h), by
      intro x
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp x.property
      exact ⟨i,Subtype.ext he⟩⟩

def permutation (v : Fin 4 → V) (hv : Function.Injective v) : Equiv.Perm (Fin 4) :=
  (intoSupport v hv).trans (enum (tupleSupport v hv)).symm

theorem tuple_permutation (v : Fin 4 → V) (hv : Function.Injective v) (i : Fin 4) :
    tuple enum (tupleSupport v hv) (permutation enum v hv i)=v i := by
  simp [tuple, permutation, intoSupport]

def key (v : Fin 4 → V) (hv : Function.Injective v) : Support V × Fin 3 :=
  (tupleSupport v hv, label (permutation enum v hv))

def canonicalOperator (k : Support V × Fin 3) : ConfigurationMatrix V :=
  matchingOperator (tuple enum k.1) k.2

theorem actual_matching_canonical (v : Fin 4 → V) (hv : Function.Injective v) :
    matchingOperator v 0 = canonicalOperator enum (key enum v hv) := by
  have hh : (fun i => tuple enum (tupleSupport v hv) (permutation enum v hv i))=v :=
    funext (tuple_permutation enum v hv)
  simpa only [hh, canonicalOperator, key] using
    matching_permutation (tuple enum (tupleSupport v hv)) (permutation enum v hv)

def physicalPairing (v : Fin 4 → V) : Finset (Finset V) :=
  {{v 0,v 1},{v 2,v 3}}

def mapPairing (v : Fin 4 → V) (p : Finset (Finset (Fin 4))) : Finset (Finset V) :=
  p.image (Finset.image v)

theorem mapPairing_injective (v : Fin 4 → V) (hv : Function.Injective v) :
    Function.Injective (mapPairing v) :=
  Finset.image_injective (Finset.image_injective hv)

def canonicalSupportPairing (S : Support V) (m : Fin 3) : Finset (Finset V) :=
  mapPairing (tuple enum S) (canonicalPairing m)

theorem physicalPairing_eq_map (v : Fin 4 → V) (hv : Function.Injective v) :
    physicalPairing v = mapPairing (tuple enum (tupleSupport v hv))
      (pairing (permutation enum v hv)) := by
  simp [physicalPairing, mapPairing, pairing, tuple_permutation]

theorem label_eq_iff_pairing (v : Fin 4 → V) (hv : Function.Injective v) (m : Fin 3) :
    label (permutation enum v hv)=m ↔
      physicalPairing v=canonicalSupportPairing enum (tupleSupport v hv) m := by
  rw [classification_table, physicalPairing_eq_map enum v hv]
  exact (mapPairing_injective (tuple enum (tupleSupport v hv))
    (tuple_injective enum (tupleSupport v hv))).eq_iff.symm

theorem key_eq_iff (v : Fin 4 → V) (hv : Function.Injective v)
    (S : Support V) (m : Fin 3) :
    key enum v hv=(S,m) ↔ tupleSupport v hv=S ∧
      physicalPairing v=canonicalSupportPairing enum S m := by
  constructor
  · intro h
    have hs : tupleSupport v hv=S := congrArg Prod.fst h
    have hm : label (permutation enum v hv)=m := congrArg Prod.snd h
    refine ⟨hs,?_⟩
    simpa only [hs] using (label_eq_iff_pairing enum v hv m).mp hm
  · rintro ⟨hs,hp⟩
    apply Prod.ext
    · exact hs
    · apply (label_eq_iff_pairing enum v hv m).mpr
      simpa only [hs] using hp

section Sum
variable {T : Type*} [Fintype T]

def coefficient (v : T → Fin 4 → V) (hv : ∀t, Function.Injective (v t))
    (a : T → ℝ) (k : Support V × Fin 3) : ℝ :=
  ∑ t, if key enum (v t) (hv t)=k then a t else 0

/-- Coefficients are actual fibers of the explicit canonical classification. -/
theorem regroup (v : T → Fin 4 → V) (hv : ∀t, Function.Injective (v t))
    (a : T → ℝ) :
    (∑ t, a t • matchingOperator (v t) 0) =
      ∑ k : Support V × Fin 3, coefficient enum v hv a k • canonicalOperator enum k := by
  simp_rw [actual_matching_canonical enum _ (hv _)]
  calc
    _ = ∑ t, ∑ k : Support V × Fin 3,
        (if key enum (v t) (hv t)=k then a t else 0) • canonicalOperator enum k := by
      apply Finset.sum_congr rfl
      intro t _
      simp
    _ = ∑ k : Support V × Fin 3, ∑ t,
        (if key enum (v t) (hv t)=k then a t else 0) • canonicalOperator enum k :=
      Finset.sum_comm
    _ = _ := by simp only [coefficient, Finset.sum_smul]

/-- The exact three coefficients on each actual four-site support. -/
theorem regroup_by_support (v : T → Fin 4 → V) (hv : ∀t, Function.Injective (v t))
    (a : T → ℝ) :
    (∑ t, a t • matchingOperator (v t) 0) =
      ∑ S : Support V, ∑ m : Fin 3,
        coefficient enum v hv a (S,m) • matchingOperator (tuple enum S) m := by
  rw [regroup, Fintype.sum_prod_type]
  rfl
end Sum
end BilayerDressed.QuarticCanonical
