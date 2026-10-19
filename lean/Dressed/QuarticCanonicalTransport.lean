import Dressed.QuarticCanonicalRegrouping
import Dressed.QuarticPairingAction
import Dressed.QuarticRootCounting

/-! Actual change of support enumeration under a site equivalence. The induced
three-matching permutation is constructed, not assumed as covariance data. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticCanonical
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable (enum : ∀ S : Support V, Fin 4 ≃ ↥S.val)

/-- The actual subtype map induced by the site permutation. -/
def supportTransport (e : V ≃ V) (S : Support V) :
    ↥S.val ≃ ↥(QuarticRootCounting.supportEquiv e S).val where
  toFun x := ⟨e x, by simp [QuarticRootCounting.supportEquiv, x.property]⟩
  invFun y := ⟨e.symm y, by
    have h := y.property
    simpa [QuarticRootCounting.supportEquiv] using h⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

def transition (e : V ≃ V) (S : Support V) : Equiv.Perm (Fin 4) :=
  ((enum S).trans (supportTransport e S)).trans
    (enum (QuarticRootCounting.supportEquiv e S)).symm

theorem tuple_transition (e : V ≃ V) (S : Support V) (i : Fin 4) :
    tuple enum (QuarticRootCounting.supportEquiv e S) (transition enum e S i) =
      e (tuple enum S i) := by
  simp [tuple, transition, supportTransport]

theorem mapPairing_comp (v : Fin 4 → V) (σ : Equiv.Perm (Fin 4))
    (p : Finset (Finset (Fin 4))) :
    mapPairing (fun i => v (σ i)) p = mapPairing v (p.image (Finset.image σ)) := by
  simp [mapPairing, Finset.image_image, Function.comp_def]

/-- This is the required matching permutation, with its bijection proved. -/
def matchingEquiv (e : V ≃ V) (S : Support V) : Equiv.Perm (Fin 3) :=
  actionEquiv (transition enum e S)

theorem canonicalSupportPairing_transport (e : V ≃ V) (S : Support V) (m : Fin 3) :
    mapPairing (fun i => e (tuple enum S i)) (canonicalPairing m) =
      canonicalSupportPairing enum (QuarticRootCounting.supportEquiv e S)
        (matchingEquiv enum e S m) := by
  have h : (fun i => e (tuple enum S i)) =
      (fun i => tuple enum (QuarticRootCounting.supportEquiv e S) (transition enum e S i)) :=
    funext (fun i => (tuple_transition enum e S i).symm)
  rw [h, mapPairing_comp, pairing_action_table]
  rfl

theorem exists_matching_transport (e : V ≃ V) (S : Support V) :
    ∃ π : Equiv.Perm (Fin 3), ∀ m : Fin 3,
      mapPairing (fun i => e (tuple enum S i)) (canonicalPairing m) =
        canonicalSupportPairing enum (QuarticRootCounting.supportEquiv e S) (π m) :=
  ⟨matchingEquiv enum e S, canonicalSupportPairing_transport enum e S⟩

end BilayerDressed.QuarticCanonical
