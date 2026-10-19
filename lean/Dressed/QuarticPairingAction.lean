import Dressed.QuarticPairingCombinatorics

/-! The actual permutation action on the three unordered four-label pairings. -/
namespace BilayerDressed.QuarticCanonical

def representative (m : Fin 3) : Equiv.Perm (Fin 4) :=
  if m=0 then Equiv.refl _ else if m=1 then Equiv.swap 1 2 else Equiv.swap 1 3

def action (σ : Equiv.Perm (Fin 4)) (m : Fin 3) : Fin 3 :=
  label (σ * representative m)

theorem pairing_action_table : ∀ σ : Equiv.Perm (Fin 4), ∀ m : Fin 3,
    (canonicalPairing m).image (Finset.image σ) = canonicalPairing (action σ m) := by
  decide +kernel

theorem action_bijective : ∀ σ : Equiv.Perm (Fin 4), Function.Bijective (action σ) := by
  decide +kernel

noncomputable def actionEquiv (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (action σ) (action_bijective σ)
end BilayerDressed.QuarticCanonical
