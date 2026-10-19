import Mathlib

/-! Exact finite classification of the three unordered pairings of four labels. -/
namespace BilayerDressed.QuarticCanonical

def partner (σ : Equiv.Perm (Fin 4)) : Fin 4 :=
  if σ 0=0 then σ 1 else if σ 1=0 then σ 0 else if σ 2=0 then σ 3 else σ 2

def label (σ : Equiv.Perm (Fin 4)) : Fin 3 :=
  if partner σ=1 then 0 else if partner σ=2 then 1 else 2

def pairing (σ : Equiv.Perm (Fin 4)) : Finset (Finset (Fin 4)) :=
  {{σ 0,σ 1},{σ 2,σ 3}}

def canonicalPairing (m : Fin 3) : Finset (Finset (Fin 4)) :=
  (![{{0,1},{2,3}}, {{0,2},{1,3}}, {{0,3},{1,2}}]) m

theorem classification_table : ∀ σ : Equiv.Perm (Fin 4), ∀ m : Fin 3,
    label σ=m ↔ pairing σ=canonicalPairing m := by
  decide +kernel

end BilayerDressed.QuarticCanonical
