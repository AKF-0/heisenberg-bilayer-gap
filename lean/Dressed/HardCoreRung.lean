import Mathlib

/-!
# Concrete four-state rung creation matrices

Index zero is the singlet vacuum and the three successor indices are the
triplets. These are actual finite matrices, not abstract creation-operator
axioms. Relating this basis to the physical two-spin computational basis is a
separate explicit change-of-basis obligation.
-/

namespace BilayerDressed

abbrev RungMatrix := Matrix (Fin 4) (Fin 4) ℝ

def rungCreate (α : Fin 3) : RungMatrix := Matrix.single α.succ 0 1
def rungAnnihilate (α : Fin 3) : RungMatrix := Matrix.single 0 α.succ 1
def rungVacuumProjector : RungMatrix := Matrix.single 0 0 1
def rungTripletProjector (α : Fin 3) : RungMatrix := Matrix.single α.succ α.succ 1
def rungNumber : RungMatrix := ∑ α : Fin 3, rungTripletProjector α

theorem rung_creation_product_zero (α β : Fin 3) :
    rungCreate α * rungCreate β = 0 := by
  apply Matrix.single_mul_single_of_ne
  exact (Fin.succ_ne_zero _).symm

theorem rung_creation_commute (α β : Fin 3) :
    Commute (rungCreate α) (rungCreate β) := by
  show rungCreate α * rungCreate β = rungCreate β * rungCreate α
  rw [rung_creation_product_zero, rung_creation_product_zero]

theorem rung_create_annihilate (α β : Fin 3) :
    rungCreate α * rungAnnihilate β = Matrix.single α.succ β.succ 1 := by
  simp [rungCreate, rungAnnihilate]

theorem rung_annihilate_create (α β : Fin 3) :
    rungAnnihilate α * rungCreate β =
      if α = β then rungVacuumProjector else 0 := by
  by_cases h : α = β
  · subst β
    simp [rungAnnihilate, rungCreate, rungVacuumProjector]
  · have hs : α.succ ≠ β.succ := fun hh => h (Fin.succ_injective _ hh)
    rw [if_neg h]
    exact Matrix.single_mul_single_of_ne 1 0 α.succ β.succ hs 1

theorem rung_create_vacuum (α : Fin 3) :
    rungCreate α * rungVacuumProjector = rungCreate α := by
  simp [rungCreate, rungVacuumProjector]

theorem rung_vacuum_create (α : Fin 3) :
    rungVacuumProjector * rungCreate α = 0 := by
  apply Matrix.single_mul_single_of_ne
  exact (Fin.succ_ne_zero _).symm

theorem rung_create_transpose (α : Fin 3) :
    (rungCreate α).transpose = rungAnnihilate α := by
  simp [rungCreate, rungAnnihilate]

theorem rung_number_create (α : Fin 3) :
    rungNumber * rungCreate α = rungCreate α := by
  classical
  unfold rungNumber
  rw [Finset.sum_mul]
  have h (β : Fin 3) : rungTripletProjector β * rungCreate α =
      if β = α then rungCreate α else 0 := by
    by_cases heq : β = α
    · subst β
      simp [rungTripletProjector, rungCreate]
    · have hs : β.succ ≠ α.succ := fun hh => heq (Fin.succ_injective _ hh)
      rw [if_neg heq]
      exact Matrix.single_mul_single_of_ne 1 β.succ β.succ α.succ hs 1
  simp_rw [h]
  simp

theorem rung_create_number (α : Fin 3) :
    rungCreate α * rungNumber = 0 := by
  unfold rungNumber
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro β _
  apply Matrix.single_mul_single_of_ne
  exact (Fin.succ_ne_zero _).symm

end BilayerDressed
