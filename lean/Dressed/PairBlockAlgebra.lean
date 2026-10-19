import Dressed.PhysicalGramLowerBound
import Dressed.GlobalCreation

/-!
# Actual two-rung block algebra with the full exterior Hilbert space

Flattening nested matrices and the proved configuration equivalence give a
real algebra equivalence, not a formal substitution into a commutative ring.
The full exterior matrix algebra is not asserted to commute. Applications
may first map a genuinely commutative creation subalgebra into these blocks.
-/
noncomputable section
namespace BilayerDressed.PairBlock
open Matrix BilayerGap
open scoped BigOperators Kronecker
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Outside (u v : V) := PhysicalGram.Outside u v
abbrev ExteriorConfig (u v : V) := Configuration (Outside u v)
abbrev ExteriorMatrix (u v : V) := ConfigurationMatrix (Outside u v)
abbrev Blocks (u v : V) := Matrix LocalBond.PairIndex LocalBond.PairIndex (ExteriorMatrix u v)

/-- Exact flattening of two local factors and every exterior factor. -/
def assemble (u v : V) (huv : u ≠ v) :
    Blocks u v ≃ₐ[ℝ] ConfigurationMatrix V :=
  (Matrix.compAlgEquiv LocalBond.PairIndex (ExteriorConfig u v) ℝ ℝ).trans
    (Matrix.reindexAlgEquiv ℝ ℝ (PhysicalGram.pairConfigEquiv u v huv))

/-- Every entry has the expected local indices and restricted exterior configurations. -/
theorem assemble_apply (u v : V) (huv : u ≠ v) (A : Blocks u v)
    (s t : Configuration V) :
    assemble u v huv A s t = A (s u,s v) (t u,t v)
      (fun w : Outside u v => s w) (fun w : Outside u v => t w) := rfl

/-- Scalars become exterior identity matrices, not traces or dimension factors. -/
theorem assemble_map_local (u v : V) (huv : u ≠ v)
    (A : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ) :
    assemble u v huv (A.map (algebraMap ℝ (ExteriorMatrix u v))) =
      Torus.pairLift A u v := by
  ext s t
  rw [assemble_apply]
  have he : (fun w : Outside u v => s w) = (fun w : Outside u v => t w) ↔
      ∀ w, w ≠ u → w ≠ v → s w = t w := by
    constructor
    · intro h w hwu hwv
      exact congrFun h ⟨w,hwu,hwv⟩
    · intro h
      funext w
      exact h w w.property.1 w.property.2
  simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply,
    Algebra.algebraMap_self_apply, Torus.pairLift, he]
  split_ifs <;> rfl

/-- A left local matrix has precisely its actual one-site tensor lift. -/
theorem assemble_left (u v : V) (huv : u ≠ v) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    assemble u v huv ((A ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)).map
      (algebraMap ℝ (ExteriorMatrix u v))) = Torus.siteLift A u := by
  rw [assemble_map_local, Torus.pairLift_left _ huv]

/-- A right local matrix has precisely its actual one-site tensor lift. -/
theorem assemble_right (u v : V) (huv : u ≠ v) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    assemble u v huv (((1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ A).map
      (algebraMap ℝ (ExteriorMatrix u v))) = Torus.siteLift A v := by
  rw [assemble_map_local, Torus.pairLift_right _ huv]

/-- The left abstract local creation is identified with the real global creation. -/
theorem assemble_left_create (u v : V) (huv : u ≠ v) (α : Fin 3) :
    assemble u v huv (((LocalBond.create α : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ
      (1 : Matrix (Fin 4) (Fin 4) ℝ)).map (algebraMap ℝ (ExteriorMatrix u v))) =
      globalCreate u α := by
  rw [assemble_left]
  rfl

/-- The right abstract local creation is identified with the real global creation. -/
theorem assemble_right_create (u v : V) (huv : u ≠ v) (α : Fin 3) :
    assemble u v huv (((1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ
      (LocalBond.create α : Matrix (Fin 4) (Fin 4) ℝ)).map
        (algebraMap ℝ (ExteriorMatrix u v))) = globalCreate v α := by
  rw [assemble_right]
  rfl

omit [Fintype V] in
/-- Local equality and exterior equality away from w exactly mean global equality away from w. -/
theorem outside_site_condition (u v : V) (w : Outside u v) (s t : Configuration V) :
    ((s u,s v) = (t u,t v) ∧
      (∀ z : Outside u v, z ≠ w → s z = t z)) ↔
        (∀ z : V, z ≠ w.val → s z = t z) := by
  constructor
  · rintro ⟨hl,ho⟩ z hz
    by_cases hzu : z=u
    · subst z
      exact congrArg Prod.fst hl
    · by_cases hzv : z=v
      · subst z
        exact congrArg Prod.snd hl
      · exact ho ⟨z,hzu,hzv⟩ (fun he => hz (congrArg Subtype.val he))
  · intro h
    refine ⟨Prod.ext (h u w.property.1.symm) (h v w.property.2.symm), ?_⟩
    intro z hz
    exact h z (fun he => hz (Subtype.ext he))

/-- A genuine exterior site lift assembles to the corresponding full-space site lift. -/
theorem assemble_scalar_siteLift (u v : V) (huv : u ≠ v)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Outside u v) :
    assemble u v huv (Matrix.scalar LocalBond.PairIndex (Torus.siteLift A w)) =
      Torus.siteLift A w.val := by
  ext s t
  rw [assemble_apply]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hl : (s u,s v) = (t u,t v)
  · rw [if_pos hl]
    have he : (∀ z : Outside u v, z ≠ w → s z = t z) ↔
        ∀ z : V, z ≠ w.val → s z = t z := by
      simpa only [hl, true_and] using outside_site_condition u v w s t
    simp only [Torus.siteLift, he]
    split_ifs <;> rfl
  · rw [if_neg hl]
    have he : ¬(∀ z : V, z ≠ w.val → s z = t z) := by
      intro hh
      exact hl ((outside_site_condition u v w s t).mpr hh).1
    simp [Torus.siteLift, he]

/-- The coefficient-ring creation is the same physical creation on its exterior rung. -/
theorem assemble_outside_create (u v : V) (huv : u ≠ v)
    (w : Outside u v) (α : Fin 3) :
    assemble u v huv (Matrix.scalar LocalBond.PairIndex (globalCreate w α)) =
      globalCreate w.val α := by
  exact assemble_scalar_siteLift u v huv (rungCreate α) w

/-- The true all-singlet column, retaining its exterior operator action. -/
theorem assemble_vacuum_column (u v : V) (huv : u ≠ v) (A : Blocks u v)
    (s : Configuration V) :
    assemble u v huv A s (TripletNumber.vacuum : Configuration V) =
      A (s u,s v) (0,0) (fun w : Outside u v => s w)
        (TripletNumber.vacuum : ExteriorConfig u v) := rfl

end BilayerDressed.PairBlock
