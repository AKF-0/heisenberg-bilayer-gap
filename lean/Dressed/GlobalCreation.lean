import Dressed.HardCoreRung
import Gap.TorusLifts

/-!
# Concrete commuting hard-core creations on the full finite configuration space

All creations are actual tensor-identity lifts of the four-state rung matrices.
The resulting pair kernel sum is proved nilpotent, not assumed to exponentiate.
-/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed
open BilayerGap.Torus
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Configuration (V : Type*) := V → Fin 4
abbrev ConfigurationMatrix (V : Type*) := Matrix (Configuration V) (Configuration V) ℝ

def globalCreate (v : V) (α : Fin 3) : ConfigurationMatrix V := siteLift (rungCreate α) v

/-- Different colors cannot both occupy one hard-core rung. -/
theorem global_creation_same_site_zero (v : V) (α β : Fin 3) :
    globalCreate v α * globalCreate v β = 0 := by
  ext s t
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r v=0
  · have hb : (0 : Fin 4) ≠ β.succ := (Fin.succ_ne_zero _).symm
    simp [globalCreate, siteLift, rungCreate, Matrix.single, hr, hb]
  · simp [globalCreate, siteLift, rungCreate, Matrix.single, hr, Ne.symm hr]

/-- Swapping both endpoints and tensor factors leaves a concrete edge lift unchanged. -/
theorem pairLift_swap_factors (A B : Matrix (Fin 4) (Fin 4) ℝ) (u v : V) :
    pairLift (A ⊗ₖ B) u v = pairLift (B ⊗ₖ A) v u := by
  ext s t
  have he : (∀ w, w ≠ u → w ≠ v → s w=t w) ↔
      (∀ w, w ≠ v → w ≠ u → s w=t w) := by tauto
  simp only [pairLift, he, Matrix.kronecker_apply, mul_comm]

/-- All global creation operators commute, including coincident sites. -/
theorem global_creation_commute (u v : V) (α β : Fin 3) :
    Commute (globalCreate u α) (globalCreate v β) := by
  by_cases huv : u=v
  · subst v
    show globalCreate u α * globalCreate u β = globalCreate u β * globalCreate u α
    rw [global_creation_same_site_zero, global_creation_same_site_zero]
  · show globalCreate u α * globalCreate v β = globalCreate v β * globalCreate u α
    unfold globalCreate
    rw [siteLift_mul_distinct _ _ huv, siteLift_mul_distinct _ _ (Ne.symm huv),
      pairLift_swap_factors]

/-- One SU(2)-invariant triplet-pair creation operator. -/
def pairCreate (u v : V) : ConfigurationMatrix V :=
  ∑ α : Fin 3, globalCreate u α * globalCreate v α

theorem pair_creation_square_zero (u v : V) : (pairCreate u v)^2=0 := by
  unfold pairCreate
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro β _
  rw [(global_creation_commute v u α β).mul_mul_mul_comm,
    global_creation_same_site_zero, zero_mul]

theorem pair_creation_commute (u v r s : V) : Commute (pairCreate u v) (pairCreate r s) := by
  unfold pairCreate
  apply Commute.sum_left
  intro α _
  apply Commute.sum_right
  intro β _
  exact ((global_creation_commute u r α β).mul_right
    (global_creation_commute u s α β)).mul_left
    ((global_creation_commute v r α β).mul_right (global_creation_commute v s α β))

/-- An arbitrary finite real symmetric-pair ansatz, with explicit ordered coefficients.
Callers may set diagonal/lower-triangle coefficients to zero when desired. -/
def pairKernelOperator (K : V → V → ℝ) : ConfigurationMatrix V :=
  ∑ u, ∑ v, K u v • pairCreate u v

/-- Nilpotence is derived from the real finite hard-core operators and their commutation. -/
theorem pair_kernel_nilpotent (K : V → V → ℝ) : IsNilpotent (pairKernelOperator K) := by
  unfold pairKernelOperator
  apply Commute.isNilpotent_sum
  · intro u _
    apply Commute.isNilpotent_sum
    · intro v _
      exact (show IsNilpotent (pairCreate u v) from ⟨2,pair_creation_square_zero u v⟩).smul _
    · intro v s _ _
      exact ((pair_creation_commute u v u s).smul_left _).smul_right _
  · intro u r _ _
    apply Commute.sum_left
    intro v _
    apply Commute.sum_right
    intro s _
    exact ((pair_creation_commute u v r s).smul_left _).smul_right _

end BilayerDressed
