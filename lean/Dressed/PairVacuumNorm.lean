import Dressed.CreationNorms

/-!
# Exact norm of the finite pair ansatz on the genuine vacuum

Ordered-pair convention: the standard operator is one half of
`pairKernelOperator K`. For symmetric zero-diagonal K its squared vacuum norm
is `(3/2) * ∑ u, ∑ v, (K u v)^2`, or three times the undirected-edge sum.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Matrix
namespace BilayerDressed
open BilayerGap.Torus
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 800000

/-- The all-singlet configuration. -/
def vacuumConfiguration : Configuration V := fun _ => 0
/-- The normalized physical tensor-basis vacuum. -/
def vacuumVector : ConfigurationHilbert V := EuclideanSpace.single vacuumConfiguration 1
/-- A same-color triplet pair in the genuine configuration basis. -/
def pairConfiguration (u v : V) (α : Fin 3) : Configuration V :=
  Function.update (Function.update vacuumConfiguration v α.succ) u α.succ

/-- The column version of the concrete creation rule. -/
theorem globalCreate_entry_column (v : V) (α : Fin 3) (s t : Configuration V) :
    globalCreate v α s t =
      if t v = 0 then if s = Function.update t v α.succ then 1 else 0 else 0 := by
  classical
  have he : ((∀ w, w ≠ v → s w = t w) ∧ s v = α.succ) ↔
      s = Function.update t v α.succ := by
    constructor
    · rintro ⟨hout, hv⟩
      funext w
      by_cases hw : w = v
      · subst w; simpa using hv
      · simpa [Function.update_of_ne hw] using hout w hw
    · intro ht
      subst s
      exact ⟨fun w hw => by simp [Function.update_of_ne hw], by simp⟩
  simp only [globalCreate, siteLift, rungCreate, Matrix.single, Matrix.of_apply]
  have hc : ((∀ w, w ≠ v → s w = t w) ∧ (α.succ = s v ∧ 0 = t v)) ↔
      (t v = 0 ∧ s = Function.update t v α.succ) := by
    constructor
    · rintro ⟨ho, ha, hb⟩
      exact ⟨hb.symm, he.mp ⟨ho, ha.symm⟩⟩
    · rintro ⟨hb, ha⟩
      have hh := he.mpr ha
      exact ⟨hh.1, hh.2.symm, hb.symm⟩
  rw [← ite_and]
  simp only [hc, ite_and]

/-- Creation acts on basis vectors by the actual hard-core update, or vanishes. -/
theorem globalCreate_single (v : V) (α : Fin 3) (t : Configuration V) :
    Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α)
        (EuclideanSpace.single t 1) =
      if t v = 0 then EuclideanSpace.single (Function.update t v α.succ) 1 else 0 := by
  classical
  ext s
  change (globalCreate v α *ᵥ Pi.single t 1) s = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [globalCreate_entry_column]
  by_cases ht : t v = 0 <;> simp [ht, EuclideanSpace.single_apply, eq_comm]

/-- Distinct endpoints create exactly the three orthogonal same-color basis pairs. -/
theorem pairCreate_vacuum (u v : V) (huv : u ≠ v) :
    Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate u v) vacuumVector =
      ∑ α : Fin 3, EuclideanSpace.single (pairConfiguration u v α) 1 := by
  classical
  unfold pairCreate
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_mul, ContinuousLinearMap.mul_apply]
  apply Finset.sum_congr rfl
  intro α _
  rw [vacuumVector, globalCreate_single]
  simp only [vacuumConfiguration, Pi.zero_apply, eq_self_iff_true, if_true]
  rw [globalCreate_single]
  simp [Function.update_of_ne huv, vacuumConfiguration, pairConfiguration]

/-- Exactly the two endpoints are occupied, in the chosen triplet color. -/
theorem pairConfiguration_apply (u v w : V) (α : Fin 3) :
    pairConfiguration u v α w = if w = u ∨ w = v then α.succ else 0 := by
  classical
  by_cases hwu : w = u <;> by_cases hwv : w = v <;>
    simp [pairConfiguration, Function.update_apply, vacuumConfiguration, hwu, hwv]

theorem pairConfiguration_nonzero (u v w : V) (α : Fin 3) :
    pairConfiguration u v α w ≠ 0 ↔ w = u ∨ w = v := by
  rw [pairConfiguration_apply]
  split_ifs <;> simp_all

theorem pairConfiguration_swap (u v : V) (α : Fin 3) :
    pairConfiguration u v α = pairConfiguration v u α := by
  funext w
  simp only [pairConfiguration_apply, or_comm]

/-- Configuration equality detects both unordered endpoints and the triplet color. -/
theorem pairConfiguration_eq_iff (u v r s : V) (α β : Fin 3)
    (huv : u ≠ v) (hrs : r ≠ s) :
    pairConfiguration u v α = pairConfiguration r s β ↔
      α = β ∧ ((u = r ∧ v = s) ∨ (u = s ∧ v = r)) := by
  constructor
  · intro h
    have hu : u = r ∨ u = s := by
      apply (pairConfiguration_nonzero r s u β).mp
      rw [← h]
      exact (pairConfiguration_nonzero u v u α).mpr (Or.inl rfl)
    have hv : v = r ∨ v = s := by
      apply (pairConfiguration_nonzero r s v β).mp
      rw [← h]
      exact (pairConfiguration_nonzero u v v α).mpr (Or.inr rfl)
    have hep : (u = r ∧ v = s) ∨ (u = s ∧ v = r) := by
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact False.elim (huv (hu.trans hv.symm))
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨hu, hv⟩
      · exact False.elim (huv (hu.trans hv.symm))
    refine ⟨?_, hep⟩
    have hcol := congrFun h u
    simp only [pairConfiguration_apply, eq_self_iff_true, true_or, if_true] at hcol
    have hh : u = r ∨ u = s := hu
    simpa only [if_pos hh, Fin.succ_inj] using hcol
  · rintro ⟨rfl, h | h⟩
    · rcases h with ⟨rfl, rfl⟩; rfl
    · rcases h with ⟨rfl, rfl⟩; exact pairConfiguration_swap _ _ _

/-- The pair operator vanishes when both endpoints coincide. -/
theorem pairCreate_same_site_zero (u : V) : pairCreate u u = 0 := by
  simp [pairCreate, global_creation_same_site_zero]

/-- An exact vacuum overlap, retaining the two ordered descriptions of an edge. -/
theorem single_inner_pairCreate_vacuum (u v r s : V) (α : Fin 3) (huv : u ≠ v) :
    ⟪EuclideanSpace.single (pairConfiguration u v α) (1 : ℝ),
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate r s) vacuumVector⟫ =
      (if u = r ∧ v = s then 1 else 0) + (if u = s ∧ v = r then 1 else 0) := by
  classical
  by_cases hrs : r = s
  · subst s
    rw [pairCreate_same_site_zero, map_zero, ContinuousLinearMap.zero_apply, inner_zero_right]
    have h : ¬(u = r ∧ v = r) := by rintro ⟨h1, h2⟩; exact huv (h1.trans h2.symm)
    simp [h]
  · rw [pairCreate_vacuum r s hrs, inner_sum]
    simp only [EuclideanSpace.inner_single_left, star_one, one_mul,
      EuclideanSpace.single_apply]
    simp only [pairConfiguration_eq_iff u v r s _ _ huv hrs]
    by_cases h1 : u = r ∧ v = s
    · rcases h1 with ⟨rfl, rfl⟩
      simp [huv, Ne.symm huv]
    · by_cases h2 : u = s ∧ v = r
      · rcases h2 with ⟨rfl, rfl⟩
        simp [huv, Ne.symm huv]
      · have h1' : ¬(r = u ∧ s = v) := by tauto
        have h2' : ¬(r = v ∧ s = u) := by tauto
        simp [h1, h2, h1', h2']

/-- Each genuine same-color pair coefficient receives the two ordered kernel entries. -/
theorem single_inner_pairKernel_vacuum (K : V → V → ℝ) (u v : V)
    (α : Fin 3) (huv : u ≠ v) :
    ⟪EuclideanSpace.single (pairConfiguration u v α) (1 : ℝ),
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (pairKernelOperator K) vacuumVector⟫ = K u v + K v u := by
  classical
  unfold pairKernelOperator
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right,
    single_inner_pairCreate_vacuum u v _ _ α huv]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp [mul_ite, ite_and]

/-- The standard half-weighted ordered-pair creation ansatz. -/
def pairKernelS (K : V → V → ℝ) : ConfigurationMatrix V :=
  pairKernelOperator (fun u v => K u v / 2)

/-- Exact quadratic vacuum norm for an arbitrary ordered kernel, before symmetry. -/
theorem pairKernelOperator_vacuum_norm_sq (K : V → V → ℝ) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (pairKernelOperator K) vacuumVector‖ ^ 2 =
      ∑ u, ∑ v, if u = v then 0 else 3 * K u v * (K u v + K v u) := by
  classical
  let y := Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
    (pairKernelOperator K) vacuumVector
  have hy : y = ∑ u, ∑ v, K u v •
      (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (pairCreate u v) vacuumVector) := by
    simp only [y, pairKernelOperator, map_sum, ContinuousLinearMap.sum_apply,
      map_smul, ContinuousLinearMap.smul_apply]
  change ‖y‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq]
  calc
    ⟪y,y⟫ = ⟪∑ u, ∑ v, K u v •
        (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
          (pairCreate u v) vacuumVector), y⟫ := by rw [← hy]
    _ = ∑ u, ∑ v, K u v * ⟪Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
          (pairCreate u v) vacuumVector, y⟫ := by
      simp only [sum_inner, real_inner_smul_left]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : u = v
      · subst v
        simp [pairCreate_same_site_zero]
      · rw [pairCreate_vacuum u v huv, sum_inner]
        simp only [y, single_inner_pairKernel_vacuum K u v _ huv, if_neg huv,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Exact physical vacuum norm with the standard half-weighted ordered-pair convention. -/
theorem pairKernelS_vacuum_norm_sq (K : V → V → ℝ)
    (hK : ∀ u v, K u v = K v u) (hdiag : ∀ u, K u u = 0) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (pairKernelS K) vacuumVector‖ ^ 2 =
      (3 / 2 : ℝ) * ∑ u, ∑ v, (K u v)^2 := by
  classical
  unfold pairKernelS
  rw [pairKernelOperator_vacuum_norm_sq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u = v
  · subst v
    simp [hdiag]
  · simp only [if_neg huv, ← hK u v]
    ring

end BilayerDressed
