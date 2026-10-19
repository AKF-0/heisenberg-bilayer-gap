import Dressed.GlobalCartesianBasis
import Dressed.DressedVacuum

/-!
# Number action on the actual finite dressed vacuum

The commutator [N,S]=2S is derived from actual tensor-basis entries and the
physical number projector sum. The final exponential identity has no assumed
grading or number-action premise and applies to every real ordered kernel K.
-/
noncomputable section
namespace BilayerDressed.NumberDressing
open Matrix BilayerGap
open scoped BigOperators Kronecker
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev H (V : Type*) [Fintype V] := ConfigurationHilbert V
abbrev Op (V : Type*) := ConfigurationMatrix V

/-- Entrywise number increase produces the actual matrix commutator. -/
theorem number_commutator_of_raise_two (A : Op V)
    (hA : ∀ s t, A s t ≠ 0 → CartesianBasis.count s = CartesianBasis.count t + 2) :
    (TripletNumber.number : Op V) * A = A * TripletNumber.number + (2 : ℝ) • A := by
  ext s t
  rw [TripletNumber.number_eq_diagonal]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hz : A s t = 0
  · simp [hz]
  · have he : TripletNumber.energy s = TripletNumber.energy t + 2 := by
      rw [← CartesianBasis.count_cast, ← CartesianBasis.count_cast, hA s t hz]
      push_cast
      rfl
    rw [he]
    ring

/-- A concrete local pair creator raises the total triplet count by exactly two. -/
theorem pairLift_raises_two
    (A : Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ)
    (hA : ∀ p q, A p q ≠ 0 → CartesianBasis.pairCount p = 2 ∧ CartesianBasis.pairCount q = 0)
    (u v : V) (huv : u ≠ v) (s t : Configuration V)
    (hst : Torus.pairLift A u v s t ≠ 0) :
    CartesianBasis.count s = CartesianBasis.count t + 2 := by
  have hout : ∀ w, w ≠ u → w ≠ v → s w = t w := by
    by_contra hh
    exact hst (by simp [Torus.pairLift, hh])
  have hn : A (s u,s v) (t u,t v) ≠ 0 := by
    simpa only [Torus.pairLift, if_pos hout] using hst
  rcases hA (s u,s v) (t u,t v) hn with ⟨hs,ht⟩
  rw [CartesianBasis.count_eq_pair_add_outside u v huv s,
    CartesianBasis.count_eq_pair_add_outside u v huv t, hs, ht,
    CartesianBasis.outsideCount_eq u v s t hout]
  omega

/-- Actual commutator for each concrete two-creation product. -/
theorem creation_product_commutator (u v : V) (huv : u ≠ v) (α : Fin 3) :
    (TripletNumber.number : Op V) * (globalCreate u α * globalCreate v α) =
      (globalCreate u α * globalCreate v α) * TripletNumber.number +
        (2 : ℝ) • (globalCreate u α * globalCreate v α) := by
  apply number_commutator_of_raise_two
  intro s t hst
  apply pairLift_raises_two (rungCreate α ⊗ₖ rungCreate α)
    (CartesianBasis.local_creation_count_support α) u v huv s t
  simpa only [globalCreate, Torus.siteLift_mul_distinct _ _ huv] using hst

/-- Actual SU(2)-pair creation, including the vanishing coincident-site case. -/
theorem pairCreate_commutator (u v : V) :
    (TripletNumber.number : Op V) * pairCreate u v =
      pairCreate u v * TripletNumber.number + (2 : ℝ) • pairCreate u v := by
  by_cases huv : u=v
  · subst v
    simp [pairCreate_same_site_zero]
  · simp only [pairCreate, Matrix.mul_sum, Matrix.sum_mul,
      creation_product_commutator _ _ huv, Finset.sum_add_distrib, ← Finset.smul_sum]

/-- No symmetry or diagonal condition on the ordered kernel is needed. -/
theorem pairKernelOperator_commutator (K : V → V → ℝ) :
    (TripletNumber.number : Op V) * pairKernelOperator K =
      pairKernelOperator K * TripletNumber.number + (2 : ℝ) • pairKernelOperator K := by
  simp only [pairKernelOperator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, pairCreate_commutator, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  exact smul_comm _ _ _

theorem pairKernelS_commutator (K : V → V → ℝ) :
    (TripletNumber.number : Op V) * pairKernelS K =
      pairKernelS K * TripletNumber.number + (2 : ℝ) • pairKernelS K :=
  pairKernelOperator_commutator _

/-- The actual physical number operator, as a Hilbert-space continuous linear map. -/
def numberGenerator : H V →L[ℝ] H V :=
  Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) TripletNumber.number

/-- Actual zero action on the normalized all-singlet vacuum. -/
theorem numberGenerator_vacuum : (numberGenerator : H V →L[ℝ] H V) vacuumVector = 0 := by
  ext s
  have hv : (TripletNumber.number : Op V).mulVec
      (Pi.single (TripletNumber.vacuum : Configuration V) 1) = 0 := by
    rw [TripletNumber.number_eq_diagonal, Matrix.diagonal_mulVec_single]
    simp [TripletNumber.energy_vacuum]
  exact congrFun hv s

theorem pairGenerator_commutator (K : V → V → ℝ) :
    numberGenerator * pairGenerator K = pairGenerator K * numberGenerator +
      (2 : ℝ) • pairGenerator K := by
  have hh := congrArg (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
    (pairKernelS_commutator K)
  simpa only [map_mul, map_add, map_smul, numberGenerator, pairGenerator] using hh

section FiniteIdentity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

omit [Nontrivial E] in
/-- Finite algebraic power identity; the hypothesis will be discharged by the actual matrices. -/
theorem number_power_vacuum (N S : E →L[ℝ] E) (Ω : E)
    (hNS : N*S = S*N + (2 : ℝ) • S) (hΩ : N Ω = 0) (k : ℕ) :
    N ((S^k) Ω) = (2*(k : ℝ)) • ((S^k) Ω) := by
  induction k with
  | zero => simpa using hΩ
  | succ k ih =>
    have hh := congrArg (fun T : E →L[ℝ] E => T ((S^k) Ω)) hNS
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply] at hh
    rw [pow_succ', ContinuousLinearMap.mul_apply, hh, ih, map_smul]
    rw [← add_smul]
    congr 1
    push_cast
    ring

omit [Nontrivial E] in
/-- Exact finite-Taylor number action, with the cutoff shifted by one. -/
theorem number_taylor_vacuum (N S : E →L[ℝ] E) (Ω : E)
    (hNS : N*S = S*N + (2 : ℝ) • S) (hΩ : N Ω = 0) (m : ℕ) :
    N (taylorOperator S (m+1) Ω) = taylorOperator S m ((2 : ℝ) • (S Ω)) := by
  simp only [taylorOperator, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, ContinuousLinearMap.one_apply, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul, hΩ, add_zero]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [number_power_vacuum N S Ω hNS hΩ]
  simp only [pow_succ, ContinuousLinearMap.mul_apply, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

local instance : Module ℚ (E →L[ℝ] E) :=
  Module.compHom (E →L[ℝ] E) (Rat.castHom ℝ)

/-- Exact nilpotent exponential identity, proved through finite Taylor polynomials. -/
theorem number_nilpotent_exp_vacuum (N S : E →L[ℝ] E) (Ω : E)
    (hNS : N*S = S*N + (2 : ℝ) • S) (hΩ : N Ω = 0) (hS : IsNilpotent S) :
    N ((IsNilpotent.exp S) Ω) = (IsNilpotent.exp S) ((2 : ℝ) • (S Ω)) := by
  obtain ⟨m,hm⟩ := hS
  have hm1 : S^(m+1)=0 := by rw [pow_succ, hm, zero_mul]
  calc
    _ = N (taylorOperator S (m+1) Ω) := by rw [nilpotent_exp_eq_taylor S (m+1) hm1]
    _ = taylorOperator S m ((2 : ℝ) • (S Ω)) := number_taylor_vacuum N S Ω hNS hΩ m
    _ = _ := by rw [nilpotent_exp_eq_taylor S m hm]
end FiniteIdentity

local instance : Module ℚ (H V →L[ℝ] H V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- The final concrete physical identity: no number-action or grading premise remains. -/
theorem number_dressedVector (K : V → V → ℝ) :
    Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (TripletNumber.number : Op V) (dressedVector K) =
        (IsNilpotent.exp (pairGenerator K)) ((2 : ℝ) • (pairGenerator K vacuumVector)) := by
  exact number_nilpotent_exp_vacuum numberGenerator (pairGenerator K) vacuumVector
    (pairGenerator_commutator K) numberGenerator_vacuum (pairGenerator_nilpotent K)

end BilayerDressed.NumberDressing
