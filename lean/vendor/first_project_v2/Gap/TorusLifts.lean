import Gap.TorusBasis

/-!
# Configuration-space lifts and exact independent-cluster matrix identities

A one-site lift acts by the supplied matrix at its site and by identity at every
other site. These are explicit matrix entries, not formal noncommutative symbols.
-/
noncomputable section
namespace BilayerGap
namespace Torus
open ClusterProducts Matrix
open scoped Kronecker
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A genuine tensor-identity extension of a local matrix. -/
def siteLift {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) (v : V) : Matrix (V → S) (V → S) ℝ :=
  fun s t => if ∀ w, w ≠ v → s w = t w then A (s v) (t v) else 0

/-- A two-site matrix, acting as identity outside those two sites. -/
def pairLift {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix (S × S) (S × S) ℝ) (u v : V) : Matrix (V → S) (V → S) ℝ :=
  fun s t => if ∀ w, w ≠ u → w ≠ v → s w = t w
    then A (s u,s v) (t u,t v) else 0

private theorem outside_zero_iff {S : Type*} {k : ℕ}
    (s t : Fin (k+1) → S) :
    (∀ w, w ≠ 0 → s w = t w) ↔ (fun j : Fin k => s j.succ) = (fun j : Fin k => t j.succ) := by
  constructor
  · intro h; funext j; exact h j.succ (Fin.succ_ne_zero j)
  · intro h w hw
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hw
    exact congrFun h j

private theorem outside_succ_iff {S : Type*} {k : ℕ}
    (s t : Fin (k+1) → S) (i : Fin k) :
    (∀ w, w ≠ i.succ → s w = t w) ↔
      s 0 = t 0 ∧ ∀ j, j ≠ i → s j.succ = t j.succ := by
  constructor
  · intro h
    exact ⟨h 0 (Fin.succ_ne_zero i).symm, fun j hj => h j.succ (by simpa using hj)⟩
  · rintro ⟨h0,h⟩ w hw
    refine Fin.cases (fun _ => h0) (fun j hw => ?_) w hw
    exact h j (by simpa using hw)

theorem siteLift_zero {S : Type*} [DecidableEq S] {k : ℕ}
    (A : Matrix S S ℝ) (s t : Fin (k+1) → S) :
    siteLift A 0 s t = A (s 0) (t 0) *
      (if (fun j : Fin k => s j.succ) = (fun j : Fin k => t j.succ) then 1 else 0) := by
  simp only [siteLift, outside_zero_iff]
  split <;> simp_all

theorem siteLift_succ {S : Type*} [DecidableEq S] {k : ℕ}
    (A : Matrix S S ℝ) (s t : Fin (k+1) → S) (i : Fin k) :
    siteLift A i.succ s t = (if s 0 = t 0 then 1 else 0) *
      siteLift A i (fun j : Fin k => s j.succ) (fun j : Fin k => t j.succ) := by
  simp only [siteLift, outside_succ_iff]
  by_cases h0 : s 0 = t 0 <;> by_cases h : ∀ j, j ≠ i → s j.succ = t j.succ <;>
    simp [h0,h]

/-- Sum-of-local-operators formula for the actual recursive tensor Hamiltonian. -/
theorem independent_as_site_sum (A : Matrix (Fin 16) (Fin 16) ℝ) (k : ℕ)
    (s t : PowerIndex k) :
    independentHamiltonian A k s t =
      ∑ i, siteLift A i (powerIndexEquiv k s) (powerIndexEquiv k t) := by
  induction k with
  | zero => simp [independentHamiltonian]
  | succ k ih =>
    rcases s with ⟨s0,s⟩
    rcases t with ⟨t0,t⟩
    rw [Fin.sum_univ_succ, siteLift_zero]
    simp only [siteLift_succ, ← Finset.mul_sum]
    change A s0 t0 * (1 : Matrix (PowerIndex k) (PowerIndex k) ℝ) s t +
        (1 : Matrix (Fin 16) (Fin 16) ℝ) s0 t0 * independentHamiltonian A k s t =
      A s0 t0 * (if powerIndexEquiv k s = powerIndexEquiv k t then 1 else 0) +
        (if s0 = t0 then 1 else 0) *
          ∑ i, siteLift A i (powerIndexEquiv k s) (powerIndexEquiv k t)
    rw [ih]
    simp only [Equiv.apply_eq_iff_eq, Matrix.one_apply]

/-- Product-of-Kronecker-deltas form, for comparison with transfer expansions. -/
theorem siteLift_eq_delta_product {V S : Type*} [Fintype V] [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) (v : V) (s t : V → S) :
    siteLift A v s t =
      (∏ w ∈ Finset.univ.erase v, (if s w = t w then 1 else 0 : ℝ)) * A (s v) (t v) := by
  rw [Finset.prod_boole]
  have he : (∀ w ∈ Finset.univ.erase v, s w = t w) ↔ ∀ w, w ≠ v → s w = t w := by simp
  simp only [he]
  unfold siteLift
  split <;> simp_all

/-- Two-site product-of-deltas form. -/
theorem pairLift_eq_delta_product {V S : Type*} [Fintype V] [DecidableEq V] [DecidableEq S]
    (A : Matrix (S×S) (S×S) ℝ) (u v : V) (s t : V → S) :
    pairLift A u v s t =
      (∏ w ∈ (Finset.univ.erase u).erase v, (if s w = t w then 1 else 0 : ℝ)) *
        A (s u,s v) (t u,t v) := by
  rw [Finset.prod_boole]
  have he : (∀ w ∈ (Finset.univ.erase u).erase v, s w = t w) ↔
      ∀ w, w ≠ u → w ≠ v → s w = t w := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  simp only [he]
  unfold pairLift
  split <;> simp_all

/-- The local cluster label records its actual ordered endpoint rung states. -/
def packedConfig {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V)
    (s : V → Fin 4) : Fin k → Fin 16 :=
  fun i => finProdFinEquiv (s (e (i,0)),s (e (i,1)))

theorem basisOfPairing_symm_packed {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V)
    (s : V → Fin 4) :
    powerIndexEquiv k ((basisOfPairing e).symm s) = packedConfig e s := by
  simp only [basisOfPairing, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

private theorem packed_outside_iff {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V)
    (s t : V → Fin 4) (i : Fin k) :
    (∀ j, j ≠ i → packedConfig e s j = packedConfig e t j) ↔
      ∀ v, v ≠ e (i,0) → v ≠ e (i,1) → s v = t v := by
  constructor
  · intro h v hv0 hv1
    obtain ⟨⟨j,a⟩,rfl⟩ := e.surjective v
    have hji : j ≠ i := by
      intro he; subst j
      fin_cases a
      · exact hv0 rfl
      · exact hv1 rfl
    have he := finProdFinEquiv.injective (h j hji)
    fin_cases a
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · intro h j hji
    apply congrArg finProdFinEquiv
    apply Prod.ext
    · exact h (e (j,0))
        (fun he => hji (congrArg Prod.fst (e.injective he)))
        (fun he => hji (congrArg Prod.fst (e.injective he)))
    · exact h (e (j,1))
        (fun he => hji (congrArg Prod.fst (e.injective he)))
        (fun he => hji (congrArg Prod.fst (e.injective he)))

/-- Generic independent cluster matrix becomes the sum of actual two-site lifts. -/
theorem reindex_independent_eq_pair_sum {V : Type*} [DecidableEq V] {k : ℕ}
    (e : (Fin k × Fin 2) ≃ V) (A : Matrix (Fin 16) (Fin 16) ℝ) :
    Matrix.reindex (basisOfPairing e) (basisOfPairing e) (independentHamiltonian A k) =
      ∑ i, pairLift (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm A)
        (e (i,0)) (e (i,1)) := by
  ext s t
  change independentHamiltonian A k ((basisOfPairing e).symm s) ((basisOfPairing e).symm t) = _
  rw [independent_as_site_sum, basisOfPairing_symm_packed, basisOfPairing_symm_packed]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [siteLift, pairLift, packed_outside_iff]
  rfl

theorem pairLift_add {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A B : Matrix (S×S) (S×S) ℝ) (u v : V) :
    pairLift (A+B) u v = pairLift A u v + pairLift B u v := by
  ext s t
  simp only [pairLift, Matrix.add_apply]
  split <;> simp

theorem pairLift_sub {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A B : Matrix (S×S) (S×S) ℝ) (u v : V) :
    pairLift (A-B) u v = pairLift A u v - pairLift B u v := by
  ext s t
  simp only [pairLift, Matrix.sub_apply]
  split <;> simp

theorem pairLift_smul {V S : Type*} [DecidableEq V] [DecidableEq S]
    (a : ℝ) (A : Matrix (S×S) (S×S) ℝ) (u v : V) :
    pairLift (a • A) u v = a • pairLift A u v := by
  ext s t
  simp only [pairLift, Matrix.smul_apply, smul_eq_mul]
  split <;> simp

theorem pairLift_sum {V S I : Type*} [DecidableEq V] [DecidableEq S] [Fintype I]
    (A : I → Matrix (S×S) (S×S) ℝ) (u v : V) :
    pairLift (∑ i, A i) u v = ∑ i, pairLift (A i) u v := by
  ext s t
  simp only [pairLift, Matrix.sum_apply]
  split <;> simp

theorem pairLift_left {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) {u v : V} (huv : u ≠ v) :
    pairLift (A ⊗ₖ (1 : Matrix S S ℝ)) u v = siteLift A u := by
  ext s t
  have he : (∀ w, w ≠ u → s w = t w) ↔
      (∀ w, w ≠ u → w ≠ v → s w = t w) ∧ s v = t v := by
    constructor
    · intro h; exact ⟨fun w hw _ => h w hw, h v huv.symm⟩
    · rintro ⟨h,hv⟩ w hw
      by_cases hv' : w = v
      · simpa [hv'] using hv
      · exact h w hw hv'
  simp only [siteLift, pairLift, he, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases hout : ∀ w, w ≠ u → w ≠ v → s w = t w <;>
    by_cases hv : s v = t v <;> simp [hout,hv]

theorem pairLift_right {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) {u v : V} (huv : u ≠ v) :
    pairLift ((1 : Matrix S S ℝ) ⊗ₖ A) u v = siteLift A v := by
  ext s t
  have he : (∀ w, w ≠ v → s w = t w) ↔
      (∀ w, w ≠ u → w ≠ v → s w = t w) ∧ s u = t u := by
    constructor
    · intro h; exact ⟨fun w _ hw => h w hw, h u huv⟩
    · rintro ⟨h,hu⟩ w hw
      by_cases hu' : w = u
      · simpa [hu'] using hu
      · exact h w hu' hw
  simp only [siteLift, pairLift, he, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases hout : ∀ w, w ≠ u → w ≠ v → s w = t w <;>
    by_cases hu : s u = t u <;> simp [hout,hu]

/-- The two-site tensor lift is the actual product of the two lifted local matrices. -/
theorem siteLift_mul_distinct {V S : Type*} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S] (A B : Matrix S S ℝ) {u v : V} (huv : u ≠ v) :
    siteLift A u * siteLift B v = pairLift (A ⊗ₖ B) u v := by
  ext s t
  let r₀ : V → S := Function.update s u (t u)
  rw [Matrix.mul_apply, Finset.sum_eq_single r₀]
  · have hleft : ∀ w, w ≠ u → s w = r₀ w := by
      intro w hw; simp [r₀, Function.update_of_ne hw]
    have hright : (∀ w, w ≠ v → r₀ w = t w) ↔
        ∀ w, w ≠ u → w ≠ v → s w = t w := by
      constructor
      · intro h w hwu hwv
        simpa [r₀, Function.update_of_ne hwu] using h w hwv
      · intro h w hwv
        by_cases hwu : w = u
        · simp [r₀,hwu]
        · simpa [r₀,Function.update_of_ne hwu] using h w hwu hwv
    simp only [siteLift, pairLift, if_pos hleft, hright, Matrix.kronecker_apply]
    simp only [r₀, Function.update_self, Function.update_of_ne huv.symm]
    split <;> simp
  · intro r _ hr
    by_cases hleft : ∀ w, w ≠ u → s w = r w
    · by_cases hright : ∀ w, w ≠ v → r w = t w
      · exfalso
        apply hr
        funext w
        by_cases hw : w = u
        · subst w; simpa [r₀] using hright u huv
        · simpa [r₀,Function.update_of_ne hw] using (hleft w hw).symm
      · simp [siteLift,hright]
    · simp [siteLift,hleft]
  · simp

/-- Identical local factors make the edge lift independent of edge orientation. -/
theorem pairLift_tensor_swap {V S : Type*} [DecidableEq V] [DecidableEq S]
    (G : Matrix S S ℝ) (u v : V) :
    pairLift (G ⊗ₖ G) u v = pairLift (G ⊗ₖ G) v u := by
  ext s t
  have he : (∀ w, w ≠ u → w ≠ v → s w = t w) ↔
      (∀ w, w ≠ v → w ≠ u → s w = t w) := by tauto
  simp only [pairLift,he,Matrix.kronecker_apply,mul_comm]

/-- Tensor-identity extension respects matrix transpose. -/
theorem siteLift_transpose {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) (v : V) : (siteLift A v).transpose = siteLift A.transpose v := by
  ext s t
  have he : (∀ w, w ≠ v → t w = s w) ↔ (∀ w, w ≠ v → s w = t w) := by
    simp only [eq_comm]
  simp only [siteLift,Matrix.transpose_apply,he]

theorem siteLift_neg {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) (v : V) : siteLift (-A) v = -siteLift A v := by
  ext s t
  simp only [siteLift,Matrix.neg_apply]
  split <;> simp

theorem siteLift_hermitian {V S : Type*} [DecidableEq V] [DecidableEq S]
    (A : Matrix S S ℝ) (hA : A.IsHermitian) (v : V) : (siteLift A v).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial,siteLift_transpose]
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] at hA
  rw [hA]

/-- Copies of the same local matrix at any two sites commute, including a degenerate edge. -/
theorem siteLift_self_commute {V S : Type*} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S] (A : Matrix S S ℝ) (u v : V) :
    Commute (siteLift A u) (siteLift A v) := by
  by_cases huv : u = v
  · subst v; exact Commute.refl _
  · change siteLift A u * siteLift A v = siteLift A v * siteLift A u
    rw [siteLift_mul_distinct A A huv,siteLift_mul_distinct A A (Ne.symm huv),
      pairLift_tensor_swap A u v]

/-- A product of two copies of an antisymmetric local generator is Hermitian. -/
theorem siteLift_antisymmetric_product_hermitian {V S : Type*} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S] (G : Matrix S S ℝ)
    (hG : G.transpose = -G) (u v : V) : (siteLift G u * siteLift G v).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul,
    siteLift_transpose,siteLift_transpose,hG,siteLift_neg,siteLift_neg,neg_mul_neg]
  exact (siteLift_self_commute G u v).eq.symm

end Torus
end BilayerGap
