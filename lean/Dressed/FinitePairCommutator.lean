import Dressed.FiniteOccupationTotalCutoff

/-!
# The genuine finite pair-creation commutator

Every operator here is an actual matrix on the total-occupation cutoff.  The
ordinary bosonic pair identity is restricted to columns with two spare grades.
On the last two input grades the pair creator vanishes instead.  No full finite
CCR, operator norm estimate, or pair commutator is assumed as a hypothesis.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOccupation.TotalCutoff.Pair
open Matrix
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matrix vanishes on all input occupation columns strictly below n. -/
def VanishesBelow {M N : ℕ} (A : Op V M N) (n : ℕ) : Prop :=
  ∀ ν μ, totalDegree μ.val < n → A ν μ = 0

/-- The exact finite CCR defect, retained as an actual matrix. -/
def defect {M N : ℕ} (i j : Mode V) : Op V M N :=
  annihilate i * create j - create j * annihilate i -
    (if i = j then (1 : ℝ) else 0) • (1 : Op V M N)

theorem defect_vanishesBelow {M N : ℕ} (hNM : N ≤ M) (i j : Mode V) :
    VanishesBelow (defect (M := M) (N := N) i j) N := by
  intro ν μ hμ
  rw [defect, Matrix.sub_apply, commutator_safe_entry hNM i j ν μ hμ]
  by_cases hij : i = j <;> by_cases hνμ : ν = μ <;>
    simp [hij, hνμ]

theorem VanishesBelow.left_mul {M N n : ℕ} {A : Op V M N}
    (hA : VanishesBelow A n) (B : Op V M N) : VanishesBelow (B * A) n := by
  intro ν μ hμ
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  rw [hA ρ μ hμ, mul_zero]

theorem VanishesBelow.right_create {M N n : ℕ} {A : Op V M N}
    (hA : VanishesBelow A (n + 1)) (i : Mode V) :
    VanishesBelow (A * create i) n := by
  intro ν μ hμ
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  by_cases hz : create (M := M) (N := N) i ρ μ = 0
  · rw [hz, mul_zero]
  · have hd := degree_of_create_ne_zero i ρ μ hz
    rw [hA ν ρ (by omega), zero_mul]

theorem VanishesBelow.right_annihilate {M N n : ℕ} {A : Op V M N}
    (hA : VanishesBelow A n) (i : Mode V) :
    VanishesBelow (A * annihilate i) (n + 1) := by
  intro ν μ hμ
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  by_cases hz : annihilate (M := M) (N := N) i ρ μ = 0
  · rw [hz, mul_zero]
  · have hd := degree_of_annihilate_ne_zero i ρ μ hz
    rw [hA ν ρ (by omega), zero_mul]

omit [DecidableEq V] in
theorem VanishesBelow.mono {M N n m : ℕ} {A : Op V M N}
    (hA : VanishesBelow A n) (hmn : m ≤ n) : VanishesBelow A m := by
  intro ν μ hμ
  exact hA ν μ (lt_of_lt_of_le hμ hmn)

/-- Actual pair creation, with the mode index including every color. -/
def pairCreate {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) : Op V M N :=
  (1 / 2 : ℝ) • ∑ i, ∑ j, B i j • (create i * create j)

/-- The pair creator raises total degree by exactly two. -/
theorem pairCreate_eq_zero_of_degree {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (ν μ : Basis V M N)
    (hdegree : totalDegree ν.val ≠ totalDegree μ.val + 2) :
    pairCreate B ν μ = 0 := by
  simp only [pairCreate, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp_rw [create_pair_eq_zero_of_degree _ _ ν μ hdegree]
  simp

/-- The last two input grades are killed, including cutoffs zero and one. -/
theorem pairCreate_top_entry {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (ν μ : Basis V M N)
    (hμ : N < totalDegree μ.val + 2) : pairCreate B ν μ = 0 := by
  apply pairCreate_eq_zero_of_degree
  have hν := ν.property
  omega

/-- The genuine pair commutator on the last two grades is negative, not the
infinite-CCR expression. -/
theorem pairCommutator_top_entry {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (ν μ : Basis V M N)
    (hμ : N < totalDegree μ.val + 2) :
    ((pairCreate (M := M) (N := N) B).transpose * pairCreate B -
        pairCreate B * (pairCreate B).transpose : Op V M N) ν μ =
      -((pairCreate B * (pairCreate B).transpose : Op V M N) ν μ) := by
  rw [Matrix.sub_apply]
  have hz : ((pairCreate B).transpose * pairCreate B : Op V M N) ν μ = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro ρ _
    rw [pairCreate_top_entry B ρ μ hμ, mul_zero]
  rw [hz, zero_sub]


theorem four_factor_defect_expansion {M N : ℕ} (i j k l : Mode V) :
    (annihilate i * annihilate j) * (create k * create l) -
      (create k * create l) * (annihilate i * annihilate j) =
    (if j = k then (1 : ℝ) else 0) • (create l * annihilate i) +
    (if j = l then (1 : ℝ) else 0) • (create k * annihilate i) +
    (if i = k then (1 : ℝ) else 0) • (create l * annihilate j) +
    (if i = l then (1 : ℝ) else 0) • (create k * annihilate j) +
    ((if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0) +
      (if j = l then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)) •
        (1 : Op V M N) +
    annihilate i * defect j k * create l +
    annihilate i * create k * defect j l +
    defect i k * create l * annihilate j +
    create k * defect i l * annihilate j +
    (if j = k then (1 : ℝ) else 0) • defect i l +
    (if j = l then (1 : ℝ) else 0) • defect i k := by
  simp only [defect, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, mul_one, one_mul, mul_assoc]
  module

/-- Normal ordering of an actual annihilation pair against a creation pair,
valid only with two available upper grades. -/
theorem four_factor_safe_entry {M N n : ℕ} (hNM : N ≤ M) (hnN : n + 2 ≤ N)
    (i j k l : Mode V) (ν μ : Basis V M N) (hμ : totalDegree μ.val ≤ n) :
    ((annihilate i * annihilate j) * (create k * create l) -
      (create k * create l) * (annihilate i * annihilate j) : Op V M N) ν μ =
    ((if j = k then (1 : ℝ) else 0) • (create l * annihilate i) +
    (if j = l then (1 : ℝ) else 0) • (create k * annihilate i) +
    (if i = k then (1 : ℝ) else 0) • (create l * annihilate j) +
    (if i = l then (1 : ℝ) else 0) • (create k * annihilate j) +
    ((if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0) +
      (if j = l then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)) •
        (1 : Op V M N) : Op V M N) ν μ := by
  have hd (a b : Mode V) : VanishesBelow (defect (M := M) (N := N) a b) (n + 2) :=
    (defect_vanishesBelow hNM a b).mono hnN
  have hz₁ : (annihilate i * defect j k * create l : Op V M N) ν μ = 0 := by
    rw [mul_assoc]
    exact ((hd j k).right_create (n := n + 1) l).left_mul (annihilate i) ν μ (by omega)
  have hz₂ : (annihilate i * create k * defect j l : Op V M N) ν μ = 0 :=
    (hd j l).left_mul (annihilate i * create k) ν μ (by omega)
  have hz₃ : (defect i k * create l * annihilate j : Op V M N) ν μ = 0 :=
    ((hd i k).right_create (n := n + 1) l).right_annihilate j ν μ (by omega)
  have hz₄ : (create k * defect i l * annihilate j : Op V M N) ν μ = 0 := by
    rw [mul_assoc]
    exact ((hd i l).right_annihilate j).left_mul (create k) ν μ (by omega)
  rw [four_factor_defect_expansion]
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [hz₁, hz₂, hz₃, hz₄, hd i l ν μ (by omega), hd i k ν μ (by omega)]
  simp

variable {I : Type*} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in
lemma triple_contraction (B : Matrix I I ℝ) (hB : ∀ i j, B i j = B j i)
    (f : I → I → ℝ) :
    (∑ i, ∑ j, ∑ k, B i j * B j k * f k i) =
      ∑ k, ∑ i, (B * B) k i * f k i := by
  calc
    _ = ∑ i, ∑ k, ∑ j, B i j * B j k * f k i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, B i j * B j k * f k i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hB i j, hB j k]
      ring
lemma coefficient_contraction (B : Matrix I I ℝ) (hB : ∀ i j, B i j = B j i)
    (f : I → I → ℝ) (e : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l *
      ((if j = k then (1 : ℝ) else 0) * f l i +
       (if j = l then (1 : ℝ) else 0) * f k i +
       (if i = k then (1 : ℝ) else 0) * f l j +
       (if i = l then (1 : ℝ) else 0) * f k j +
       ((if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0) +
        (if j = l then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)) * e)) =
      4 * (∑ i, ∑ j, (B * B) i j * f i j) + 2 * Matrix.trace (B * B) * e := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ, if_true]
  have h₂ : (∑ i, ∑ j, ∑ k, B i j * B k j * f k i) =
      ∑ i, ∑ j, ∑ k, B i j * B j k * f k i := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    rw [hB k j]
  have h₃ : (∑ i, ∑ j, ∑ k, B i j * B i k * f k j) =
      ∑ i, ∑ j, ∑ k, B i j * B j k * f k i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    rw [hB j i]
  have h₄ : (∑ i, ∑ j, ∑ k, B i j * B k i * f k j) =
      ∑ i, ∑ j, ∑ k, B i j * B j k * f k i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    rw [hB j i, hB k j]
  have hc₂ : (∑ i, ∑ j, B i j * B i j * e) =
      ∑ i, ∑ j, B i j * B j i * e := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hB j i]
  have hc₁ : (∑ i, ∑ j, B i j * B j i * e) = Matrix.trace (B * B) * e := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  rw [h₂, h₃, h₄, hc₂, hc₁, triple_contraction B hB]
  ring

theorem pairCreate_transpose {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j, B i j = B j i) :
    (pairCreate (M := M) (N := N) B).transpose =
      (1 / 2 : ℝ) • ∑ i, ∑ j, B i j • (annihilate i * annihilate j) := by
  simp only [pairCreate, Matrix.transpose_smul, Matrix.transpose_sum, Matrix.transpose_mul,
    annihilate]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB j i]

lemma sum_commutator {I A : Type*} [Fintype I] [Ring A] (f g : I → A) :
    (∑ i, f i) * (∑ j, g j) - (∑ j, g j) * (∑ i, f i) =
      ∑ i, ∑ j, (f i * g j - g j * f i) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

theorem pairCommutator_sum {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j, B i j = B j i) :
    (pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose =
      (1 / 4 : ℝ) • ∑ i, ∑ j, ∑ k, ∑ l, (B i j * B k l) •
        ((annihilate i * annihilate j) * (create k * create l) -
          (create k * create l) * (annihilate i * annihilate j) : Op V M N) := by
  rw [pairCreate_transpose B hB]
  simp only [pairCreate, smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num
  rw [← smul_sub]
  congr 1
  have hh := sum_commutator
    (fun p : Mode V × Mode V => B p.1 p.2 •
      (annihilate p.1 * annihilate p.2 : Op V M N))
    (fun p : Mode V × Mode V => B p.1 p.2 •
      (create p.1 * create p.2 : Op V M N))
  simp only [Fintype.sum_prod_type (α₁ := Mode V) (α₂ := Mode V)] at hh
  rw [hh]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  rw [mul_comm (B k l) (B i j)]

/-- The actual number-preserving second quantization of a mode matrix. -/
def secondQuantization {M N : ℕ} (A : Matrix (Mode V) (Mode V) ℝ) : Op V M N :=
  ∑ i, ∑ j, A i j • (create i * annihilate j)

theorem pairCommutator_safe_entry {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M)
    (ν μ : Basis V M N) (hμ : totalDegree μ.val + 2 ≤ N) :
    ((pairCreate B).transpose * pairCreate B -
        pairCreate B * (pairCreate B).transpose : Op V M N) ν μ =
      (secondQuantization (B * B) + (Matrix.trace (B * B) / 2) •
        (1 : Op V M N) : Op V M N) ν μ := by
  rw [pairCommutator_sum B hB]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp_rw [four_factor_safe_entry hNM hμ _ _ _ _ ν μ (le_refl _)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [coefficient_contraction B hB]
  simp only [secondQuantization, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  ring


lemma secondQuantization_form {M N : ℕ} (A : Matrix (Mode V) (Mode V) ℝ)
    (x : Basis V M N → ℝ) :
    dotProduct x ((secondQuantization A).mulVec x) =
      ∑ ν, dotProduct (fun i => (annihilate i).mulVec x ν)
        (A.mulVec (fun i => (annihilate i).mulVec x ν)) := by
  have hp (i j : Mode V) :
      dotProduct x ((create i * annihilate j : Op V M N).mulVec x) =
        dotProduct ((annihilate i).mulVec x) ((annihilate j).mulVec x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rfl
  simp only [secondQuantization, Matrix.sum_mulVec, Matrix.smul_mulVec,
    dotProduct_sum, dotProduct_smul, smul_eq_mul, hp]
  change (∑ i, ∑ j, A i j * ∑ ν, (annihilate i *ᵥ x) ν * (annihilate j *ᵥ x) ν) =
    ∑ ν, ∑ i, (annihilate i *ᵥ x) ν * ∑ j, A i j * (annihilate j *ᵥ x) ν
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i : Mode V, ∑ ν : Basis V M N, ∑ j : Mode V,
        A i j * ((annihilate i).mulVec x ν * (annihilate j).mulVec x ν) := by
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm
    _ = ∑ ν : Basis V M N, ∑ i : Mode V, ∑ j : Mode V,
        A i j * ((annihilate i).mulVec x ν * (annihilate j).mulVec x ν) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring

lemma secondQuantization_nonneg {M N : ℕ} (A : Matrix (Mode V) (Mode V) ℝ)
    (hA : A.PosSemidef) (x : Basis V M N → ℝ) :
    0 ≤ dotProduct x ((secondQuantization A).mulVec x) := by
  rw [secondQuantization_form]
  apply Finset.sum_nonneg
  intro ν _
  simpa only [star_trivial] using hA.2 (fun i => (annihilate i).mulVec x ν)

lemma secondQuantization_sub {M N : ℕ} (A B : Matrix (Mode V) (Mode V) ℝ) :
    (secondQuantization (A - B) : Op V M N) = secondQuantization A - secondQuantization B := by
  simp only [secondQuantization, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma secondQuantization_scalar {M N : ℕ} (q : ℝ) :
    (secondQuantization (q • (1 : Matrix (Mode V) (Mode V) ℝ)) : Op V M N) =
      q • number := by
  simp only [secondQuantization, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ← Finset.smul_sum, sum_create_annihilate]

lemma secondQuantization_le_number {M N : ℕ} (A : Matrix (Mode V) (Mode V) ℝ)
    (q : ℝ) (hA : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - A).PosSemidef)
    (x : Basis V M N → ℝ) :
    dotProduct x ((secondQuantization A).mulVec x) ≤
      q * dotProduct x ((number : Op V M N).mulVec x) := by
  have hh := secondQuantization_nonneg (M := M) (N := N) _ hA x
  rw [secondQuantization_sub, secondQuantization_scalar] at hh
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, sub_nonneg] using hh

/-- Exact finite projector identity, with the nontruncated safe condition. -/
theorem pairCommutator_on_degreeLE {M N n : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (hnN : n + 2 ≤ N) :
    ((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose) *
        degreeLEProjector n =
      (secondQuantization (B * B) + (Matrix.trace (B * B) / 2) • 1) *
        (degreeLEProjector n : Op V M N) := by
  ext ν μ
  simp only [degreeLEProjector, Matrix.mul_diagonal]
  by_cases hμ : totalDegree μ.val ≤ n
  · rw [if_pos hμ, mul_one, mul_one, pairCommutator_safe_entry B hB hNM ν μ (by omega)]
  · simp [hμ]

theorem pairCommutator_mulVec_of_safe_support {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M)
    (x : Basis V M N → ℝ) (hx : ∀ μ, x μ ≠ 0 → totalDegree μ.val + 2 ≤ N) :
    ((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x =
      (secondQuantization (B * B) + (Matrix.trace (B * B) / 2) • 1 : Op V M N).mulVec x := by
  funext ν
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hz : x μ = 0
  · simp [hz]
  · rw [pairCommutator_safe_entry B hB hNM ν μ (hx μ hz)]

theorem pairCommutator_form_le_of_safe_support {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M)
    (q : ℝ) (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (x : Basis V M N → ℝ) (hx : ∀ μ, x μ ≠ 0 → totalDegree μ.val + 2 ≤ N) :
    dotProduct x
      (((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x) ≤
      q * dotProduct x ((number : Op V M N).mulVec x) +
        (Matrix.trace (B * B) / 2) * dotProduct x x := by
  rw [pairCommutator_mulVec_of_safe_support B hB hNM x hx]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  exact add_le_add_right (secondQuantization_le_number (B * B) q hbound x) _

theorem pairCommutator_mulVec_of_top_support {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (x : Basis V M N → ℝ)
    (hx : ∀ μ, x μ ≠ 0 → N < totalDegree μ.val + 2) :
    ((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x =
      (-(pairCreate B * (pairCreate B).transpose) : Op V M N).mulVec x := by
  funext ν
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hz : x μ = 0
  · simp [hz]
  · rw [pairCommutator_top_entry B ν μ (hx μ hz)]
    rfl

/-- Every vector supported in the top two grades has a nonpositive commutator form. -/
theorem pairCommutator_form_nonpos_of_top_support {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (x : Basis V M N → ℝ)
    (hx : ∀ μ, x μ ≠ 0 → N < totalDegree μ.val + 2) :
    dotProduct x
      (((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x) ≤ 0 := by
  rw [pairCommutator_mulVec_of_top_support B x hx]
  have hp : 0 ≤ dotProduct x
      ((pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose (pairCreate B : Op V M N)).2 x
  simpa only [Matrix.neg_mulVec, dotProduct_neg] using neg_nonpos.mpr hp

omit [DecidableEq V] in
lemma square_posSemidef (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j, B i j = B j i) : (B * B).PosSemidef := by
  have ht : B.transpose = B := by ext i j; exact hB j i
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, ht] using
    Matrix.posSemidef_conjTranspose_mul_self B

lemma number_mulVec_of_grade {M N n : ℕ} (x : Basis V M N → ℝ)
    (hx : ∀ μ, totalDegree μ.val ≠ n → x μ = 0) :
    (number : Op V M N).mulVec x = (n : ℝ) • x := by
  rw [number_eq_diagonal]
  funext μ
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hμ : totalDegree μ.val = n
  · rw [hμ]
  · rw [hx μ hμ, mul_zero, mul_zero]

/-- Genuine finite grade-n quadratic-form bound.  It includes both top grades,
where negativity replaces the ordinary CCR.  There is no extra color factor
multiplying n; all colors are already in the mode matrix B. -/
theorem pairCommutator_form_le_of_grade {M N n : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M)
    (q : ℝ) (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (x : Basis V M N → ℝ) (hx : ∀ μ, totalDegree μ.val ≠ n → x μ = 0) :
    dotProduct x
      (((pairCreate B).transpose * pairCreate B - pairCreate B * (pairCreate B).transpose : Op V M N).mulVec x) ≤
      (q * (n : ℝ) + Matrix.trace (B * B) / 2) * dotProduct x x := by
  have hn : dotProduct x ((number : Op V M N).mulVec x) =
      (n : ℝ) * dotProduct x x := by
    rw [number_mulVec_of_grade x hx, dotProduct_smul, smul_eq_mul]
  have hdeg (μ : Basis V M N) (hμ : x μ ≠ 0) : totalDegree μ.val = n := by
    by_contra h
    exact hμ (hx μ h)
  by_cases hsafe : n + 2 ≤ N
  · have hh := pairCommutator_form_le_of_safe_support B hB hNM q hbound x
      (fun μ hμ => by rw [hdeg μ hμ]; exact hsafe)
    rw [hn] at hh
    convert hh using 1; ring
  · have hh := pairCommutator_form_nonpos_of_top_support B x
      (fun μ hμ => by rw [hdeg μ hμ]; omega)
    apply hh.trans
    have hp := secondQuantization_nonneg (M := M) (N := N) (B * B) (square_posSemidef B hB) x
    have hb := secondQuantization_le_number (M := M) (N := N) (B * B) q hbound x
    rw [hn] at hb
    have ht : 0 ≤ Matrix.trace (B * B) / 2 := div_nonneg (square_posSemidef B hB).trace_nonneg (by norm_num)
    have hxnonneg : 0 ≤ dotProduct x x := by
      exact Finset.sum_nonneg (fun μ _ => mul_self_nonneg (x μ))
    nlinarith [mul_nonneg ht hxnonneg]

/-- The commutator form is the difference of genuine finite Hilbert norm squares. -/
theorem pairCommutator_form_eq_norm_sq {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (x : EuclideanSpace ℝ (Basis V M N)) :
    dotProduct (WithLp.ofLp x)
      (((pairCreate B).transpose * pairCreate B -
        pairCreate B * (pairCreate B).transpose : Op V M N).mulVec (WithLp.ofLp x)) =
      ‖(pairCreate B).toEuclideanLin x‖ ^ 2 -
        ‖(pairCreate B).transpose.toEuclideanLin x‖ ^ 2 := by
  simp only [Matrix.sub_mulVec, dotProduct_sub, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    star_trivial]
  have hf (A : Op V M N) :
      dotProduct (WithLp.ofLp x) ((A.transpose * A).mulVec (WithLp.ofLp x)) =
        dotProduct (A.mulVec (WithLp.ofLp x)) (A.mulVec (WithLp.ofLp x)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact congrArg₂ (fun a b : ℝ => a - b) (hf (pairCreate B))
    (by simpa only [Matrix.transpose_transpose] using hf (pairCreate B).transpose)

/-- The same grade-n bound in the actual Euclidean Hilbert norm, ready for the
finite graded pair-power recurrence. -/
theorem pairCreate_norm_sq_sub_adjoint_norm_sq_le {M N n : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M)
    (q : ℝ) (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (x : EuclideanSpace ℝ (Basis V M N))
    (hx : ∀ μ, totalDegree μ.val ≠ n → x μ = 0) :
    ‖(pairCreate B).toEuclideanLin x‖ ^ 2 -
        ‖(pairCreate B).transpose.toEuclideanLin x‖ ^ 2 ≤
      (q * (n : ℝ) + Matrix.trace (B * B) / 2) * ‖x‖ ^ 2 := by
  have hh := pairCommutator_form_le_of_grade B hB hNM q hbound (WithLp.ofLp x) hx
  rw [pairCommutator_form_eq_norm_sq] at hh
  have hnorm : dotProduct (WithLp.ofLp x) (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      real_inner_self_eq_norm_sq x
  rwa [hnorm] at hh

end BilayerDressed.FiniteOccupation.TotalCutoff.Pair
