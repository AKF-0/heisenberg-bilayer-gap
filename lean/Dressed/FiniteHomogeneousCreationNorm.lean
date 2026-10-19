import Dressed.FiniteOccupationRotatedWords
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite homogeneous creation multiplication

The coefficient proof uses finite occupation antidiagonals, not a
symmetric-tensor bound. All scalars are real, as in the actual cutoff matrices.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation.Homogeneous
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {I : Type*} [DecidableEq I]

/-- Multivariate Vandermonde, by finite-mode induction and ordinary Vandermonde. -/
theorem multivariate_vandermonde (s : Finset I) (γ : I → ℕ) (d : ℕ) :
    (∑ α ∈ s.piAntidiag d, ∏ i ∈ s, (γ i).choose (α i)) =
      (∑ i ∈ s, γ i).choose d := by
  induction s using Finset.cons_induction generalizing d with
  | empty =>
    by_cases hd : d = 0
    · subst d; simp
    · simp [Finset.piAntidiag_empty_of_ne_zero hd, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hd)]
  | @cons i s hi ih =>
    rw [Finset.piAntidiag_cons hi, Finset.sum_disjiUnion]
    simp only [Finset.sum_map, addRightEmbedding_apply, Pi.add_apply]
    calc
      _ = ∑ p ∈ Finset.antidiagonal d,
          (γ i).choose p.1 * (∑ α ∈ s.piAntidiag p.2, ∏ j ∈ s, (γ j).choose (α j)) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro α hα
        have hzero : α i = 0 := by
          by_contra hne
          exact hi ((Finset.mem_piAntidiag.mp hα).2 i hne)
        rw [Finset.prod_cons]
        simp only [ite_true, hzero, zero_add]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        simp [hji]
      _ = ∑ p ∈ Finset.antidiagonal d, (γ i).choose p.1 * (∑ j ∈ s, γ j).choose p.2 := by
        simp_rw [ih]
      _ = _ := by rw [Finset.sum_cons, Nat.add_choose_eq]

variable [Fintype I]

/-- The finite set of all occupations of exactly degree n. -/
def gradeIndices (n : ℕ) : Finset (I → ℕ) := Finset.piAntidiag Finset.univ n

@[simp] theorem mem_gradeIndices {n : ℕ} {α : I → ℕ} :
    α ∈ gradeIndices n ↔ ∑ i, α i = n := by simp [gradeIndices]

/-- Product binomial coefficient of two occupations. -/
def multiChoose (γ α : I → ℕ) : ℕ := ∏ i, (γ i).choose (α i)

theorem sum_multiChoose (γ : I → ℕ) (d : ℕ) :
    ∑ α ∈ gradeIndices d, multiChoose γ α = (∑ i, γ i).choose d :=
  multivariate_vandermonde Finset.univ γ d

/-- Euclidean squared norm on an exact finite occupation grade. -/
def gradeNormSq (n : ℕ) (v : (I → ℕ) → ℝ) : ℝ :=
  ∑ α ∈ gradeIndices n, v α ^ 2

/-- The normalized creation convolution. Missing occupations contribute zero. -/
def multiply (d : ℕ) (r v : (I → ℕ) → ℝ) (γ : I → ℕ) : ℝ :=
  ∑ α ∈ gradeIndices d,
    Real.sqrt (multiChoose γ α : ℝ) *
      (if α ≤ γ then r α * v (γ - α) else 0)

theorem multiply_coefficient_bound (d : ℕ) (r v : (I → ℕ) → ℝ) (γ : I → ℕ) :
    multiply d r v γ ^ 2 ≤ ((∑ i, γ i).choose d : ℝ) *
      ∑ α ∈ gradeIndices d, if α ≤ γ then r α ^ 2 * v (γ - α) ^ 2 else 0 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (gradeIndices (I := I) d)
    (fun α => Real.sqrt (multiChoose γ α : ℝ))
    (fun α => if α ≤ γ then r α * v (γ - α) else 0)
  simp only [Real.sq_sqrt (Nat.cast_nonneg _), ite_pow, mul_pow, zero_pow (by decide : 2 ≠ 0)] at h
  rw [← Nat.cast_sum, sum_multiChoose] at h
  exact h

/-- Subtracting a supported degree-d occupation leaves exactly degree n. -/
theorem degree_sub {n d : ℕ} {α γ : I → ℕ}
    (hα : α ∈ gradeIndices d) (hγ : γ ∈ gradeIndices (n + d)) (hle : α ≤ γ) :
    γ - α ∈ gradeIndices n := by
  apply mem_gradeIndices.mpr
  have he : (∑ i, γ i) = (∑ i, α i) + ∑ i, (γ - α) i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.add_sub_of_le (hle i)).symm
  have ha := mem_gradeIndices.mp hα
  have hg := mem_gradeIndices.mp hγ
  omega

/-- Exact finite change of variables γ = α + β. -/
theorem sum_occupation_sub {n d : ℕ} (α : I → ℕ) (hα : α ∈ gradeIndices d)
    (f : (I → ℕ) → ℝ) :
    (∑ γ ∈ gradeIndices (n + d), if α ≤ γ then f (γ - α) else 0) =
      ∑ β ∈ gradeIndices n, f β := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun γ _ => γ - α)
  · intro γ hγ
    exact degree_sub hα (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2
  · intro γ hγ δ hδ he
    funext i
    have hg := (Finset.mem_filter.mp hγ).2 i
    have hd := (Finset.mem_filter.mp hδ).2 i
    change α i ≤ γ i at hg
    change α i ≤ δ i at hd
    have hi := congrFun he i
    change γ i - α i = δ i - α i at hi
    omega
  · intro β hβ
    refine ⟨α + β, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · apply mem_gradeIndices.mpr
      simp only [Pi.add_apply, Finset.sum_add_distrib, mem_gradeIndices.mp hα,
        mem_gradeIndices.mp hβ]
      omega
    · intro i; exact Nat.le_add_right _ _
    · funext i; exact Nat.add_sub_cancel_left _ _
  · intro γ hγ
    rfl

/-- The exact finite homogeneous multiplication norm, with the sharp binomial
factor. This is a proved occupation convolution bound, not an assumed tensor
estimate. -/
theorem homogeneous_multiplication_bound (n d : ℕ) (r v : (I → ℕ) → ℝ) :
    gradeNormSq (n + d) (multiply d r v) ≤
      ((n + d).choose d : ℝ) * gradeNormSq d r * gradeNormSq n v := by
  unfold gradeNormSq
  calc
    _ ≤ ∑ γ ∈ gradeIndices (n + d), ((n + d).choose d : ℝ) *
        ∑ α ∈ gradeIndices d, if α ≤ γ then r α ^ 2 * v (γ - α) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro γ hγ
      simpa only [mem_gradeIndices.mp hγ] using multiply_coefficient_bound d r v γ
    _ = ((n + d).choose d : ℝ) *
        ∑ α ∈ gradeIndices d, r α ^ 2 * ∑ β ∈ gradeIndices n, v β ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro α hα
      calc
        _ = r α ^ 2 * ∑ γ ∈ gradeIndices (n + d),
            if α ≤ γ then v (γ - α) ^ 2 else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro γ hγ
          split_ifs <;> simp
        _ = _ := by rw [sum_occupation_sub (n := n) α hα (fun β => v β ^ 2)]
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The finite occupation convolution has the correct degree-zero endpoint. -/
theorem multiply_degree_zero (r v : (I → ℕ) → ℝ) (γ : I → ℕ) :
    multiply 0 r v γ = r 0 * v γ := by
  simp [multiply, gradeIndices, multiChoose]

/-- The convolution of a residual with vacuum has exactly its seed coefficients. -/
theorem multiply_vacuum (d : ℕ) (r : (I → ℕ) → ℝ) (γ : I → ℕ)
    (hγ : γ ∈ gradeIndices d) :
    multiply d r (fun β => if β = 0 then 1 else 0) γ = r γ := by
  unfold multiply
  rw [Finset.sum_eq_single γ]
  · simp [multiChoose]
  · intro α hα hne
    by_cases hle : α ≤ γ
    · have hnz : γ - α ≠ 0 := by
        intro he
        apply hne
        funext i
        have hi := congrFun he i
        have hh : α i ≤ γ i := hle i
        change γ i - α i = 0 at hi
        omega
      simp [hle, hnz]
    · simp [hle]
  · exact fun h => False.elim (h hγ)

section ActualMatrices
variable {V : Type*} [Fintype V] [DecidableEq V]
open Matrix

/-- Forget only the finite coordinate bounds. -/
def naturalOccupation {M : ℕ} (ν : Occupation V M) : Mode V → ℕ := fun i => (ν i).val

/-- Actual normalized occupation shift, including all cutoff zeros. -/
def normalizedKernel {M : ℕ} (α : Mode V → ℕ) : FiniteOccupation.Op V M :=
  fun ν μ => if naturalOccupation ν = α + naturalOccupation μ
    then Real.sqrt (multiChoose (naturalOccupation ν) α : ℝ) else 0

omit [DecidableEq V] in
/-- Degree-zero normalized creation is exactly the identity matrix. -/
theorem normalizedKernel_zero {M : ℕ} :
    normalizedKernel (V := V) (M := M) 0 = 1 := by
  ext ν μ
  have he : naturalOccupation ν = naturalOccupation μ ↔ ν = μ := by
    constructor
    · intro h; funext i; exact Fin.ext (congrFun h i)
    · intro h; rw [h]
  simp [normalizedKernel, multiChoose, he, Matrix.one_apply]

/-- Increment the multiplicity of one mode. -/
def addMode (α : Mode V → ℕ) (i : Mode V) : Mode V → ℕ :=
  Function.update α i (α i + 1)

/-- A single-coordinate Pascal identity, multiplied over the other modes. -/
theorem multiChoose_addMode (α β : Mode V → ℕ) (i : Mode V) :
    (α i + 1) * multiChoose (addMode α i + β) (addMode α i) =
      (α i + β i + 1) * multiChoose (α + β) α := by
  unfold multiChoose
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => (α + β) j |>.choose (α j)) (Finset.mem_univ i)]
  have hp : (∏ j ∈ Finset.univ.erase i, ((addMode α i + β) j).choose (addMode α i j)) =
      ∏ j ∈ Finset.univ.erase i, ((α + β) j).choose (α j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [addMode, (Finset.mem_erase.mp hj).1]
  rw [hp]
  simp only [addMode, Function.update_self, Pi.add_apply]
  have hc := Nat.succ_mul_choose_eq (α i + β i) (α i)
  have he : α i + 1 + β i = α i + β i + 1 := by omega
  rw [he]
  simpa only [Nat.succ_eq_add_one, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun t : ℕ => t * ∏ j ∈ Finset.univ.erase i, (α j + β j).choose (α j)) hc.symm

omit [Fintype V] in
/-- Exact support composition for one actual creation. -/
theorem raises_addMode {M : ℕ} (α : Mode V → ℕ) (i : Mode V)
    (ν ρ μ : Occupation V M) (hν : Raises i ν ρ)
    (hρ : naturalOccupation ρ = α + naturalOccupation μ) :
    naturalOccupation ν = addMode α i + naturalOccupation μ := by
  funext j
  have hj := congrFun hρ j
  change (ρ j).val = α j + (μ j).val at hj
  by_cases hji : j = i
  · subst j
    simp only [naturalOccupation, addMode, Function.update_self, Pi.add_apply]
    have h := hν.1
    omega
  · simp only [naturalOccupation, addMode, Function.update_of_ne hji, Pi.add_apply]
    rw [hν.2 j hji]
    exact hj

/-- Creation times a normalized shift is the next normalized shift with the
precise square-root multiplicity. This equality retains every cutoff zero. -/
theorem create_mul_normalizedKernel {M : ℕ} (α : Mode V → ℕ) (i : Mode V) :
    FiniteOccupation.create i * normalizedKernel (M := M) α =
      Real.sqrt (α i + 1 : ℝ) • normalizedKernel (addMode α i) := by
  ext ν μ
  by_cases hfinal : naturalOccupation ν = addMode α i + naturalOccupation μ
  · have hbound : ∀ j, α j + (μ j).val < M + 1 := by
      intro j
      have hj := congrFun hfinal j
      have hv := (ν j).isLt
      change (ν j).val = addMode α i j + (μ j).val at hj
      by_cases hji : j = i
      · subst j
        simp only [addMode, Function.update_self] at hj
        omega
      · simp only [addMode, Function.update_of_ne hji] at hj
        omega
    let ρ : Occupation V M := fun j => ⟨α j + (μ j).val, hbound j⟩
    have hρ : naturalOccupation ρ = α + naturalOccupation μ := rfl
    have hraise : Raises i ν ρ := by
      constructor
      · have hi := congrFun hfinal i
        simp only [naturalOccupation, addMode, Function.update_self, Pi.add_apply] at hi
        change (ν i).val = (α i + (μ i).val) + 1
        omega
      · intro j hji
        apply Fin.ext
        have hj := congrFun hfinal j
        simpa only [naturalOccupation, addMode, Function.update_of_ne hji, Pi.add_apply]
          using hj
    rw [Matrix.mul_apply, Finset.sum_eq_single ρ]
    · simp only [FiniteOccupation.create, if_pos hraise, normalizedKernel, if_pos hρ,
        Matrix.smul_apply, smul_eq_mul, if_pos hfinal]
      have hc := multiChoose_addMode α (naturalOccupation μ) i
      rw [← hfinal, ← hρ] at hc
      have hcr : (α i + 1 : ℝ) * (multiChoose (naturalOccupation ν) (addMode α i) : ℝ) =
          (α i + (μ i).val + 1 : ℝ) * (multiChoose (naturalOccupation ρ) α : ℝ) := by
        exact_mod_cast hc
      have hsq : (Real.sqrt ((ρ i).val + 1 : ℝ) *
          Real.sqrt (multiChoose (naturalOccupation ρ) α : ℝ)) ^ 2 =
          (Real.sqrt (α i + 1 : ℝ) *
          Real.sqrt (multiChoose (naturalOccupation ν) (addMode α i) : ℝ)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (ρ i).val + 1),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ α i + 1),
          Real.sq_sqrt (Nat.cast_nonneg _)]
        change (((α i + (μ i).val : ℕ) : ℝ) + 1) * _ = _
        push_cast
        exact hcr.symm
      nlinarith [mul_nonneg (Real.sqrt_nonneg ((ρ i).val + 1 : ℝ))
        (Real.sqrt_nonneg (multiChoose (naturalOccupation ρ) α : ℝ)),
        mul_nonneg (Real.sqrt_nonneg (α i + 1 : ℝ))
        (Real.sqrt_nonneg (multiChoose (naturalOccupation ν) (addMode α i) : ℝ))]
    · intro δ hδ hne
      by_cases hs : naturalOccupation δ = α + naturalOccupation μ
      · have he : δ = ρ := by
          funext j
          apply Fin.ext
          exact congrFun (hs.trans hρ.symm) j
        exact False.elim (hne he)
      · simp [normalizedKernel, hs]
    · simp
  · simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, normalizedKernel,
      if_neg hfinal, mul_zero]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_cases hs : naturalOccupation ρ = α + naturalOccupation μ
    · have hn : ¬ Raises i ν ρ := fun hr => hfinal (raises_addMode α i ν ρ μ hr hs)
      simp [FiniteOccupation.create, hn]
    · simp [hs]

/-- An actual finite product of creation matrices, in a fixed word order. -/
def creationWord {M : ℕ} : List (Mode V) → FiniteOccupation.Op V M
  | [] => 1
  | i :: L => FiniteOccupation.create i * creationWord L

/-- Exact finite matrix entries of an arbitrary creation word. -/
theorem creationWord_eq_kernel {M : ℕ} (L : List (Mode V)) :
    creationWord (M := M) L = Real.sqrt (RotatedWords.wordFactorial L : ℝ) •
      normalizedKernel (fun i => L.count i) := by
  induction L with
  | nil => simpa [creationWord] using (normalizedKernel_zero (V := V) (M := M)).symm
  | cons i L ih =>
    rw [creationWord, ih, Matrix.mul_smul, create_mul_normalizedKernel, smul_smul,
      RotatedWords.wordFactorial_cons]
    have hc : (fun j => (i :: L).count j) = addMode (fun j => L.count j) i := by
      funext j
      by_cases hji : j = i
      · subst j; simp [addMode]
      · simp [addMode, hji, Ne.symm hji]
    rw [hc, Nat.cast_mul, Real.sqrt_mul (by positivity)]
    rw [mul_comm]
    congr 1
    norm_cast

/-- A concrete list containing α_i copies of each finite mode. -/
def occupationList (α : Mode V → ℕ) : List (Mode V) :=
  (Finset.univ : Finset (Mode V)).toList.flatMap (fun i => List.replicate (α i) i)

@[simp] theorem count_occupationList (α : Mode V → ℕ) (i : Mode V) :
    (occupationList α).count i = α i := by
  simp [occupationList, List.count_flatMap, Function.comp_def,
    Finset.sum_map_toList, List.count_replicate, beq_iff_eq]

/-- Actual creation product divided by its occupation factorial normalization. -/
def normalizedMonomial {M : ℕ} (α : Mode V → ℕ) : FiniteOccupation.Op V M :=
  (Real.sqrt (RotatedWords.wordFactorial (occupationList α) : ℝ))⁻¹ •
    creationWord (occupationList α)

/-- The occupation convolution kernel is proved equal to the actual normalized
creation product, rather than postulated as its action. -/
theorem normalizedMonomial_eq_kernel {M : ℕ} (α : Mode V → ℕ) :
    normalizedMonomial (M := M) α = normalizedKernel α := by
  rw [normalizedMonomial, creationWord_eq_kernel, smul_smul]
  have hp : (0 : ℝ) < RotatedWords.wordFactorial (occupationList α) := by
    exact_mod_cast RotatedWords.wordFactorial_pos (occupationList α)
  rw [inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hp)), one_smul]
  simp

/-- Actual total-cutoff coordinate index, forgetting the stored bound proofs. -/
def naturalBasis {M N : ℕ} (ν : TotalCutoff.Basis V M N) : Mode V → ℕ :=
  naturalOccupation ν.val

omit [DecidableEq V] in
theorem naturalBasis_injective {M N : ℕ} :
    Function.Injective (naturalBasis (V := V) (M := M) (N := N)) := by
  intro ν μ h
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun h i)

/-- Extend an actual finite vector by zero to all natural occupations. -/
def readVector {M N : ℕ} (x : RotatedWords.Vector V M N) (β : Mode V → ℕ) : ℝ :=
  if h : ∃ ν : TotalCutoff.Basis V M N, naturalBasis ν = β then x h.choose else 0

@[simp] theorem readVector_basis {M N : ℕ} (x : RotatedWords.Vector V M N)
    (ν : TotalCutoff.Basis V M N) : readVector x (naturalBasis ν) = x ν := by
  have h : ∃ μ : TotalCutoff.Basis V M N, naturalBasis μ = naturalBasis ν := ⟨ν, rfl⟩
  rw [readVector, dif_pos h]
  exact congrArg x (naturalBasis_injective h.choose_spec)

theorem readVector_nonzero_exists {M N : ℕ} (x : RotatedWords.Vector V M N)
    (β : Mode V → ℕ) (hβ : readVector x β ≠ 0) :
    ∃ ν : TotalCutoff.Basis V M N, naturalBasis ν = β := by
  by_contra h
  exact hβ (by simp [readVector, h])

theorem readVector_grade {M N n : ℕ} {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) (β : Mode V → ℕ) (hβ : (∑ i, β i) ≠ n) :
    readVector x β = 0 := by
  by_cases h : ∃ ν : TotalCutoff.Basis V M N, naturalBasis ν = β
  · obtain ⟨ν, rfl⟩ := h
    rw [readVector_basis]
    exact hx ν hβ
  · simp [readVector, h]

/-- The occupation coefficient squared norm is exactly the actual Euclidean
squared norm, not an assumed isometry. -/
theorem gradeNormSq_readVector {M N n : ℕ} {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) : gradeNormSq n (readVector x) = x ⬝ᵥ x := by
  unfold gradeNormSq dotProduct
  simp only [← sq]
  symm
  apply Finset.sum_bij_ne_zero (fun ν _ _ => naturalBasis ν)
  · intro ν hν hne
    apply mem_gradeIndices.mpr
    by_contra hn
    have hz := hx ν hn
    simp [hz] at hne
  · intro ν hν hne μ hμ hme he
    exact naturalBasis_injective he
  · intro β hβ hne
    have hn : readVector x β ≠ 0 := by intro h; simp [h] at hne
    obtain ⟨ν, rfl⟩ := readVector_nonzero_exists x β hn
    exact ⟨ν, Finset.mem_univ _, by simpa using hne, rfl⟩
  · intro ν hν hne
    simp

/-- Subtracting occupation multiplicities stays inside the actual total cutoff. -/
def subBasis {M N : ℕ} (ν : TotalCutoff.Basis V M N) (α : Mode V → ℕ) :
    TotalCutoff.Basis V M N :=
  ⟨fun i => ⟨(ν.val i).val - α i, lt_of_le_of_lt (Nat.sub_le _ _) (ν.val i).isLt⟩,
    le_trans (Finset.sum_le_sum (fun i _ => Nat.sub_le (ν.val i).val (α i))) ν.property⟩

omit [DecidableEq V] in
@[simp] theorem naturalBasis_subBasis {M N : ℕ} (ν : TotalCutoff.Basis V M N)
    (α : Mode V → ℕ) : naturalBasis (subBasis ν α) = naturalBasis ν - α := rfl

/-- Actual compressed normalized-monomial action, with exactly the convolution
coefficient and an explicit zero if subtraction is impossible. -/
theorem normalizedKernel_mulVec {M N : ℕ} (α : Mode V → ℕ)
    (x : RotatedWords.Vector V M N) (ν : TotalCutoff.Basis V M N) :
    (TotalCutoff.compress (normalizedKernel α) *ᵥ x) ν =
      Real.sqrt (multiChoose (naturalBasis ν) α : ℝ) *
        (if α ≤ naturalBasis ν then readVector x (naturalBasis ν - α) else 0) := by
  rw [Matrix.mulVec, dotProduct]
  by_cases hle : α ≤ naturalBasis ν
  · rw [if_pos hle, Finset.sum_eq_single (subBasis ν α)]
    · have hs : naturalBasis ν = α + naturalBasis (subBasis ν α) := by
        funext i
        exact (Nat.add_sub_of_le (hle i)).symm
      change (if naturalBasis ν = α + naturalBasis (subBasis ν α) then _ else _) * _ = _
      rw [if_pos hs, ← naturalBasis_subBasis ν α, readVector_basis]
      rfl
    · intro μ hμ hne
      have hs : naturalBasis ν ≠ α + naturalBasis μ := by
        intro he
        apply hne
        apply naturalBasis_injective
        rw [naturalBasis_subBasis, he]
        funext i
        exact (Nat.add_sub_cancel_left (α i) (naturalBasis μ i)).symm
      change (if naturalBasis ν = α + naturalBasis μ then _ else _) * x μ = 0
      rw [if_neg hs, zero_mul]
    · simp
  · rw [if_neg hle, mul_zero]
    apply Finset.sum_eq_zero
    intro μ hμ
    have hs : naturalBasis ν ≠ α + naturalBasis μ := by
      intro he
      apply hle
      intro i
      rw [he]
      exact Nat.le_add_right _ _
    change (if naturalBasis ν = α + naturalBasis μ then _ else _) * _ = 0
    rw [if_neg hs, zero_mul]

/-- Finite homogeneous sum of genuine normalized creation products. -/
def homogeneousOperator {M N : ℕ} (d : ℕ) (r : (Mode V → ℕ) → ℝ) :
    TotalCutoff.Op V M N :=
  ∑ α ∈ gradeIndices d, r α • TotalCutoff.compress (normalizedMonomial α)

/-- The normalized convolution is the exact actual matrix-vector product at
all represented output occupations, even at a cutoff boundary. -/
theorem homogeneousOperator_coefficient {M N : ℕ} (d : ℕ)
    (r : (Mode V → ℕ) → ℝ) (x : RotatedWords.Vector V M N)
    (ν : TotalCutoff.Basis V M N) :
    (homogeneousOperator d r *ᵥ x) ν = multiply d r (readVector x) (naturalBasis ν) := by
  simp only [homogeneousOperator, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, normalizedMonomial_eq_kernel,
    normalizedKernel_mulVec, multiply]
  apply Finset.sum_congr rfl
  intro α hα
  split_ifs <;> ring

/-- Multiplication cannot mix exact total grades. -/
theorem multiply_eq_zero_of_degree (n d : ℕ) (r v : (Mode V → ℕ) → ℝ)
    (hv : ∀ β, (∑ i, β i) ≠ n → v β = 0) (γ : Mode V → ℕ)
    (hγ : (∑ i, γ i) ≠ n + d) : multiply d r v γ = 0 := by
  unfold multiply
  apply Finset.sum_eq_zero
  intro α hα
  by_cases hle : α ≤ γ
  · have hsub : (∑ i, (γ - α) i) ≠ n := by
      intro hn
      apply hγ
      have he : (∑ i, γ i) = (∑ i, α i) + ∑ i, (γ - α) i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact (Nat.add_sub_of_le (hle i)).symm
      rw [he, mem_gradeIndices.mp hα, hn, Nat.add_comm]
    simp [hle, hv _ hsub]
  · simp [hle]

/-- Exact grade support for the actual homogeneous operator. -/
theorem homogeneousOperator_grade {M N n : ℕ} (d : ℕ)
    (r : (Mode V → ℕ) → ℝ) {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) :
    RotatedWords.HasGrade (n + d) (homogeneousOperator d r *ᵥ x) := by
  intro ν hν
  rw [homogeneousOperator_coefficient]
  exact multiply_eq_zero_of_degree n d r (readVector x) (readVector_grade hx) _ hν

/-- Truncation only discards nonnegative squared coefficients. -/
theorem actual_norm_le_coefficient_norm {M N n : ℕ} (d : ℕ)
    (r : (Mode V → ℕ) → ℝ) {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) :
    (homogeneousOperator d r *ᵥ x) ⬝ᵥ (homogeneousOperator d r *ᵥ x) ≤
      gradeNormSq (n + d) (multiply d r (readVector x)) := by
  rw [← gradeNormSq_readVector (homogeneousOperator_grade d r hx)]
  apply Finset.sum_le_sum
  intro γ hγ
  by_cases h : ∃ ν : TotalCutoff.Basis V M N, naturalBasis ν = γ
  · obtain ⟨ν, rfl⟩ := h
    rw [readVector_basis, homogeneousOperator_coefficient]
  · simp only [readVector, dif_neg h, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

/-- Sharp finite creation bound in terms of normalized occupation coefficients.
It remains valid under an insufficient cutoff, because output is discarded. -/
theorem actual_homogeneous_norm_bound {M N n : ℕ} (d : ℕ)
    (r : (Mode V → ℕ) → ℝ) {x : RotatedWords.Vector V M N}
    (hx : RotatedWords.HasGrade n x) :
    (homogeneousOperator d r *ᵥ x) ⬝ᵥ (homogeneousOperator d r *ᵥ x) ≤
      ((n + d).choose d : ℝ) * gradeNormSq d r * (x ⬝ᵥ x) := by
  calc
    _ ≤ gradeNormSq (n + d) (multiply d r (readVector x)) :=
      actual_norm_le_coefficient_norm d r hx
    _ ≤ _ := by
      simpa only [gradeNormSq_readVector hx] using
        homogeneous_multiplication_bound n d r (readVector x)

/-- Every degree-d occupation is genuinely present under the stated cutoffs. -/
def basisOfGrade {M N d : ℕ} (hNM : N ≤ M) (hdN : d ≤ N)
    (α : Mode V → ℕ) (hα : α ∈ gradeIndices d) : TotalCutoff.Basis V M N :=
  ⟨fun i => ⟨α i, Nat.lt_succ_of_le (le_trans
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    (le_trans (by simpa only [mem_gradeIndices.mp hα] using hdN) hNM))⟩,
    by simpa only [totalDegree, mem_gradeIndices.mp hα] using hdN⟩

@[simp] theorem naturalBasis_basisOfGrade {M N d : ℕ} (hNM : N ≤ M) (hdN : d ≤ N)
    (α : Mode V → ℕ) (hα : α ∈ gradeIndices d) :
    naturalBasis (basisOfGrade hNM hdN α hα) = α := rfl

omit [DecidableEq V] in
@[simp] theorem naturalBasis_vacuum {M N : ℕ} :
    naturalBasis (TotalCutoff.vacuum : TotalCutoff.Basis V M N) = 0 := rfl

/-- The actual finite vacuum extends to exactly the zero-occupation delta. -/
theorem readVector_vacuum {M N : ℕ} :
    readVector (RotatedWords.vacuumVector : RotatedWords.Vector V M N) =
      fun β => if β = 0 then 1 else 0 := by
  funext β
  by_cases h : ∃ ν : TotalCutoff.Basis V M N, naturalBasis ν = β
  · obtain ⟨ν, rfl⟩ := h
    rw [readVector_basis]
    have he : naturalBasis ν = 0 ↔ ν = TotalCutoff.vacuum := by
      constructor
      · intro hν
        apply naturalBasis_injective
        exact hν
      · intro hν; rw [hν, naturalBasis_vacuum]
    by_cases hν : ν = TotalCutoff.vacuum
    · subst ν
      simp [RotatedWords.vacuumVector]
    · simp [RotatedWords.vacuumVector, he, hν]
  · have hn : β ≠ 0 := by
      intro hb
      exact h ⟨TotalCutoff.vacuum, by rw [naturalBasis_vacuum, hb]⟩
    simp [readVector, h, hn]

/-- With adequate degree cutoff, the vacuum seed norm is exactly the coefficient
norm, with no lost occupation and no omitted repeated modes. -/
theorem homogeneous_vacuum_norm {M N : ℕ} (hNM : N ≤ M) (d : ℕ) (hdN : d ≤ N)
    (r : (Mode V → ℕ) → ℝ) :
    (homogeneousOperator d r *ᵥ (RotatedWords.vacuumVector : RotatedWords.Vector V M N)) ⬝ᵥ
      (homogeneousOperator d r *ᵥ RotatedWords.vacuumVector) = gradeNormSq d r := by
  rw [← gradeNormSq_readVector (homogeneousOperator_grade d r RotatedWords.grade_vacuum)]
  simp only [Nat.zero_add]
  apply Finset.sum_congr rfl
  intro α hα
  have he := homogeneousOperator_coefficient d r
    (RotatedWords.vacuumVector : RotatedWords.Vector V M N) (basisOfGrade hNM hdN α hα)
  rw [naturalBasis_basisOfGrade, readVector_vacuum, multiply_vacuum d r α hα] at he
  rw [← naturalBasis_basisOfGrade hNM hdN α hα, readVector_basis, he]
  rfl

/-- The desired actual-operator inequality. All n+d output levels are explicitly
available, and the norm of the genuine vacuum seed determines the constant. -/
theorem actual_homogeneous_vacuum_bound {M N n d : ℕ} (hNM : N ≤ M)
    (hcut : n + d ≤ N) (r : (Mode V → ℕ) → ℝ)
    {x : RotatedWords.Vector V M N} (hx : RotatedWords.HasGrade n x) :
    (homogeneousOperator d r *ᵥ x) ⬝ᵥ (homogeneousOperator d r *ᵥ x) ≤
      ((n + d).choose d : ℝ) *
      ((homogeneousOperator d r *ᵥ (RotatedWords.vacuumVector : RotatedWords.Vector V M N)) ⬝ᵥ
        (homogeneousOperator d r *ᵥ RotatedWords.vacuumVector)) * (x ⬝ᵥ x) := by
  rw [homogeneous_vacuum_norm hNM d (by omega) r]
  exact actual_homogeneous_norm_bound d r hx

/-- A word made directly from the actual compressed creation matrices. -/
def totalCreationWord {M N : ℕ} : List (Mode V) → TotalCutoff.Op V M N
  | [] => 1
  | i :: L => TotalCutoff.create i * totalCreationWord L

/-- Compression of a pure creation word is exact: an excluded intermediate
occupation can never be repaired by a later creation. -/
theorem compress_creationWord {M N : ℕ} (L : List (Mode V)) :
    TotalCutoff.compress (creationWord (M := M) L) =
      (totalCreationWord L : TotalCutoff.Op V M N) := by
  induction L with
  | nil =>
    ext ν μ
    simp [creationWord, totalCreationWord, TotalCutoff.compress, Matrix.one_apply,
      Subtype.val_inj]
  | cons i L ih =>
    rw [creationWord, totalCreationWord, ← ih, TotalCutoff.create_mul_compress]

/-- Explicit identification of every summand with a normalized product of the
actual total-cutoff creation matrices, not merely a proposed coefficient model. -/
theorem compress_normalizedMonomial {M N : ℕ} (α : Mode V → ℕ) :
    TotalCutoff.compress (normalizedMonomial (M := M) α) =
      (Real.sqrt (RotatedWords.wordFactorial (occupationList α) : ℝ))⁻¹ •
        (totalCreationWord (occupationList α) : TotalCutoff.Op V M N) := by
  rw [← compress_creationWord]
  rfl

/-- The conventional occupation factorial in the normalization is explicit. -/
theorem factorial_occupationList (α : Mode V → ℕ) :
    RotatedWords.wordFactorial (occupationList α) = ∏ i, (α i).factorial := by
  simp [RotatedWords.wordFactorial]

/-- No output coefficient is truncated when every n+d level is available. -/
theorem actual_norm_eq_coefficient_norm {M N n d : ℕ} (hNM : N ≤ M)
    (hcut : n + d ≤ N) (r : (Mode V → ℕ) → ℝ)
    {x : RotatedWords.Vector V M N} (hx : RotatedWords.HasGrade n x) :
    (homogeneousOperator d r *ᵥ x) ⬝ᵥ (homogeneousOperator d r *ᵥ x) =
      gradeNormSq (n + d) (multiply d r (readVector x)) := by
  rw [← gradeNormSq_readVector (homogeneousOperator_grade d r hx)]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [← naturalBasis_basisOfGrade hNM hcut γ hγ, readVector_basis,
    homogeneousOperator_coefficient]

/-- Degree zero is scalar multiplication, including at cutoff zero. -/
theorem homogeneousOperator_zero_mulVec {M N : ℕ} (r : (Mode V → ℕ) → ℝ)
    (x : RotatedWords.Vector V M N) : homogeneousOperator 0 r *ᵥ x = r 0 • x := by
  ext ν
  rw [homogeneousOperator_coefficient, multiply_degree_zero, readVector_basis]
  rfl

/-- Stronger version for truncated output: only the degree-d vacuum seed must
fit. The outgoing n+d grade is allowed to be discarded by the actual cutoff. -/
theorem actual_homogeneous_vacuum_bound_truncated {M N n d : ℕ} (hNM : N ≤ M)
    (hseed : d ≤ N) (r : (Mode V → ℕ) → ℝ)
    {x : RotatedWords.Vector V M N} (hx : RotatedWords.HasGrade n x) :
    (homogeneousOperator d r *ᵥ x) ⬝ᵥ (homogeneousOperator d r *ᵥ x) ≤
      ((n + d).choose d : ℝ) *
      ((homogeneousOperator d r *ᵥ (RotatedWords.vacuumVector : RotatedWords.Vector V M N)) ⬝ᵥ
        (homogeneousOperator d r *ᵥ RotatedWords.vacuumVector)) * (x ⬝ᵥ x) := by
  rw [homogeneous_vacuum_norm hNM d hseed r]
  exact actual_homogeneous_norm_bound d r hx

end ActualMatrices

end BilayerDressed.FiniteOccupation.Homogeneous
