import Dressed.FinitePairCommutator
import Dressed.FiniteWickSupersolution

/-!
# Actual finite positive pair-state moments

This module uses the real finite total-cutoff creation matrices. It retains
the upper-boundary correction with its favorable entrywise sign. The state
is an explicitly finite Taylor polynomial, never an untruncated product-space
exponential. Norm bounds and covariance supersolutions are separate modules.
-/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BilayerDressed.PositiveEntryOrder
/-- Entrywise order, explicitly separate from the scoped Loewner matrix order. -/
scoped instance {σ τ : Type*} : PartialOrder (Matrix σ τ ℝ) :=
  inferInstanceAs (PartialOrder (σ → τ → ℝ))
end BilayerDressed.PositiveEntryOrder
open scoped BilayerDressed.PositiveEntryOrder
namespace BilayerDressed.PositiveMatrix
open Matrix
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 theorem mul_nonneg (A B : Matrix σ σ ℝ) (hA : 0≤A) (hB : 0≤B) : 0≤A*B := by
  intro u v
  exact Finset.sum_nonneg fun k _ => _root_.mul_nonneg (hA u k) (hB k v)

 theorem mul_le_mul_left (A B C : Matrix σ σ ℝ) (hA : 0≤A) (hBC : B≤C) :
    A*B≤A*C := by
  intro u v
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hBC k v) (hA u k)

 theorem mul_le_mul_right (A B C : Matrix σ σ ℝ) (hC : 0≤C) (hAB : A≤B) :
    A*C≤B*C := by
  intro u v
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hAB u k) (hC k v)

 theorem mulVec_nonneg (A : Matrix σ σ ℝ) (hA : 0≤A) (v : σ→ℝ) (hv : 0≤v) :
    0≤A.mulVec v := by
  intro u
  exact Finset.sum_nonneg fun k _ => _root_.mul_nonneg (hA u k) (hv k)

 theorem mulVec_le_mulVec (A : Matrix σ σ ℝ) (hA : 0≤A)
    (v w : σ→ℝ) (hvw : v≤w) : A.mulVec v≤A.mulVec w := by
  intro u
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hvw k) (hA u k)

 theorem mulVec_le_mulVec_of_matrix (A B : Matrix σ σ ℝ) (hAB : A≤B)
    (v : σ→ℝ) (hv : 0≤v) : A.mulVec v≤B.mulVec v := by
  intro u
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hAB u k) (hv k)

 theorem pow_nonneg (S : Matrix σ σ ℝ) (hS : 0≤S) (k : ℕ) : 0≤S^k := by
  induction k with
  | zero => intro u v; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih => simpa only [pow_succ] using mul_nonneg (S^k) S ih hS

/-- Finite Taylor polynomial, with truncation order independent of nilpotence. -/
def taylor (S : Matrix σ σ ℝ) (n : ℕ) : Matrix σ σ ℝ :=
  ∑ k ∈ Finset.range (n+1), (1/(k.factorial : ℝ)) • S^k

 theorem taylor_nonneg (S : Matrix σ σ ℝ) (hS : 0≤S) (n : ℕ) : 0≤taylor S n := by
  intro u v
  simp only [taylor,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact Finset.sum_nonneg fun k _ => _root_.mul_nonneg (by positivity) (pow_nonneg S hS k u v)

/-- A one-step entrywise derivative bound propagates to every power. -/
theorem derivative_power_le (A S T : Matrix σ σ ℝ) (hS : 0≤S)
    (hAS : A*S≤S*A+T) (hTS : Commute T S) (n : ℕ) :
    A*S^(n+1)≤S^(n+1)*A+((n+1 : ℕ) : ℝ) • (T*S^n) := by
  induction n with
  | zero => simpa using hAS
  | succ n ih =>
    calc
      A*S^(n+1+1)=(A*S^(n+1))*S := by rw [pow_succ]; simp only [mul_assoc]
      _ ≤ (S^(n+1)*A+((n+1 : ℕ) : ℝ) • (T*S^n))*S :=
        mul_le_mul_right _ _ _ hS ih
      _ = S^(n+1)*(A*S)+((n+1 : ℕ) : ℝ) • (T*S^(n+1)) := by
        simp only [add_mul,Matrix.smul_mul,mul_assoc,pow_succ]
      _ ≤ S^(n+1)*(S*A+T)+((n+1 : ℕ) : ℝ) • (T*S^(n+1)) := by
        intro u v
        exact add_le_add_right (mul_le_mul_left _ _ _ (pow_nonneg S hS _) hAS u v) _
      _ = S^(n+1+1)*A+((n+1+1 : ℕ) : ℝ) • (T*S^(n+1)) := by
        rw [mul_add,← mul_assoc,← pow_succ,← (hTS.pow_right (n+1)).eq]
        push_cast
        module

/-- Finite Taylor differentiation, with the last positive term not yet added. -/
theorem derivative_taylor_succ_le (A S T : Matrix σ σ ℝ) (hS : 0≤S)
    (hAS : A*S≤S*A+T) (hTS : Commute T S) (n : ℕ) :
    A*taylor S (n+1)≤taylor S (n+1)*A+T*taylor S n := by
  have hc (k : ℕ) : (1/(((k+1).factorial : ℕ) : ℝ))*((k+1 : ℕ) : ℝ)=
      1/(k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    have hk : (k : ℝ)+1≠0 := by positivity
    have hf : (k.factorial : ℝ)≠0 := by positivity
    field_simp
  have ht : taylor S (n+1)=1+∑ k∈Finset.range (n+1),
      (1/(((k+1).factorial : ℕ) : ℝ)) • S^(k+1) := by
    rw [taylor,Finset.sum_range_succ']
    simp [add_comm]
  rw [ht,mul_add,mul_one]
  calc
    A+A*(∑ k∈Finset.range (n+1), (1/(((k+1).factorial : ℕ) : ℝ)) • S^(k+1))
      ≤ A+∑ k∈Finset.range (n+1), (1/(((k+1).factorial : ℕ) : ℝ)) •
        (S^(k+1)*A+((k+1 : ℕ) : ℝ) • (T*S^k)) := by
      intro u v
      simp only [Matrix.add_apply,Matrix.mul_sum,Matrix.mul_smul,Matrix.sum_apply,
        Matrix.smul_apply,smul_eq_mul]
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (derivative_power_le A S T hS hAS hTS k u v)
        (by positivity)
    _ = _ := by
      simp only [smul_add,smul_smul,hc,Finset.sum_add_distrib,add_mul,one_mul,
        Matrix.sum_mul,Matrix.smul_mul,taylor,Matrix.mul_sum,Matrix.mul_smul]
      abel

/-- Taylor polynomials increase entrywise for a positive matrix. -/
theorem taylor_le_succ (S : Matrix σ σ ℝ) (hS : 0≤S) (n : ℕ) :
    taylor S n≤taylor S (n+1) := by
  intro u v
  simp only [taylor,Finset.sum_range_succ,Matrix.add_apply]
  exact le_add_of_nonneg_right (_root_.mul_nonneg (by positivity)
    (pow_nonneg S hS (n+1) u v))

/-- A finite positive Taylor vector satisfies the annihilation domination. -/
theorem annihilate_taylor_vacuum_le (A S T : Matrix σ σ ℝ)
    (hS : 0≤S) (hT : 0≤T) (hAS : A*S≤S*A+T) (hTS : Commute T S)
    (Ω : σ→ℝ) (hΩ : 0≤Ω) (hAΩ : A.mulVec Ω=0) (n : ℕ) :
    A.mulVec ((taylor S n).mulVec Ω)≤T.mulVec ((taylor S n).mulVec Ω) := by
  cases n with
  | zero =>
    simpa [taylor,hAΩ] using mulVec_nonneg T hT Ω hΩ
  | succ n =>
    have hh := mulVec_le_mulVec_of_matrix _ _
      (derivative_taylor_succ_le A S T hS hAS hTS n) Ω hΩ
    simp only [Matrix.add_mulVec,← Matrix.mulVec_mulVec,hAΩ,Matrix.mulVec_zero,zero_add] at hh
    exact hh.trans (mulVec_le_mulVec T hT _ _
      (mulVec_le_mulVec_of_matrix _ _ (taylor_le_succ S hS n) Ω hΩ))

/-- A literal ordered creation word. -/
def word {ι : Type*} (C : ι→Matrix σ σ ℝ) : List ι→Matrix σ σ ℝ
  | [] => 1
  | j::l => C j*word C l

 theorem word_nonneg {ι : Type*} (C : ι→Matrix σ σ ℝ) (hC : ∀ i,0≤C i) :
    ∀ l, 0≤word C l
  | [] => by intro u v; simp only [word,Matrix.one_apply]; split_ifs <;> norm_num
  | j::l => mul_nonneg (C j) (word C l) (hC j) (word_nonneg C hC l)

/-- Algebraic derivative of a word. Each occurrence, including repeats, is counted. -/
def derivative {ι : Type*} [DecidableEq ι] (C : ι→Matrix σ σ ℝ)
    (i : ι) : List ι→Matrix σ σ ℝ
  | [] => 0
  | j::l => (if i=j then word C l else 0) + C j*derivative C i l

/-- Entrywise CCR upper bounds imply the corresponding upper bound for every word. -/
theorem annihilate_word_le {ι : Type*} [DecidableEq ι]
    (C A : ι→Matrix σ σ ℝ) (hC : ∀ i,0≤C i)
    (hCCR : ∀ i j, A i*C j≤C j*A i+(if i=j then 1 else 0)) :
    ∀ i l, A i*word C l≤word C l*A i+derivative C i l := by
  intro i l
  induction l with
  | nil => simp [word,derivative]
  | cons j l ih =>
    calc
      A i*word C (j::l)=(A i*C j)*word C l := by simp only [word,mul_assoc]
      _ ≤ (C j*A i+(if i=j then 1 else 0))*word C l :=
        mul_le_mul_right _ _ _ (word_nonneg C hC l) (hCCR i j)
      _ = C j*(A i*word C l)+(if i=j then word C l else 0) := by
        by_cases hij : i=j <;> simp [hij,add_mul,mul_assoc]
      _ ≤ C j*(word C l*A i+derivative C i l)+(if i=j then word C l else 0) :=
        by
          intro u v
          exact add_le_add_right (mul_le_mul_left _ _ _ (hC j) ih u v) _
      _ = word C (j::l)*A i+derivative C i (j::l) := by
        simp only [word,derivative,mul_add,mul_assoc]
        abel

/-- Unnormalized quadratic expectation. -/
def expect (ψ : σ→ℝ) (X : Matrix σ σ ℝ) : ℝ := dotProduct ψ (X.mulVec ψ)

theorem expect_mono (ψ : σ→ℝ) (hψ : 0≤ψ) (X Y : Matrix σ σ ℝ) (hXY : X≤Y) :
    expect ψ X≤expect ψ Y :=
  dotProduct_le_dotProduct_of_nonneg_left (mulVec_le_mulVec_of_matrix X Y hXY ψ hψ) hψ

theorem expect_nonneg (ψ : σ→ℝ) (hψ : 0≤ψ) (X : Matrix σ σ ℝ) (hX : 0≤X) :
    0≤expect ψ X := dotProduct_nonneg_of_nonneg hψ (mulVec_nonneg X hX ψ hψ)

@[simp] theorem expect_add (ψ : σ→ℝ) (X Y : Matrix σ σ ℝ) :
    expect ψ (X+Y)=expect ψ X+expect ψ Y := by
  simp [expect,Matrix.add_mulVec,dotProduct_add]

@[simp] theorem expect_smul (ψ : σ→ℝ) (c : ℝ) (X : Matrix σ σ ℝ) :
    expect ψ (c • X)=c*expect ψ X := by
  simp [expect,Matrix.smul_mulVec,dotProduct_smul]

@[simp] theorem expect_sum {ι : Type*} (ψ : σ→ℝ) (s : Finset ι) (X : ι→Matrix σ σ ℝ) :
    expect ψ (∑ i∈s,X i)=∑ i∈s,expect ψ (X i) := by
  simp [expect,Matrix.sum_mulVec,dotProduct_sum]

 theorem expect_left_transpose (ψ : σ→ℝ) (X Y : Matrix σ σ ℝ) :
    expect ψ (X*Y)=dotProduct (X.transpose.mulVec ψ) (Y.mulVec ψ) := by
  simp only [expect,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

 theorem dot_create (ψ v : σ→ℝ) (C : Matrix σ σ ℝ) :
    dotProduct (C.mulVec ψ) v=dotProduct ψ (C.transpose.mulVec v) := by
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

 theorem word_commute {ι : Type*} (C : ι→Matrix σ σ ℝ)
    (hC : ∀ i j,Commute (C i) (C j)) (i : ι) : ∀ l,Commute (C i) (word C l)
  | [] => Commute.one_right _
  | j::l => (hC i j).mul_right (word_commute C hC i l)

/-- Removing an occurrence records the word derivative without assuming distinct labels. -/
theorem derivative_eq_sum_eraseIdx {ι : Type*} [DecidableEq ι]
    (C : ι→Matrix σ σ ℝ) (i : ι) (l : List ι) :
    derivative C i l=∑ a : Fin l.length,
      if i=l[a] then word C (l.eraseIdx a.val) else 0 := by
  induction l with
  | nil => simp [derivative]
  | cons j l ih =>
    rw [derivative,ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.getElem_cons_zero,List.eraseIdx_cons_zero,Fin.val_zero,
      List.getElem_cons_succ,Fin.val_succ,List.eraseIdx_cons_succ,word]
    rw [Matrix.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> first | rfl | simp_all

/-- The weighted derivative is exactly the sum over removed occurrences. -/
theorem weighted_derivative_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι→Matrix σ σ ℝ) (b : ι→ℝ) (ψ : σ→ℝ) (l : List ι) :
    (∑ k,b k*expect ψ (derivative C k l))=
      ∑ a : Fin l.length,b l[a]*expect ψ (word C (l.eraseIdx a.val)) := by
  simp only [derivative_eq_sum_eraseIdx,expect_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have he (k : ι) : expect ψ (if k=l[a] then word C (l.eraseIdx a.val) else 0)=
      if k=l[a] then expect ψ (word C (l.eraseIdx a.val)) else 0 := by
    split_ifs <;> simp [expect]
  simp only [he,mul_ite,mul_zero]
  simp

end BilayerDressed.PositiveMatrix

namespace BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem create_nonneg {M N : ℕ} (i : Mode V) :
    0≤(create (M := M) (N := N) i : Op V M N) := by
  classical
  intro ν μ
  change 0≤(if FiniteOccupation.Raises i ν.val μ.val then Real.sqrt _ else 0)
  split_ifs <;> positivity

 theorem annihilate_nonneg {M N : ℕ} (i : Mode V) :
    0≤(annihilate (M := M) (N := N) i : Op V M N) :=
  fun ν μ => create_nonneg i μ ν

/-- True global finite CCR upper inequality. The top defect has the correct sign. -/
theorem annihilate_create_le {M N : ℕ} (hNM : N≤M) (i j : Mode V) :
    annihilate (M := M) (N := N) i*create j ≤
      create j*annihilate i+(if i=j then 1 else 0) := by
  intro ν μ
  by_cases htop : totalDegree μ.val=N
  · have he := commutator_top_entry (M := M) (N := N) i j ν μ htop
    have hp := PositiveMatrix.mul_nonneg (create (M := M) (N := N) j)
      (annihilate i) (create_nonneg j) (annihilate_nonneg i) ν μ
    change (0 : ℝ)≤((create j*annihilate i : Op V M N) ν μ) at hp
    have hδ : 0≤(if i=j then (1 : Op V M N) else 0) ν μ := by
      by_cases hij : i=j <;> by_cases hνμ : ν=μ <;> simp [hij,hνμ,Matrix.one_apply]
    simp only [Matrix.sub_apply] at he
    change _≤_+(if i=j then (1 : Op V M N) else 0) ν μ
    linarith
  · have hs : totalDegree μ.val<N := lt_of_le_of_ne μ.property htop
    have he := commutator_safe_entry hNM i j ν μ hs
    change _≤_+(if i=j then (1 : Op V M N) else 0) ν μ
    simp only [Matrix.sub_apply] at he
    by_cases hij : i=j <;> by_cases hνμ : ν=μ <;>
      simp [hij,hνμ,Matrix.one_apply] at he ⊢ <;> linarith

/-- The previous word inequality now uses only actual finite creation matrices. -/
theorem actual_annihilate_word_le {M N : ℕ} (hNM : N≤M) (i : Mode V) (l : List (Mode V)) :
    annihilate (M := M) (N := N) i*PositiveMatrix.word create l ≤
      PositiveMatrix.word create l*annihilate i+PositiveMatrix.derivative create i l :=
  PositiveMatrix.annihilate_word_le create annihilate create_nonneg
    (annihilate_create_le hNM) i l

/-- The linear creator in the i-th row of the actual pair kernel. -/
def linearCreate {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (i : Mode V) : Op V M N :=
  ∑ j, B i j • create j

 theorem pairCreate_nonneg {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j,0≤B i j) : 0≤(Pair.pairCreate B : Op V M N) := by
  intro ν μ
  simp only [Pair.pairCreate,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  apply _root_.mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact _root_.mul_nonneg (hB i j)
    (PositiveMatrix.mul_nonneg (create i) (create j) (create_nonneg i) (create_nonneg j) ν μ)

 theorem linearCreate_nonneg {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j,0≤B i j) (i : Mode V) : 0≤(linearCreate B i : Op V M N) := by
  intro ν μ
  simp only [linearCreate,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact Finset.sum_nonneg fun j _ => _root_.mul_nonneg (hB i j) (create_nonneg j ν μ)

 theorem create_pair_commute {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (i : Mode V) :
    Commute (create (M := M) (N := N) i) (Pair.pairCreate B) := by
  unfold Pair.pairCreate
  apply Commute.smul_right
  apply Commute.sum_right
  intro j _
  apply Commute.sum_right
  intro k _
  exact ((create_commute (M := M) (N := N) i j).mul_right (create_commute i k)).smul_right (B j k)

 theorem linear_pair_commute {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (i : Mode V) :
    Commute (linearCreate (M := M) (N := N) B i) (Pair.pairCreate B) := by
  unfold linearCreate
  apply Commute.sum_left
  intro j _
  exact (create_pair_commute B j).smul_left (B i j)

/-- Actual global pair inequality, including all finite-cutoff boundary terms. -/
theorem annihilate_pair_le {M N : ℕ} (hNM : N≤M)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (i : Mode V) :
    annihilate (M := M) (N := N) i*Pair.pairCreate B ≤
      Pair.pairCreate B*annihilate i+linearCreate B i := by
  have ht (j k : Mode V) :
      annihilate (M := M) (N := N) i*(create j*create k) ≤
        (create j*create k)*annihilate i+(if i=j then create k else 0)+
          (if i=k then create j else 0) := by
    have hh := actual_annihilate_word_le hNM i [j,k]
    simpa [PositiveMatrix.word,PositiveMatrix.derivative,mul_ite,add_assoc] using hh
  have hd1 : (∑ j,∑ k, B j k • (if i=j then (create (M := M) (N := N) k) else 0))=
      linearCreate B i := by
    rw [Finset.sum_comm]
    simp [linearCreate,smul_ite]
  have hd2 : (∑ j,∑ k, B j k • (if i=k then (create (M := M) (N := N) j) else 0))=
      linearCreate B i := by
    simp [linearCreate,smul_ite,hsym]
  calc
    _ = (1/2 : ℝ) • ∑ j,∑ k, B j k •
        (annihilate (M := M) (N := N) i*(create j*create k)) := by
      simp [Pair.pairCreate,Matrix.mul_smul,Matrix.mul_sum]
    _ ≤ (1/2 : ℝ) • ∑ j,∑ k, B j k •
        ((create (M := M) (N := N) j*create k)*annihilate i+
          (if i=j then create k else 0)+(if i=k then create j else 0)) := by
      intro ν μ
      simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (ht j k ν μ) (hB j k)
    _ = _ := by
      simp only [smul_add,Finset.sum_add_distrib]
      rw [hd1,hd2]
      simp only [Pair.pairCreate,Matrix.smul_mul,Matrix.sum_mul,smul_add]
      module

/-- Explicit finite state used for Wick bounds; no full exponential is substituted. -/
def pairState {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (n : ℕ) : Basis V M N→ℝ :=
  (PositiveMatrix.taylor (Pair.pairCreate B) n).mulVec (Pi.single vacuum 1)

theorem pairState_nonneg {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j,0≤B i j) (n : ℕ) : 0≤(pairState (M := M) (N := N) B n) := by
  apply PositiveMatrix.mulVec_nonneg _ (PositiveMatrix.taylor_nonneg _ (pairCreate_nonneg B hB) n)
  intro ν
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

/-- Domination for the literal finite pair state, with the top defect retained. -/
theorem annihilate_pairState_le {M N : ℕ} (hNM : N≤M)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (n : ℕ) (i : Mode V) :
    (annihilate i).mulVec (pairState (M := M) (N := N) B n)≤
      (linearCreate B i).mulVec (pairState B n) := by
  apply PositiveMatrix.annihilate_taylor_vacuum_le
    (annihilate i) (Pair.pairCreate B) (linearCreate B i)
    (pairCreate_nonneg B hB) (linearCreate_nonneg B hB i)
    (annihilate_pair_le hNM B hB hsym i) (linear_pair_commute B i)
  · intro ν
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · exact annihilate_vacuum_vector i

/-- Actual moment recurrence in derivative form, before the finite max principle. -/
theorem state_moment_recurrence {M N : ℕ} (hNM : N≤M)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (ψ : Basis V M N→ℝ) (hψ : 0≤ψ)
    (hdom : ∀ i,(annihilate i).mulVec ψ≤(linearCreate B i).mulVec ψ)
    (i : Mode V) (l : List (Mode V)) :
    PositiveMatrix.expect ψ (create i*PositiveMatrix.word create l)≤
      (∑ k,B i k*PositiveMatrix.expect ψ (PositiveMatrix.derivative create k l))+
      ∑ j,(B*B) i j*PositiveMatrix.expect ψ (create j*PositiveMatrix.word create l) := by
  let W : Op V M N := PositiveMatrix.word create l
  have hW : 0≤W := PositiveMatrix.word_nonneg create create_nonneg l
  have hleft : PositiveMatrix.expect ψ (create i*W)≤
      ∑ k,B i k*PositiveMatrix.expect ψ (annihilate k*W) := by
    rw [PositiveMatrix.expect_left_transpose]
    change dotProduct ((annihilate i).mulVec ψ) (W.mulVec ψ)≤_
    calc
      _ ≤ dotProduct ((linearCreate B i).mulVec ψ) (W.mulVec ψ) :=
        dotProduct_le_dotProduct_of_nonneg_right (hdom i)
          (PositiveMatrix.mulVec_nonneg W hW ψ hψ)
      _ = _ := by
        simp only [linearCreate,Matrix.sum_mulVec,Matrix.smul_mulVec,sum_dotProduct,
          smul_dotProduct,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [PositiveMatrix.dot_create]
        simp only [PositiveMatrix.expect,← Matrix.mulVec_mulVec,annihilate]
  have hright (k : Mode V) : PositiveMatrix.expect ψ (annihilate k*W)≤
      PositiveMatrix.expect ψ (PositiveMatrix.derivative create k l)+
        ∑ j,B k j*PositiveMatrix.expect ψ (create j*W) := by
    calc
      _ ≤ PositiveMatrix.expect ψ (W*annihilate k+PositiveMatrix.derivative create k l) :=
        PositiveMatrix.expect_mono ψ hψ _ _ (actual_annihilate_word_le hNM k l)
      _ = PositiveMatrix.expect ψ (W*annihilate k)+
            PositiveMatrix.expect ψ (PositiveMatrix.derivative create k l) :=
        PositiveMatrix.expect_add _ _ _
      _ ≤ PositiveMatrix.expect ψ (W*linearCreate B k)+
            PositiveMatrix.expect ψ (PositiveMatrix.derivative create k l) := by
        apply add_le_add_right
        apply dotProduct_le_dotProduct_of_nonneg_left _ hψ
        simpa only [← Matrix.mulVec_mulVec] using
          PositiveMatrix.mulVec_le_mulVec W hW _ _ (hdom k)
      _ = _ := by
        simp only [linearCreate,Matrix.mul_sum,Matrix.mul_smul,PositiveMatrix.expect_sum,
          PositiveMatrix.expect_smul]
        have he : (∑ j,B k j*PositiveMatrix.expect ψ (W*create j))=
            ∑ j,B k j*PositiveMatrix.expect ψ (create j*W) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← (PositiveMatrix.word_commute create create_commute j l).eq]
        rw [he]
        exact add_comm _ _
  refine hleft.trans ?_
  calc
    (∑ k,B i k*PositiveMatrix.expect ψ (annihilate k*W))
      ≤ ∑ k,B i k*(PositiveMatrix.expect ψ (PositiveMatrix.derivative create k l)+
          ∑ j,B k j*PositiveMatrix.expect ψ (create j*W)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hright k) (hB i k)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,Matrix.mul_apply,Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The recurrence now applies to the literal finite pair-state, with no moment oracle. -/
theorem pairState_moment_recurrence {M N : ℕ} (hNM : N≤M)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (n : ℕ) (i : Mode V) (l : List (Mode V)) :
    PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (create i*PositiveMatrix.word create l)≤
      (∑ k,B i k*PositiveMatrix.expect (pairState (M := M) (N := N) B n) (PositiveMatrix.derivative create k l))+
      ∑ j,(B*B) i j*PositiveMatrix.expect (pairState (M := M) (N := N) B n) (create j*PositiveMatrix.word create l) :=
  state_moment_recurrence hNM B hB _ (pairState_nonneg B hB n)
    (annihilate_pairState_le hNM B hB hsym n) i l

/-- The literal finite-state recurrence, with every deleted occurrence displayed. -/
theorem pairState_moment_recurrence_positions {M N : ℕ} (hNM : N≤M)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (n : ℕ) (i : Mode V) (l : List (Mode V)) :
    PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (create i*PositiveMatrix.word create l)≤
      (∑ a : Fin l.length,B i l[a]*PositiveMatrix.expect (pairState (M := M) (N := N) B n)
        (PositiveMatrix.word create (l.eraseIdx a.val)))+
      ∑ j,(B*B) i j*PositiveMatrix.expect (pairState (M := M) (N := N) B n)
        (create j*PositiveMatrix.word create l) := by
  have h := pairState_moment_recurrence (M := M) (N := N) hNM B hB hsym n i l
  rw [PositiveMatrix.weighted_derivative_expect] at h
  exact h

/-- The actual moment recurrence closes against any certified covariance supersolution. -/
theorem pairState_wick_step {M N : ℕ} (hNM : N≤M)
    (B L : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (q : ℝ) (hq : q<1)
    (hrow : ∀ i,∑ j,(B*B) i j≤q)
    (hL : ∀ i j,B i j+((B*B)*L) i j≤L i j)
    (n : ℕ) (i : Mode V) (l : List (Mode V)) :
    PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (PositiveMatrix.word create (i::l))≤
      ∑ a : Fin l.length,L i l[a]*PositiveMatrix.expect (pairState (M := M) (N := N) B n)
        (PositiveMatrix.word create (l.eraseIdx a.val)) := by
  exact FiniteWick.weighted_column_comparison B L q hB hq hrow hL
    (fun a : Fin l.length => l[a])
    (fun a => PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (PositiveMatrix.word create (l.eraseIdx a.val)))
    (fun a => PositiveMatrix.expect_nonneg _ (pairState_nonneg B hB n) _
      (PositiveMatrix.word_nonneg create create_nonneg _))
    (fun j => PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (create j*PositiveMatrix.word create l))
    (fun j => pairState_moment_recurrence_positions hNM B hB hsym n j l) i

end BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
