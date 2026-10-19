import Dressed.FiniteWickPairings

/-! Entrywise absolute-value comparison for genuine finite signed trial states.
These inequalities are independent of Gaussian terminology and use only
finite sums, nonnegative matrix entries, and an injective basis inclusion.
-/
noncomputable section
open scoped BigOperators BilayerDressed.PositiveEntryOrder
namespace BilayerDressed.PositiveMatrix
open Matrix
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Entrywise domination is explicit; no default matrix operator order is used. -/
def entryAbs {ρ τ : Type*} (A : Matrix ρ τ ℝ) : Matrix ρ τ ℝ := fun i j => |A i j|

def AbsLE {ρ τ : Type*} (A B : Matrix ρ τ ℝ) : Prop := ∀ i j,|A i j|≤B i j

 theorem absLE_nonneg {ρ τ : Type*} {A B : Matrix ρ τ ℝ} (h : AbsLE A B) :
    ∀ i j,0≤B i j := fun i j => (abs_nonneg _).trans (h i j)

 theorem absLE_mul (A B C D : Matrix σ σ ℝ) (hAC : AbsLE A C) (hBD : AbsLE B D) :
    AbsLE (A*B) (C*D) := by
  intro i j
  calc
    |(A*B) i j|≤∑ k,|A i k*B k j| := by simpa [Matrix.mul_apply] using Finset.abs_sum_le_sum_abs (fun k => A i k*B k j) Finset.univ
    _ ≤ ∑ k,C i k*D k j := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hAC i k) (hBD k j) (abs_nonneg _) (absLE_nonneg hAC i k)
    _ = _ := rfl

 theorem absLE_pow (S T : Matrix σ σ ℝ) (hST : AbsLE S T) (n : ℕ) :
    AbsLE (S^n) (T^n) := by
  induction n with
  | zero => intro i j; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih => simpa only [pow_succ] using absLE_mul _ _ _ _ ih hST

 theorem absLE_taylor (S T : Matrix σ σ ℝ) (hST : AbsLE S T) (n : ℕ) :
    AbsLE (taylor S n) (taylor T n) := by
  intro i j
  simp only [taylor,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤1/(k.factorial : ℝ))]
  exact mul_le_mul_of_nonneg_left (absLE_pow S T hST k i j) (by positivity)

 theorem abs_mulVec_le (A B : Matrix σ σ ℝ) (hAB : AbsLE A B)
    (v w : σ→ℝ) (hvw : ∀ i,|v i|≤w i) : ∀ i,|(A.mulVec v) i|≤(B.mulVec w) i := by
  intro i
  change |∑ j,A i j*v j|≤∑ j,B i j*w j
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul (hAB i j) (hvw j) (abs_nonneg _) (absLE_nonneg hAB i j)

 theorem abs_dotProduct_le (u v U V : σ→ℝ)
    (hu : ∀ i,|u i|≤U i) (hv : ∀ i,|v i|≤V i) :
    |dotProduct u v|≤dotProduct U V := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul (hu i) (hv i) (abs_nonneg _) ((abs_nonneg _).trans (hu i))

 theorem abs_expect_le (v w : σ→ℝ) (hvw : ∀ i,|v i|≤w i)
    (A B : Matrix σ σ ℝ) (hAB : AbsLE A B) : |expect v A|≤expect w B :=
  abs_dotProduct_le v (A.mulVec v) w (B.mulVec w) hvw (abs_mulVec_le A B hAB v w hvw)

/-- Restricting nonnegative products to an injected subset can only lower their sum. -/
theorem injected_dotProduct_le {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (e : ρ→σ) (he : Function.Injective e) (U V : σ→ℝ) (hU : 0≤U) (hV : 0≤V) :
    (∑ i,U (e i)*V (e i))≤dotProduct U V := by
  have hh : (∑ i,U (e i)*V (e i))=∑ j∈Finset.univ.image e,U j*V j := by
    symm
    exact Finset.sum_image (fun _ _ _ _ h => he h)
  rw [hh]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => _root_.mul_nonneg (hU i) (hV i))

/-- This is the signed physical projection mean bound used after exact compression. -/
theorem projected_abs_dotProduct_le {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (e : ρ→σ) (he : Function.Injective e) (u v : ρ→ℝ) (U V : σ→ℝ)
    (hu : ∀ i,|u i|≤U (e i)) (hv : ∀ i,|v i|≤V (e i))
    (hU : 0≤U) (hV : 0≤V) : |dotProduct u v|≤dotProduct U V := by
  exact (abs_dotProduct_le u v (fun i => U (e i)) (fun i => V (e i)) hu hv).trans
    (injected_dotProduct_le e he U V hU hV)

/-- A literal finite creation polynomial, with arbitrary repeated labels. -/
def creationPolynomial {ι α : Type*} [Fintype α]
    (C : ι→Matrix σ σ ℝ) (c : α→ℝ) (w : α→List ι) : Matrix σ σ ℝ :=
  ∑ a,c a • word C (w a)

 theorem creationPolynomial_absLE {ι α : Type*} [Fintype α]
    (C : ι→Matrix σ σ ℝ) (hC : ∀ i,0≤C i) (c : α→ℝ) (w : α→List ι) :
    AbsLE (creationPolynomial C c w) (creationPolynomial C (fun a => |c a|) w) := by
  intro i j
  simp only [creationPolynomial,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul,abs_of_nonneg (word_nonneg C hC (w a) i j)]

end BilayerDressed.PositiveMatrix

namespace BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Taking absolute kernel entries dominates the actual finite pair creator. -/
theorem pairCreate_absLE {M N : ℕ} (K : Matrix (Mode V) (Mode V) ℝ) :
    PositiveMatrix.AbsLE (Pair.pairCreate K : Op V M N)
      (Pair.pairCreate (fun i j => |K i j|)) := by
  intro ν μ
  simp only [Pair.pairCreate,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul,abs_of_nonneg
    (PositiveMatrix.mul_nonneg (create i) (create j) (create_nonneg i) (create_nonneg j) ν μ)]

/-- The same inclusive finite Taylor state is dominated componentwise. -/
theorem pairState_abs_le {M N : ℕ} (K : Matrix (Mode V) (Mode V) ℝ) (n : ℕ) :
    ∀ ν,|pairState (M := M) (N := N) K n ν|≤pairState (fun i j => |K i j|) n ν := by
  apply PositiveMatrix.abs_mulVec_le _ _
    (PositiveMatrix.absLE_taylor _ _ (pairCreate_absLE K) n)
  intro ν
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

/-- Polynomial actions are dominated with both state and coefficient signs removed. -/
theorem pairState_polynomial_abs_le {M N : ℕ} {α : Type*} [Fintype α]
    (K : Matrix (Mode V) (Mode V) ℝ) (n : ℕ) (c : α→ℝ) (w : α→List (Mode V)) :
    ∀ ν,|((PositiveMatrix.creationPolynomial create c w).mulVec
      (pairState (M := M) (N := N) K n)) ν|≤
      ((PositiveMatrix.creationPolynomial create (fun a => |c a|) w).mulVec
        (pairState (fun i j => |K i j|) n)) ν :=
  PositiveMatrix.abs_mulVec_le _ _
    (PositiveMatrix.creationPolynomial_absLE create create_nonneg c w) _ _ (pairState_abs_le K n)

/-- Positive finite polynomial expectations close using actual finite Wick bounds. -/
theorem pairState_polynomial_wick_bound {M N : ℕ} {α : Type*} [Fintype α]
    (hNM : N≤M) (B L : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (hL0 : ∀ i j,0≤L i j)
    (q : ℝ) (hq : q<1) (hrow : ∀ i,∑ j,(B*B) i j≤q)
    (hL : ∀ i j,B i j+((B*B)*L) i j≤L i j)
    (n : ℕ) (c : α→ℝ) (hc : ∀ a,0≤c a) (w : α→List (Mode V)) :
    PositiveMatrix.expect (pairState (M := M) (N := N) B n)
      (PositiveMatrix.creationPolynomial create c w)≤
      dotProduct (pairState (M := M) (N := N) B n) (pairState (M := M) (N := N) B n)*
        ∑ a,c a*FiniteWickPairings.wick L (w a) := by
  simp only [PositiveMatrix.creationPolynomial,PositiveMatrix.expect_sum,PositiveMatrix.expect_smul,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_left
    (pairState_wick_bound hNM B L hB hsym hL0 q hq hrow hL n (w a)) (hc a)
  exact h.trans_eq (by ring)

/-- Signed trial and residual restricted to any injected physical basis are bounded
by the full positive finite-state Wick expression. Exact physical compression
identifies the left side in a separate algebraic module. -/
theorem injected_pairState_polynomial_mean_bound {M N : ℕ}
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq ρ]
    (hNM : N≤M) (K L : Matrix (Mode V) (Mode V) ℝ)
    (hsym : ∀ i j,K i j=K j i) (hL0 : ∀ i j,0≤L i j)
    (q : ℝ) (hq : q<1)
    (hrow : ∀ i,∑ j,(PositiveMatrix.entryAbs K*PositiveMatrix.entryAbs K) i j≤q)
    (hL : ∀ i j,|K i j|+((PositiveMatrix.entryAbs K*PositiveMatrix.entryAbs K)*L) i j≤L i j)
    (n : ℕ) (c : α→ℝ) (w : α→List (Mode V))
    (e : ρ→Basis V M N) (he : Function.Injective e) :
    |dotProduct (fun s => pairState (M := M) (N := N) K n (e s))
      (fun s => ((PositiveMatrix.creationPolynomial create c w).mulVec (pairState K n)) (e s))|≤
      dotProduct (pairState (M := M) (N := N) (fun i j => |K i j|) n)
        (pairState (M := M) (N := N) (fun i j => |K i j|) n)*
        ∑ a,|c a| *FiniteWickPairings.wick L (w a) := by
  let B : Matrix (Mode V) (Mode V) ℝ := fun i j => |K i j|
  let ψ := pairState (M := M) (N := N) B n
  let P : Op V M N := PositiveMatrix.creationPolynomial create (fun a => |c a|) w
  have hψ : 0≤ψ := pairState_nonneg B (fun _ _ => abs_nonneg _) n
  have hP : 0≤P := PositiveMatrix.absLE_nonneg
    (PositiveMatrix.creationPolynomial_absLE create create_nonneg c w)
  have hproj := PositiveMatrix.projected_abs_dotProduct_le e he
    (fun s => pairState (M := M) (N := N) K n (e s))
    (fun s => ((PositiveMatrix.creationPolynomial create c w).mulVec (pairState K n)) (e s))
    ψ (P.mulVec ψ)
    (fun s => pairState_abs_le K n (e s))
    (fun s => pairState_polynomial_abs_le K n c w (e s))
    hψ (PositiveMatrix.mulVec_nonneg P hP ψ hψ)
  exact hproj.trans (pairState_polynomial_wick_bound hNM B L
    (fun _ _ => abs_nonneg _) (fun i j => congrArg abs (hsym i j)) hL0 q hq hrow hL
    n (fun a => |c a|) (fun _ => abs_nonneg _) w)

end BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
