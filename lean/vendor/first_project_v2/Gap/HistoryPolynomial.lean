import Gap.HistoryTransfer
import Gap.HistoryEuler

/-!
# The finite matching polynomial behind the discrete transfer

Factoring the local square-root weights produces two endpoint factors for
every event, exactly. Thus the physical one-step operator is a polynomial in
the time step, even though its symmetric spatial factorization uses square
roots. Colliding histories vanish identically; no limit of their weights is
assumed or needed.
-/
noncomputable section
namespace BilayerGap.History
open scoped BigOperators
open Polynomial

/-- A bond carries either zero or one event in a single time slot. -/
def occupation {B : Type*} : Option B → ℕ
  | none => 0
  | some _ => 1

/-- Polynomial local factor after removing the endpoint square-root weights. -/
def vertexPolynomial {V B : Type*} [DecidableEq V]
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) :
    Option B → Option B → Matrix V V ℝ[X]
  | none, none => fun i j => C ((1 : Matrix V V ℝ) i j)-X*C (h i j)
  | some a, none => fun i j => C (G a i j)
  | none, some b => fun i j => C (G b i j)
  | some _, some _ => 0

/-- Pointwise factorization, also valid for collisions since both sides vanish. -/
theorem collisionVertex_eq_weight_eval {V B : Type*} [Fintype V] [DecidableEq V]
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (δ g : ℝ)
    (x y : Option B) (i j : V) :
    collisionVertex h G δ g x y i j =
      Real.sqrt (δ*g)^(occupation x+occupation y)*
        (vertexPolynomial h G x y i j).eval δ := by
  cases x <;> cases y <;>
    simp [collisionVertex, vertexPolynomial, occupation, Matrix.smul_apply] <;> ring

section SpatialPolynomial
variable {S V B : Type*} [Fintype S] [DecidableEq S]
  [Fintype V] [DecidableEq V] [Fintype B]

def eventCount (x : S → Option B) : ℕ := ∑ s, occupation (x s)

/-- The next-site map is a permutation, so every occupied bond contributes
exactly two endpoints. This is an exact finite counting statement. -/
theorem endpoint_count (next : Equiv.Perm S) (x : S → Option B) :
    ∑ s, (occupation (x s)+occupation (x (next s))) = 2*eventCount x := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp next (fun s => occupation (x s))]
  simp [eventCount, two_mul]

/-- An explicit finite polynomial in the physical product basis. It sums all
bond configurations; the collision rule makes non-matchings identically zero. -/
def matchingPolynomial (next : Equiv.Perm S)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    Matrix (S → V) (S → V) ℝ[X] :=
  fun a b => ∑ x : S → Option B,
    (X*C g)^eventCount x * ∏ s, vertexPolynomial h G (x s) (x (next s)) (a s) (b s)

/-- Evaluation of the finite polynomial is exactly the physical one-step
operator obtained from the real symmetric spatial transfer. -/
theorem temporalKernel_eq_eval_matchingPolynomial (next : Equiv.Perm S)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (δ g : ℝ)
    (hδg : 0 ≤ δ*g) :
    temporalKernel next (collisionVertex h G δ g) =
      fun a b => (matchingPolynomial next h G g a b).eval δ := by
  ext a b
  simp only [temporalKernel, matchingPolynomial, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [collisionVertex_eq_weight_eval]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, endpoint_count]
  rw [pow_mul, Real.sq_sqrt hδg]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod]

theorem occupation_eq_zero_iff (x : Option B) : occupation x = 0 ↔ x = none := by
  cases x <;> simp [occupation]

theorem eventCount_eq_zero_iff (x : S → Option B) :
    eventCount x = 0 ↔ x = fun _ => none := by
  simp [eventCount, Finset.sum_eq_zero_iff, occupation_eq_zero_iff, funext_iff]

/-- Product-basis Kronecker identity, written without an arbitrary tensor order. -/
theorem product_identity_entries (a b : S → V) :
    (∏ s, (1 : Matrix V V ℝ) (a s) (b s)) = (1 : Matrix (S → V) (S → V) ℝ) a b := by
  simp [Matrix.one_apply, Fintype.prod_ite_zero, funext_iff]

/-- The explicit polynomial step starts at the identity. Nonempty histories
have positive event count and hence vanish at zero time step. -/
theorem matchingPolynomial_coeff_zero (next : Equiv.Perm S)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    (fun a b => (matchingPolynomial next h G g a b).coeff 0) =
      (1 : Matrix (S → V) (S → V) ℝ) := by
  classical
  ext a b
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [matchingPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, zero_mul,
    Polynomial.eval_prod]
  rw [Finset.sum_eq_single (fun _ : S => (none : Option B))]
  · simpa [eventCount, occupation, vertexPolynomial] using product_identity_entries a b
  · intro x _ hx
    have hk : eventCount x ≠ 0 := fun hk => hx ((eventCount_eq_zero_iff x).mp hk)
    simp [hk]
  · simp

/-- Only the zero- and one-event sectors can contribute to the linear
coefficient. Every collision or multi-event term is treated exactly. -/
theorem coeff_one_weighted (Q : ℝ[X]) (g : ℝ) (k : ℕ) :
    ((X*C g)^k*Q).coeff 1 =
      if k=0 then Q.coeff 1 else if k=1 then g*Q.coeff 0 else 0 := by
  rw [mul_pow, ← Polynomial.C_pow, mul_assoc, Polynomial.coeff_X_pow_mul']
  rcases k with _ | k
  · simp
  rcases k with _ | k
  · simp
  · simp [show ¬k+2 ≤ 1 by omega]

/-- A first-coefficient product rule, obtained from actual polynomial
calculus. It does not assume positivity of the polynomial coefficients. -/
theorem coeff_one_prod (P : S → ℝ[X]) :
    (∏ s, P s).coeff 1 =
      ∑ s, (∏ t ∈ Finset.univ.erase s, (P t).coeff 0)*(P s).coeff 1 := by
  have hp := HasDerivAt.fun_finset_prod
    (fun s (_ : s ∈ (Finset.univ : Finset S)) => (P s).hasDerivAt 0)
  have hq := (∏ s, P s).hasDerivAt 0
  have heq : (fun x : ℝ => (∏ s, P s).eval x) =
      (fun x => ∏ s, (P s).eval x) := by funext x; exact Polynomial.eval_prod _ _ _
  rw [heq] at hq
  have hh := hq.unique hp
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    Nat.cast_zero, zero_add, mul_one, smul_eq_mul] using hh

/-- The on-site sum in the physical product basis. -/
def onSiteGenerator (h : Matrix V V ℝ) : Matrix (S → V) (S → V) ℝ :=
  fun a b => ∑ s, (∏ t ∈ Finset.univ.erase s,
    (1 : Matrix V V ℝ) (a t) (b t))*h (a s) (b s)

/-- The unweighted local insertion factor at zero time step. -/
def insertionVertex (G : B → Matrix V V ℝ) :
    Option B → Option B → Matrix V V ℝ
  | none, none => 1
  | some a, none => G a
  | none, some b => G b
  | some _, some _ => 0

@[simp] theorem vertexPolynomial_coeff_zero (h : Matrix V V ℝ)
    (G : B → Matrix V V ℝ) (x y : Option B) (i j : V) :
    (vertexPolynomial h G x y i j).coeff 0 = insertionVertex G x y i j := by
  cases x <;> cases y <;> simp [vertexPolynomial, insertionVertex]

/-- The exactly-one-bond sector. Reindexing this finite sum by site and
label gives the usual sum of pair insertions at the endpoints of each bond. -/
def oneEventGenerator (next : Equiv.Perm S) (G : B → Matrix V V ℝ) :
    Matrix (S → V) (S → V) ℝ :=
  fun a b => ∑ x : S → Option B,
    if eventCount x = 1 then ∏ s, insertionVertex G (x s) (x (next s)) (a s) (b s)
    else 0

/-- Exact linear coefficient of the physical matching polynomial. The sign of
the on-site term and the factor of g are derived, not additional hypotheses. -/
theorem matchingPolynomial_coeff_one (next : Equiv.Perm S)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    (fun a b => (matchingPolynomial next h G g a b).coeff 1) =
      -onSiteGenerator h+g • oneEventGenerator next G := by
  classical
  ext a b
  simp only [matchingPolynomial, Polynomial.finset_sum_coeff, coeff_one_weighted]
  have hsplit (x : S → Option B) (Q : ℝ[X]) :
      (if eventCount x=0 then Q.coeff 1 else if eventCount x=1 then g*Q.coeff 0 else 0) =
      (if x=(fun _ => none) then Q.coeff 1 else 0) +
      g*(if eventCount x=1 then Q.coeff 0 else 0) := by
    by_cases hzero : eventCount x=0
    · have hx := (eventCount_eq_zero_iff x).mp hzero
      simp [hx, eventCount, occupation]
    · have hx : x ≠ fun _ => none := fun hh => hzero ((eventCount_eq_zero_iff x).mpr hh)
      by_cases hone : eventCount x=1 <;> simp [hzero, hx, hone]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hempty :
      (∏ s, vertexPolynomial h G none none (a s) (b s)).coeff 1 =
      -onSiteGenerator h a b := by
    rw [coeff_one_prod]
    simp [vertexPolynomial, onSiteGenerator, Finset.sum_neg_distrib]
  rw [hempty]
  change -onSiteGenerator h a b+g*_ = -onSiteGenerator h a b+g*_
  congr 1
  congr 1
  unfold oneEventGenerator
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp only [← Polynomial.coeff_zero_eq_eval_zero, vertexPolynomial_coeff_zero]
  · rfl

#print axioms matchingPolynomial_coeff_one
#print axioms matchingPolynomial_coeff_zero
#print axioms endpoint_count
#print axioms temporalKernel_eq_eval_matchingPolynomial
end SpatialPolynomial
end BilayerGap.History
