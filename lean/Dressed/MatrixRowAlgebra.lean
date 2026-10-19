import Dressed.MatrixRowBounds

/-! Finite row bounds for the concrete quadratic residual polynomial. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HasAbsRowBound.add (A B : Matrix ι ι ℝ) (a b : ℝ)
    (hA : HasAbsRowBound A a) (hB : HasAbsRowBound B b) :
    HasAbsRowBound (A+B) (a+b) := fun i =>
  (absRowSum_add_le A B i).trans (add_le_add (hA i) (hB i))

theorem HasAbsRowBound.smul (A : Matrix ι ι ℝ) (a r : ℝ)
    (hA : HasAbsRowBound A a) : HasAbsRowBound (r • A) (|r| * a) := by
  intro i
  rw [absRowSum_smul]
  exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)

theorem HasAbsRowBound.mono (A : Matrix ι ι ℝ) (a b : ℝ)
    (hA : HasAbsRowBound A a) (hab : a≤b) : HasAbsRowBound A b :=
  fun i => (hA i).trans hab

theorem HasAbsRowBound.offDiagonal (A : Matrix ι ι ℝ) (a : ℝ)
    (hA : HasAbsRowBound A a) : HasAbsRowBound (offDiagonal A) a :=
  fun i => (absRowSum_offDiagonal_le A i).trans (hA i)

/-- Entrywise multiplication uses an entry bound on the second factor. -/
theorem HasAbsRowBound.hadamard (A B : Matrix ι ι ℝ) (a b : ℝ)
    (hA : HasAbsRowBound A a) (hB : ∀ i j, |B i j|≤b) (hb : 0≤b) :
    HasAbsRowBound (fun i j => A i j*B i j) (a*b) := by
  intro i
  calc
    (∑ j, |A i j*B i j|) ≤ ∑ j, |A i j| * b := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB i j) (abs_nonneg _)
    _ = absRowSum A i*b := by simp only [absRowSum, Finset.sum_mul]
    _ ≤ a*b := mul_le_mul_of_nonneg_right (hA i) hb

theorem HasAbsRowBound.diagonal (d : ι → ℝ) (a : ℝ)
    (hd : ∀ i, |d i|≤a) : HasAbsRowBound (Matrix.diagonal d) a := by
  intro i
  simpa [absRowSum, Matrix.diagonal_apply, apply_ite] using hd i

/-- The exact nonlinear part of the degree-two residual coefficient matrix. -/
def quadraticNonlinear (D K Z : Matrix ι ι ℝ) (g : ℝ) : Matrix ι ι ℝ :=
  (g/2) • offDiagonal (K*D*K) + (-2*g) • (Z*K+K*Z) +
    (2*g) • (show Matrix ι ι ℝ from fun i j => D i j*K i j*K i j)

/-- No norm oracle: every term is bounded from its actual finite coefficients. -/
theorem quadraticNonlinear_row_bound (D K Z : Matrix ι ι ℝ) (g κ z k : ℝ)
    (hg : 0≤g) (hκ : 0≤κ) (hz : 0≤z) (hk : 0≤k)
    (hD : HasAbsRowBound D 4) (hK : HasAbsRowBound K κ)
    (hZ : HasAbsRowBound Z z) (hentry : ∀ i j, |K i j|≤k) :
    HasAbsRowBound (quadraticNonlinear D K Z g)
      (2*g*κ^2+4*g*z*κ+8*g*k^2) := by
  have hKD := hK.mul K D κ 4 hD (by norm_num)
  have hKDK := hKD.mul (K*D) K (κ*4) κ hK hκ
  have h₁ := (hKDK.offDiagonal (K*D*K) ((κ*4)*κ)).smul
    (offDiagonal (K*D*K)) ((κ*4)*κ) (g/2)
  have hZK := hZ.mul Z K z κ hK hκ
  have hKZ := hK.mul K Z κ z hZ hz
  have h₂ := (hZK.add (Z*K) (K*Z) (z*κ) (κ*z) hKZ).smul
    (Z*K+K*Z) (z*κ+κ*z) (-2*g)
  have hDK := hD.hadamard D K 4 k hentry hk
  have hDKK := hDK.hadamard (fun i j => D i j*K i j) K (4*k) k hentry hk
  have h₃ := hDKK.smul (fun i j => D i j*K i j*K i j) ((4*k)*k) (2*g)
  have hh := (h₁.add _ _ _ _ h₂).add _ _ _ _ h₃
  have habs₁ : |g/2|=g/2 := abs_of_nonneg (by positivity)
  have habs₂ : |-2*g|=2*g := by rw [abs_of_nonpos (by nlinarith)]; ring
  have habs₃ : |2*g|=2*g := abs_of_nonneg (by positivity)
  simp only [habs₁, habs₂, habs₃] at hh
  unfold quadraticNonlinear
  convert hh using 1 <;> ring

end BilayerDressed
