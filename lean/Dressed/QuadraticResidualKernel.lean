import Dressed.FourRegularKernel
import Dressed.PairVacuumNorm

/-! Exact cancellation through second order in the actual coefficient matrix.
This is a finite matrix identity, followed by coefficient-derived row bounds. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem offDiagonal_add (A B : Matrix V V ℝ) :
    offDiagonal (A+B)=offDiagonal A+offDiagonal B := by
  ext i j
  by_cases h : i=j <;> simp [offDiagonal,h]

theorem offDiagonal_sub (A B : Matrix V V ℝ) :
    offDiagonal (A-B)=offDiagonal A-offDiagonal B := by
  ext i j
  by_cases h : i=j <;> simp [offDiagonal,h]

theorem offDiagonal_smul (r : ℝ) (A : Matrix V V ℝ) :
    offDiagonal (r • A)=r • offDiagonal A := by
  ext i j
  by_cases h : i=j <;> simp [offDiagonal,h]

theorem offDiagonal_eq_self (A : Matrix V V ℝ) (h : ∀ i, A i i=0) :
    offDiagonal A=A := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [offDiagonal,h]
  · simp [offDiagonal,hij]

theorem transpose_offDiagonal (A : Matrix V V ℝ) :
    (offDiagonal A).transpose=offDiagonal A.transpose := by
  ext i j
  simp [offDiagonal,eq_comm]

namespace FourRegularData
variable (G : FourRegularData V)

 theorem off_square_eq (i j : V) :
    offDiagonal (G.adjacency*G.adjacency) i j =
      (G.adjacency*G.adjacency-(4 : ℝ) • (1 : Matrix V V ℝ)) i j := by
  by_cases h : i=j
  · subst j; simp [offDiagonal,G.square_diagonal]
  · simp [offDiagonal,h]

 theorem cube_diagonal (i : V) :
    (G.adjacency*G.adjacency*G.adjacency) i i=0 := by
  apply Finset.sum_eq_zero
  intro j _
  change (G.adjacency*G.adjacency) i j * G.adjacency j i=0
  rcases G.binary j i with h | h
  · simp [h]
  · rw [G.triangle_free i j (by rw [G.symmetric i j]; exact h), zero_mul]

 theorem adjacency_mul_kernel (g : ℝ) :
    G.adjacency*G.kernel g =
      (-(g/4+g^2/8)) • (G.adjacency*G.adjacency) +
      (g^2/8) • (G.adjacency*G.adjacency*G.adjacency) -
      (g^2/2) • G.adjacency := by
  have ho : offDiagonal (G.adjacency*G.adjacency) =
      G.adjacency*G.adjacency-(4 : ℝ) • (1 : Matrix V V ℝ) := by
    ext i j; exact G.off_square_eq i j
  rw [kernel, ho]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one]
  rw [← mul_assoc]
  module

 theorem kernel_mul_adjacency (g : ℝ) :
    G.kernel g*G.adjacency =
      (-(g/4+g^2/8)) • (G.adjacency*G.adjacency) +
      (g^2/8) • (G.adjacency*G.adjacency*G.adjacency) -
      (g^2/2) • G.adjacency := by
  have ho : offDiagonal (G.adjacency*G.adjacency) =
      G.adjacency*G.adjacency-(4 : ℝ) • (1 : Matrix V V ℝ) := by
    ext i j; exact G.off_square_eq i j
  rw [kernel, ho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul]
  module

 theorem adjacency_hadamard_kernel (g : ℝ) :
    (show Matrix V V ℝ from fun i j => G.adjacency i j * G.kernel g i j) =
      (-(g/4+g^2/8)) • G.adjacency := by
  ext i j
  rcases G.binary i j with h | h
  · simp [h]
  · simp [h, G.kernel_on_edge g i j h]

/-- The ungrouped, actual linear-in-K part of the residual coefficient matrix. -/
def linearQuadraticResidual (g : ℝ) : Matrix V V ℝ :=
  (2 : ℝ) • G.kernel g + (g/2) • G.adjacency +
    (g/2) • offDiagonal (G.adjacency*G.kernel g+G.kernel g*G.adjacency) -
    g • (show Matrix V V ℝ from fun i j => G.adjacency i j*G.kernel g i j)

/-- Exact cancellation, not an asymptotic expansion or uncontrolled remainder. -/
 theorem linearQuadraticResidual_eq (g : ℝ) :
    G.linearQuadraticResidual g = (g^3/8) •
      (G.adjacency*G.adjacency*G.adjacency-
        offDiagonal (G.adjacency*G.adjacency)-(3 : ℝ) • G.adjacency) := by
  have hD := offDiagonal_eq_self G.adjacency G.diagonal
  have hC := offDiagonal_eq_self (G.adjacency*G.adjacency*G.adjacency) G.cube_diagonal
  rw [linearQuadraticResidual, G.adjacency_mul_kernel, G.kernel_mul_adjacency,
    G.adjacency_hadamard_kernel]
  simp only [offDiagonal_add, offDiagonal_sub, offDiagonal_smul, hD, hC, kernel]
  module

 theorem adjacency_row_bound : HasAbsRowBound G.adjacency 4 := by
  intro i
  simp only [absRowSum, abs_of_nonneg (G.entry_nonneg _ _), G.degree]
  exact le_rfl

 theorem off_square_row_bound : HasAbsRowBound (offDiagonal (G.adjacency*G.adjacency)) 12 := by
  intro i
  simp only [absRowSum, abs_of_nonneg (G.off_square_nonneg _ _), G.off_square_row_sum]
  exact le_rfl

 theorem cube_row_bound : HasAbsRowBound (G.adjacency*G.adjacency*G.adjacency) 64 := by
  have hh := G.adjacency_row_bound.mul G.adjacency G.adjacency 4 4
    G.adjacency_row_bound (by norm_num)
  have hhh := hh.mul (G.adjacency*G.adjacency) G.adjacency (4*4) 4
    G.adjacency_row_bound (by norm_num)
  norm_num at hhh
  exact hhh

 theorem linearQuadraticResidual_row_bound (g : ℝ) (hg : 0≤g) :
    HasAbsRowBound (G.linearQuadraticResidual g) (11*g^3) := by
  have h₂ := G.off_square_row_bound.smul _ 12 (-1)
  have h₃ := G.adjacency_row_bound.smul _ 4 (-3)
  have hh := (G.cube_row_bound.add _ _ _ _ h₂).add _ _ _ _ h₃
  have h := hh.smul _ _ (g^3/8)
  have habs : |g^3/8|=g^3/8 := abs_of_nonneg (by positivity)
  rw [G.linearQuadraticResidual_eq]
  simp only [habs] at h
  convert h using 1
  · module
  · norm_num; ring

/-- Actual diagonal contraction matrix Z, not an independently supplied bound. -/
def contraction (g : ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => (G.adjacency*G.kernel g) i i)

 theorem contraction_row_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    HasAbsRowBound (G.contraction g) ((101/100 : ℝ)*g) := by
  apply HasAbsRowBound.diagonal
  intro i
  rw [G.adjacency_kernel_diagonal, abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hmax hg]

/-- The full degree-two residual coefficient, including all nonlinear terms. -/
def quadraticResidual (g : ℝ) : Matrix V V ℝ :=
  G.linearQuadraticResidual g+
    quadraticNonlinear G.adjacency (G.kernel g) (G.contraction g) g

 theorem quadraticResidual_row_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    HasAbsRowBound (G.quadraticResidual g) ((89119/5000 : ℝ)*g^3) := by
  have hn := quadraticNonlinear_row_bound G.adjacency (G.kernel g) (G.contraction g)
    g ((103/100 : ℝ)*g) ((101/100 : ℝ)*g) ((13/50 : ℝ)*g)
    hg (by positivity) (by positivity) (by positivity) G.adjacency_row_bound
    (G.kernel_row_bound_small g hg hmax) (G.contraction_row_bound g hg hmax)
    (G.kernel_entry_bound_small g hg hmax)
  have hh := (G.linearQuadraticResidual_row_bound g hg).add _ _ _ _ hn
  unfold quadraticResidual
  convert hh using 1 <;> ring

 theorem quadraticResidual_diagonal (g : ℝ) (i : V) : G.quadraticResidual g i i=0 := by
  simp [quadraticResidual, linearQuadraticResidual_eq, quadraticNonlinear,
    contraction, offDiagonal, G.cube_diagonal, G.diagonal, G.kernel_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

 theorem quadraticResidual_transpose (g : ℝ) :
    (G.quadraticResidual g).transpose=G.quadraticResidual g := by
  have hD : G.adjacency.transpose=G.adjacency := by
    ext i j; exact G.symmetric j i
  have hK : (G.kernel g).transpose=G.kernel g := by
    ext i j; exact G.kernel_symmetric g j i
  have hZ : (G.contraction g).transpose=G.contraction g := by simp [contraction]
  have hH : (show Matrix V V ℝ from fun i j =>
      G.adjacency i j*(G.kernel g i j*G.kernel g i j)).transpose =
      (show Matrix V V ℝ from fun i j => G.adjacency i j*(G.kernel g i j*G.kernel g i j)) := by
    ext i j
    simp only [Matrix.transpose_apply, G.symmetric j i, G.kernel_symmetric g j i]
  rw [quadraticResidual, G.linearQuadraticResidual_eq]
  simp only [quadraticNonlinear, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_mul, transpose_offDiagonal, hD, hK, hZ, hH,
    add_comm, mul_assoc]

 theorem quadraticResidual_symmetric (g : ℝ) (i j : V) :
    G.quadraticResidual g i j=G.quadraticResidual g j i := by
  have hh := congrFun (congrFun (G.quadraticResidual_transpose g) j) i
  exact hh

/-- The direct physical two-triplet residual norm. No bosonic or Gaussian norm is used. -/
 theorem quadraticResidual_vacuum_norm (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (pairKernelS (G.quadraticResidual g)) vacuumVector‖ ≤
        24*Real.sqrt (Fintype.card V : ℝ)*g^3 := by
  let x := Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
    (pairKernelS (G.quadraticResidual g)) vacuumVector
  have he : ‖x‖^2=(3/2 : ℝ)*∑ i,∑ j,(G.quadraticResidual g i j)^2 :=
    pairKernelS_vacuum_norm_sq _ (G.quadraticResidual_symmetric g) (G.quadraticResidual_diagonal g)
  have hf := sum_sq_le_card_row_sq (G.quadraticResidual g) ((89119/5000 : ℝ)*g^3)
    (G.quadraticResidual_row_bound g hg hmax) (by positivity)
  have hnorm : ‖x‖^2≤(3/2 : ℝ)*(Fintype.card V : ℝ)*((89119/5000 : ℝ)*g^3)^2 := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ)≤3/2)
    simpa only [mul_assoc] using hh
  have hsqrt : (Real.sqrt (Fintype.card V : ℝ))^2=(Fintype.card V : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsq : ‖x‖^2≤(24*Real.sqrt (Fintype.card V : ℝ)*g^3)^2 := by
    rw [mul_pow,mul_pow,hsqrt]
    nlinarith [show 0≤(Fintype.card V : ℝ)*(g^3)^2 by positivity]
  exact (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp hsq

end FourRegularData
end BilayerDressed
