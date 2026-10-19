import Dressed.MatrixRowAlgebra

/-! The explicit quadratic pair kernel on a simple triangle-free four-regular
finite graph. Hypotheses here are finite adjacency identities, not spectral or
residual estimates; concrete torus instantiations are separate. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {V : Type*} [Fintype V] [DecidableEq V]

structure FourRegularData (V : Type*) [Fintype V] where
  adjacency : Matrix V V ℝ
  symmetric : ∀ i j, adjacency i j=adjacency j i
  binary : ∀ i j, adjacency i j=0 ∨ adjacency i j=1
  diagonal : ∀ i, adjacency i i=0
  degree : ∀ i, ∑ j, adjacency i j=4
  triangle_free : ∀ i j, adjacency i j=1 → (adjacency*adjacency) i j=0

namespace FourRegularData
variable (G : FourRegularData V)

 theorem entry_nonneg (i j : V) : 0≤G.adjacency i j := by
  rcases G.binary i j with h | h <;> rw [h] <;> norm_num

 theorem entry_le_one (i j : V) : G.adjacency i j≤1 := by
  rcases G.binary i j with h | h <;> rw [h] <;> norm_num

 theorem square_entry_nonneg (i j : V) : 0≤(G.adjacency*G.adjacency) i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg (G.entry_nonneg i k) (G.entry_nonneg k j)

 theorem square_entry_le_four (i j : V) : (G.adjacency*G.adjacency) i j≤4 := by
  calc
    _ ≤ ∑ k, G.adjacency i k := by
      apply Finset.sum_le_sum
      intro k _
      simpa using mul_le_mul_of_nonneg_left (G.entry_le_one k j) (G.entry_nonneg i k)
    _ = 4 := G.degree i

 theorem square_diagonal (i : V) : (G.adjacency*G.adjacency) i i=4 := by
  calc
    _ = ∑ k, G.adjacency i k := by
      apply Finset.sum_congr rfl
      intro k _
      change G.adjacency i k * G.adjacency k i = G.adjacency i k
      rw [G.symmetric k i]
      rcases G.binary i k with h | h <;> rw [h] <;> norm_num
    _ = 4 := G.degree i

 theorem square_row_sum (i : V) : (∑ j, (G.adjacency*G.adjacency) i j)=16 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.degree]
  rw [← Finset.sum_mul, G.degree]
  norm_num

 theorem off_square_nonneg (i j : V) : 0≤offDiagonal (G.adjacency*G.adjacency) i j := by
  by_cases h : i=j
  · simp [offDiagonal,h]
  · simpa [offDiagonal,h] using G.square_entry_nonneg i j

 theorem off_square_row_sum (i : V) :
    (∑ j, offDiagonal (G.adjacency*G.adjacency) i j)=12 := by
  have hh : (∑ j, offDiagonal (G.adjacency*G.adjacency) i j) +
      (G.adjacency*G.adjacency) i i = ∑ j, (G.adjacency*G.adjacency) i j := by
    have he (j : V) : offDiagonal (G.adjacency*G.adjacency) i j +
        (if i=j then (G.adjacency*G.adjacency) i i else 0) =
        (G.adjacency*G.adjacency) i j := by
      by_cases h : i=j <;> simp [offDiagonal,h]
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => he j)
    simpa [Finset.sum_add_distrib] using hs
  rw [G.square_diagonal, G.square_row_sum] at hh
  linarith

/-- The same explicit kernel as -gD/4+g²(D²-D-4I)/8, written with its zero diagonal exposed. -/
def kernel (g : ℝ) : Matrix V V ℝ :=
  (-(g/4+g^2/8)) • G.adjacency + (g^2/8) • offDiagonal (G.adjacency*G.adjacency)

 theorem kernel_diagonal (g : ℝ) (i : V) : G.kernel g i i=0 := by
  simp [kernel, G.diagonal, offDiagonal]

 theorem kernel_abs_entry (g : ℝ) (hg : 0≤g) (i j : V) :
    |G.kernel g i j|=(g/4+g^2/8)*G.adjacency i j+
      (g^2/8)*offDiagonal (G.adjacency*G.adjacency) i j := by
  rcases G.binary i j with h | h
  · simp only [kernel, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, mul_zero, zero_add]
    exact abs_of_nonneg (mul_nonneg (by positivity) (G.off_square_nonneg i j))
  · have ho : offDiagonal (G.adjacency*G.adjacency) i j=0 := by
      simp [offDiagonal, G.triangle_free i j h]
    simp only [kernel, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, ho,
      mul_one, mul_zero, add_zero]
    rw [abs_neg, abs_of_nonneg (by positivity)]

 theorem kernel_abs_row_sum (g : ℝ) (hg : 0≤g) (i : V) :
    absRowSum (G.kernel g) i=g+2*g^2 := by
  simp only [absRowSum, G.kernel_abs_entry g hg, Finset.sum_add_distrib,
    ← Finset.mul_sum, G.degree, G.off_square_row_sum]
  ring

 theorem kernel_row_bound (g : ℝ) (hg : 0≤g) :
    HasAbsRowBound (G.kernel g) (g+2*g^2) := fun i => (G.kernel_abs_row_sum g hg i).le

 theorem square_symmetric (i j : V) :
    (G.adjacency*G.adjacency) i j=(G.adjacency*G.adjacency) j i := by
  apply Finset.sum_congr rfl
  intro k _
  change G.adjacency i k * G.adjacency k j = G.adjacency j k * G.adjacency k i
  rw [G.symmetric i k, G.symmetric k j]
  ring

 theorem kernel_symmetric (g : ℝ) (i j : V) : G.kernel g i j=G.kernel g j i := by
  simp only [kernel, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, offDiagonal]
  rw [G.symmetric i j, G.square_symmetric i j]
  simp only [eq_comm]

 theorem off_square_entry_le_four (i j : V) :
    offDiagonal (G.adjacency*G.adjacency) i j≤4 := by
  by_cases h : i=j
  · simp [offDiagonal,h]
  · simpa [offDiagonal,h] using G.square_entry_le_four i j

 theorem kernel_row_bound_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    HasAbsRowBound (G.kernel g) ((103/100 : ℝ)*g) := by
  intro i
  rw [G.kernel_abs_row_sum g hg]
  nlinarith [mul_le_mul_of_nonneg_right hmax hg]

 theorem kernel_entry_bound_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (i j : V) :
    |G.kernel g i j|≤(13/50 : ℝ)*g := by
  rw [G.kernel_abs_entry g hg]
  have h₁ := mul_le_mul_of_nonneg_left (G.entry_le_one i j)
    (by positivity : 0≤g/4+g^2/8)
  have h₂ := mul_le_mul_of_nonneg_left (G.off_square_entry_le_four i j)
    (by positivity : 0≤g^2/8)
  nlinarith [mul_le_mul_of_nonneg_right hmax hg]

 theorem kernel_on_edge (g : ℝ) (i j : V) (hij : G.adjacency i j=1) :
    G.kernel g i j=-(g/4+g^2/8) := by
  have ho : offDiagonal (G.adjacency*G.adjacency) i j=0 := by
    simp [offDiagonal,G.triangle_free i j hij]
  simp [kernel,hij,ho]

/-- Exact polynomial form of the explicit kernel, including the diagonal subtraction. -/
 theorem kernel_eq_polynomial (g : ℝ) : G.kernel g =
    (-(g/4)) • G.adjacency + (g^2/8) •
      (G.adjacency*G.adjacency-G.adjacency-(4 : ℝ) • (1 : Matrix V V ℝ)) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [kernel, G.diagonal, G.square_diagonal, offDiagonal]
  · simp only [kernel, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, Matrix.one_apply, if_neg h, offDiagonal]
    ring

/-- Exact diagonal contraction needed in the quadratic residual. -/
 theorem adjacency_kernel_diagonal (g : ℝ) (i : V) :
    (G.adjacency*G.kernel g) i i=-(g+g^2/2) := by
  calc
    _ = ∑ j, G.adjacency i j * (-(g/4+g^2/8)) := by
      apply Finset.sum_congr rfl
      intro j _
      change G.adjacency i j * G.kernel g j i = _
      rcases G.binary i j with h | h
      · simp [h]
      · rw [G.kernel_on_edge g j i (by rw [G.symmetric j i]; exact h)]
    _ = _ := by rw [← Finset.sum_mul, G.degree]; ring

end FourRegularData
end BilayerDressed
