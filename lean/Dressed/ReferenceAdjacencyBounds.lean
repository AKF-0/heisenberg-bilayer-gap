import Dressed.CoupledQuadraticCovariance
import Dressed.PhysicalProductEmbedding
import Dressed.MatrixRowAlgebra
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Spectral constants of the actual quadratic-reference adjacency

This is the reference kernel Δ=(g/2)Adj on site-color modes, not the nonlinear
dressed pair kernel. Its eigenvalue and squared-trace bounds are derived from
actual finite entries and the ordinary torus neighbor geometry.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.ReferenceAdjacency
open Matrix BilayerGap FiniteOccupation CoupledQuadratic
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
variable {V : Type*} [Fintype V] [DecidableEq V]

section SpectralRow
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A genuine Hermitian eigenvalue is controlled by an actual absolute row bound. -/
theorem eigenvalue_abs_le_row (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (r : ℝ) (hrow : HasAbsRowBound A r) (i : I) : |hA.eigenvalues i| ≤ r := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' A) (hA.eigenvalues i)
      (fun j => hA.eigenvectorBasis i j) := by
    constructor
    · exact Module.End.mem_eigenspace_iff.mpr (hA.mulVec_eigenvectorBasis i)
    · intro hz
      apply hA.eigenvectorBasis.orthonormal.ne_zero i
      ext j
      exact congrFun hz j
  obtain ⟨k,hk⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector hv)
  have hb : |hA.eigenvalues i - A k k| ≤ ∑ j ∈ Finset.univ.erase k, |A k j| := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] using hk
  calc
    |hA.eigenvalues i| = |(hA.eigenvalues i-A k k)+A k k| := by congr 1; ring
    _ ≤ |hA.eigenvalues i-A k k|+|A k k| := abs_add_le _ _
    _ ≤ (∑ j ∈ Finset.univ.erase k, |A k j|)+|A k k| := add_le_add_right hb _
    _ = absRowSum A k := Finset.sum_erase_add _ _ (Finset.mem_univ k)
    _ ≤ r := hrow k

/-- Squared eigenvalues equal the actual squared trace, by finite orthogonal diagonalization. -/
theorem eigenvalue_square_sum (A : Matrix I I ℝ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i)^2) = Matrix.trace (A*A) := by
  let Q : Matrix I I ℝ := hA.eigenvectorUnitary
  have hQ : Q.transpose * Q = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hQQ : Q * Q.transpose = 1 := Matrix.mul_eq_one_comm.mp hQ
  have hd : Q.transpose * A * Q = Matrix.diagonal hA.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hA.star_mul_self_mul_eq_diagonal
  calc
    (∑ i, (hA.eigenvalues i)^2) =
        Matrix.trace (Matrix.diagonal hA.eigenvalues * Matrix.diagonal hA.eigenvalues) := by
      simp [Matrix.diagonal_mul_diagonal, pow_two]
    _ = Matrix.trace (Q.transpose * (A*A) * Q) := by
      rw [orthogonal_conjugate_mul Q A A hQQ, hd]
    _ = Matrix.trace (A*A) := by
      rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
end SpectralRow

/-- The precise reference coefficient matrix on site-color modes. -/
def kernel (ex ey : Equiv.Perm V) (g : ℝ) : Matrix (Mode V) (Mode V) ℝ :=
  (g/2) • graphAdjacency ex ey

omit [Fintype V] in
/-- All four oriented adjacency contributions are nonnegative. -/
theorem adjacency_nonneg (ex ey : Equiv.Perm V) (i j : Mode V) :
    0 ≤ graphAdjacency ex ey i j := by
  simp only [graphAdjacency, directedAdjacency, Matrix.add_apply, Matrix.transpose_apply]
  positivity

omit [Fintype V] in
theorem kernel_hermitian (ex ey : Equiv.Perm V) (g : ℝ) :
    (kernel ex ey g).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [kernel, Matrix.transpose_smul, graphAdjacency_transpose]

/-- The exact finite row bound is 2g, with no volume factor. -/
theorem kernel_row_bound (ex ey : Equiv.Perm V) (g : ℝ) (hg : 0 ≤ g) :
    HasAbsRowBound (kernel ex ey g) (2*g) := by
  intro i
  unfold kernel
  rw [absRowSum_smul, abs_of_nonneg (by positivity)]
  have hr : absRowSum (graphAdjacency ex ey) i = 4 := by
    simp only [absRowSum, abs_of_nonneg (adjacency_nonneg ex ey i _), graphAdjacency_row_sum]
  rw [hr]
  linarith

/-- Every actual reference eigenvalue, not an assumed mode list, satisfies |z_i|≤2g. -/
theorem kernel_eigenvalue_bound (ex ey : Equiv.Perm V) (g : ℝ) (hg : 0 ≤ g)
    (i : Mode V) : |(kernel_hermitian ex ey g).eigenvalues i| ≤ 2*g :=
  eigenvalue_abs_le_row _ _ _ (kernel_row_bound ex ey g hg) i


private theorem rotate_apply (L : ℕ) [NeZero L] (i : Fin L) : finRotate L i = i+1 := by
  cases L with
  | zero => exact Fin.elim0 i
  | succ L => exact finRotate_succ_apply i

private theorem rotate_ne_self (L : ℕ) (hL : 2 ≤ L) (i : Fin L) :
    finRotate L i ≠ i := by
  letI : NeZero L := ⟨by omega⟩
  rw [rotate_apply L]
  intro h
  have hz : (1 : Fin L) = 0 := add_left_cancel (a := i) (by simpa only [add_zero] using h)
  have hv := congrArg Fin.val hz
  norm_num [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < L)] at hv

private theorem rotate_inverse_ne_self (L : ℕ) (hL : 2 ≤ L) (i : Fin L) :
    (finRotate L).symm i ≠ i := by
  intro h
  have hh := congrArg (finRotate L) h
  simp only [Equiv.apply_symm_apply] at hh
  exact rotate_ne_self L hL i hh.symm

private theorem rotate_ne_inverse (L : ℕ) (hL : 3 ≤ L) (i : Fin L) :
    finRotate L i ≠ (finRotate L).symm i := by
  cases L with
  | zero => omega
  | succ L =>
    intro h
    have h2 : i+1+1=i := by
      simpa only [rotate_apply (L+1), finRotate_succ_symm_apply,
        sub_add_cancel] using congrArg (fun x : Fin (L+1) => x+1) h
    have hz : (1 : Fin (L+1))+1=0 := add_left_cancel (a := i)
      (by simpa only [add_assoc, add_zero] using h2)
    have hv := congrArg Fin.val hz
    simp [Fin.val_add_eq_ite, Nat.mod_eq_of_lt (by omega : 1 < L+1)] at hv
    split_ifs at hv; omega

def vertexNeighbor (n m : ℕ) (v : Torus.Vertex n m) : Fin 4 → Torus.Vertex n m :=
  ![(finRotate (2*n) v.1,v.2), ((finRotate (2*n)).symm v.1,v.2),
    (v.1,finRotate (2*m) v.2), (v.1,(finRotate (2*m)).symm v.2)]

theorem vertexNeighbor_injective (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (v : Torus.Vertex n m) : Function.Injective (vertexNeighbor n m v) := by
  have hxp := rotate_ne_self (2*n) (by omega) v.1
  have hxm := rotate_inverse_ne_self (2*n) (by omega) v.1
  have hxpm := rotate_ne_inverse (2*n) (by omega) v.1
  have hypm := rotate_ne_inverse (2*m) (by omega) v.2
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [vertexNeighbor, Prod.mk.injEq, Ne.symm hxp, Ne.symm hxm,
      Ne.symm hxpm, Ne.symm hypm]

/-- The four color-preserving neighbor labels, including opposite directions. -/
def neighbor (ex ey : Equiv.Perm V) (i : Mode V) : Fin 4 → Mode V :=
  ![modePerm ex i, (modePerm ex).symm i, modePerm ey i, (modePerm ey).symm i]

omit [Fintype V] in
/-- Entrywise identification with the four-neighbor list, retaining multiplicity. -/
theorem adjacency_entry (ex ey : Equiv.Perm V) (i j : Mode V) :
    graphAdjacency ex ey i j = ∑ a : Fin 4, if j = neighbor ex ey i a then 1 else 0 := by
  have hi (e : Equiv.Perm V) : i = modePerm e j ↔ j = (modePerm e).symm i := by
    constructor
    · intro h
      rw [h, Equiv.symm_apply_apply]
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp only [graphAdjacency, directedAdjacency, Matrix.add_apply, Matrix.transpose_apply,
    hi, neighbor, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one]
  ring

omit [Fintype V] in
/-- With four distinct neighbors, the adjacency entries are genuinely zero or one. -/
theorem adjacency_entry_square (ex ey : Equiv.Perm V)
    (hneighbors : ∀ i, Function.Injective (neighbor ex ey i)) (i j : Mode V) :
    (graphAdjacency ex ey i j)^2 = graphAdjacency ex ey i j := by
  by_cases hj : ∃ a, j = neighbor ex ey i a
  · obtain ⟨a,rfl⟩ := hj
    have he : graphAdjacency ex ey i (neighbor ex ey i a) = 1 := by
      rw [adjacency_entry]
      simp [(hneighbors i).eq_iff]
    rw [he]
    norm_num
  · have he : graphAdjacency ex ey i j = 0 := by
      rw [adjacency_entry]
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg (fun h => hj ⟨a,h⟩)]
    rw [he]
    norm_num

/-- The squared adjacency diagonal counts the actual four distinct neighbors. -/
theorem adjacency_square_diagonal (ex ey : Equiv.Perm V)
    (hneighbors : ∀ i, Function.Injective (neighbor ex ey i)) (i : Mode V) :
    (graphAdjacency ex ey * graphAdjacency ex ey) i i = 4 := by
  have hs (j : Mode V) : graphAdjacency ex ey j i = graphAdjacency ex ey i j :=
    congrArg (fun A : Matrix (Mode V) (Mode V) ℝ => A i j) (graphAdjacency_transpose ex ey)
  simp only [Matrix.mul_apply, hs, ← pow_two, adjacency_entry_square ex ey hneighbors,
    graphAdjacency_row_sum]

/-- The exact reference square diagonal is g². -/
theorem kernel_square_diagonal (ex ey : Equiv.Perm V)
    (hneighbors : ∀ i, Function.Injective (neighbor ex ey i)) (g : ℝ) (i : Mode V) :
    (kernel ex ey g * kernel ex ey g) i i = g^2 := by
  simp only [kernel, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul, adjacency_square_diagonal ex ey hneighbors]
  ring

/-- Exact trace-square constant: three colors times the number of sites times g². -/
theorem kernel_trace_square (ex ey : Equiv.Perm V)
    (hneighbors : ∀ i, Function.Injective (neighbor ex ey i)) (g : ℝ) :
    Matrix.trace (kernel ex ey g * kernel ex ey g) = 3*(Fintype.card V : ℝ)*g^2 := by
  simp only [Matrix.trace, Matrix.diag_apply, kernel_square_diagonal ex ey hneighbors,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The spatial component of the mode-neighbor list is the actual torus neighbor list. -/
theorem torus_neighbor_fst (n m : ℕ) (i : Mode (Torus.Vertex n m)) (a : Fin 4) :
    (neighbor (Torus.xNext n m) (Torus.yNext n m) i a).1 = vertexNeighbor n m i.1 a := by
  fin_cases a <;> rfl

/-- Ordinary even tori have four distinct neighboring modes; color is unchanged. -/
theorem torus_neighbors_injective (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (i : Mode (Torus.Vertex n m)) :
    Function.Injective (neighbor (Torus.xNext n m) (Torus.yNext n m) i) := by
  intro a b h
  apply vertexNeighbor_injective n m hn hm i.1
  simpa only [torus_neighbor_fst] using congrArg Prod.fst h

/-- Actual reference eigenvalues in the canonical finite spectral basis. -/
theorem graphModeEigenvalue_bound (ex ey : Equiv.Perm V) (g : ℝ) (hg : 0 ≤ g)
    (i : Mode V) : |PhysicalProduct.graphModeEigenvalue ex ey g i| ≤ 2*g :=
  kernel_eigenvalue_bound ex ey g hg i

/-- Exact sum of squared canonical mode eigenvalues on an ordinary even torus. -/
theorem torus_graphModeEigenvalue_square_sum (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (g : ℝ) :
    (∑ i : Mode (Torus.Vertex n m),
      (PhysicalProduct.graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i)^2) =
        3*((2*n)*(2*m) : ℝ)*g^2 := by
  change (∑ i, ((kernel_hermitian (Torus.xNext n m) (Torus.yNext n m) g).eigenvalues i)^2) = _
  rw [eigenvalue_square_sum, kernel_trace_square _ _ (torus_neighbors_injective n m hn hm)]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]

/-- Exact squared trace of the canonical physical-reference kernel on the ordinary torus. -/
theorem torus_graphKernel_trace_square (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (g : ℝ) :
    Matrix.trace
      (PhysicalProduct.graphKernel (Torus.xNext n m) (Torus.yNext n m) g *
        PhysicalProduct.graphKernel (Torus.xNext n m) (Torus.yNext n m) g) =
      3*((2*n)*(2*m) : ℝ)*g^2 := by
  change Matrix.trace (kernel (Torus.xNext n m) (Torus.yNext n m) g *
    kernel (Torus.xNext n m) (Torus.yNext n m) g) = _
  rw [kernel_trace_square _ _ (torus_neighbors_injective n m hn hm)]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]

end BilayerDressed.ReferenceAdjacency
