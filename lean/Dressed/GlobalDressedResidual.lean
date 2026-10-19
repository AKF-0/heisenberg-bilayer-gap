import Dressed.GlobalResidualAssembly
import Dressed.GlobalResidualNaturality
import Dressed.NumberDressing

/-!
# The exact global dressed residual for the concrete Cartesian Hamiltonian

All coefficients below live in the genuine commutative hard-core creation
subalgebra of the actual configuration matrices. The matrix exponential is
finite because the concrete pair generator is nilpotent.
-/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed.GlobalResidual
open LocalBond PhysicalGram BilayerGap
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 100000

/-- The exact block generator is nilpotent independently of its assembly. -/
theorem blockGenerator_nilpotent (K : V → V → ℝ) (u v : V) :
    IsNilpotent (blockGenerator K u v) := by
  exact (Matrix.scalar_commute (outsideGenerator K u v) (fun _ => Commute.all _ _)
    (bondGenerator K u v)).isNilpotent_add
      ((outsideGenerator_nilpotent K u v).map (Matrix.scalar PairIndex))
      ⟨3, generatorMatrix_cube_zero _ _ _⟩

/-- The block bond assembles to the literal Cartesian bond matrix. -/
theorem assemble_twiceBond (u v : V) (huv : u ≠ v) :
    assembleCreation u v huv (twiceBond : LocalMatrix u v) =
      Torus.pairLift (twiceBond : Matrix PairIndex PairIndex ℝ) u v := by
  change PairBlock.assemble u v huv ((twiceBond : LocalMatrix u v).map
    (creationAlgebra (Outside u v)).val) = _
  rw [← twiceBond_map (algebraMap ℝ (Coeff u v)), Matrix.map_map]
  rw [← PairBlock.assemble_map_local u v huv]
  congr 1

/-- All local occupancy sectors become the actual global creation polynomial. -/
theorem assemble_creationPolynomial (u v : V) (huv : u ≠ v) (w : PairIndex → Coeff u v) :
    assembleCreation u v huv (creationPolynomial w) =
      ((evaluate (C u) (C v) (fun p => coefficientLiftC u v huv (w p)) :
        creationAlgebra V) : ConfigurationMatrix V) := by
  rw [creationPolynomial_expansion]
  simp only [map_add, map_sum, assembleCreation_coefficient,
    map_one, mul_one, assembleCreation_left, assembleCreation_right, assembleCreation_pair]
  simp only [evaluate, Subalgebra.coe_add, Subalgebra.coe_mul,
    AddSubmonoidClass.coe_finset_sum, coe_coefficientLiftC, coe_C]
  have hc (a : Coeff u v) (r : V) (α : Fin 3) :
      coefficientLift u v huv a * globalCreate r α =
        globalCreate r α * coefficientLift u v huv a :=
    congrArg (fun z : creationAlgebra V => (z : ConfigurationMatrix V))
      (mul_comm (coefficientLiftC u v huv a) (C r α))
  have hcc (a : Coeff u v) (α β : Fin 3) :
      coefficientLift u v huv a * (globalCreate u α * globalCreate v β) =
        (globalCreate u α * globalCreate v β) * coefficientLift u v huv a :=
    congrArg (fun z : creationAlgebra V => (z : ConfigurationMatrix V))
      (mul_comm (coefficientLiftC u v huv a) (C u α*C v β))
  simp only [hc, hcc]

/-- Exact quadratic creation polynomial for one actual bond. -/
def bondResidual2 (K : V → V → ℝ) (u v : V) : creationAlgebra V :=
  bondR2 (C u) (C v) (outsideField C K u v u) (outsideField C K u v v)
    (algebraMap ℝ (creationAlgebra V) (K u v))

/-- Exact quartic creation polynomial for one actual bond. -/
def bondResidual4 (K : V → V → ℝ) (u v : V) : creationAlgebra V :=
  bondR4 (C u) (C v) (outsideField C K u v u) (outsideField C K u v v)
    (algebraMap ℝ (creationAlgebra V) (K u v))

/-- Exact sextic creation polynomial for one actual bond. -/
def bondResidual6 (K : V → V → ℝ) (u v : V) : creationAlgebra V :=
  bondR6 (C u) (C v) (outsideField C K u v u) (outsideField C K u v v)

/-- All degrees, including the scalar shift, before any kernel specialization. -/
def bondResidual (K : V → V → ℝ) (u v : V) : creationAlgebra V :=
  algebraMap ℝ (creationAlgebra V) (3*K u v) + bondResidual2 K u v +
    bondResidual4 K u v + bondResidual6 K u v

theorem assemble_transformedCoefficients (K : V → V → ℝ) (u v : V) (huv : u ≠ v) :
    assembleCreation u v huv (creationPolynomial (transformedCoefficients
      (field K u v u) (field K u v v) (algebraMap ℝ (Coeff u v) (K u v)))) =
      ((bondResidual K u v : creationAlgebra V) : ConfigurationMatrix V) := by
  rw [assemble_creationPolynomial]
  apply congrArg (fun a : creationAlgebra V => (a : ConfigurationMatrix V))
  have hm := transformedCoefficients_map (coefficientLiftC u v huv).toRingHom
    (field K u v u) (field K u v v) (algebraMap ℝ (Coeff u v) (K u v))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coefficientLiftC_field,
    AlgHom.commutes] at hm
  rw [hm, transformed_degree_decomposition]
  simp only [bondResidual, bondResidual2, bondResidual4, bondResidual6, map_mul, map_ofNat]

/-- Equality on the local vacuum column gives equality on the full vacuum column. -/
theorem assemble_vacuum_equality (u v : V) (huv : u ≠ v) (M N : LocalMatrix u v)
    (h : M.mulVec (Pi.single (0,0) 1) = N.mulVec (Pi.single (0,0) 1))
    (s : Configuration V) :
    assembleCreation u v huv M s TripletNumber.vacuum =
      assembleCreation u v huv N s TripletNumber.vacuum := by
  have hp := congrFun h (s u,s v)
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] at hp
  change PairBlock.assemble u v huv (M.map (creationAlgebra (Outside u v)).val) s
    TripletNumber.vacuum = PairBlock.assemble u v huv
      (N.map (creationAlgebra (Outside u v)).val) s TripletNumber.vacuum
  rw [PairBlock.assemble_vacuum_column, PairBlock.assemble_vacuum_column]
  exact congrArg (fun a : Coeff u v => (a : ConfigurationMatrix (Outside u v))
    (fun w => s w) TripletNumber.vacuum) hp

/-- The finite block exponential is exactly the exponential of the actual pair sum. -/
theorem assemble_exp_block (K : V → V → ℝ) (hK : ∀ r s, K r s = K s r)
    (u v : V) (huv : u ≠ v) :
    assembleCreation u v huv (IsNilpotent.exp (blockGenerator K u v)) =
      IsNilpotent.exp (pairKernelS K) := by
  rw [(blockGenerator_nilpotent K u v).map_exp (assembleCreation u v huv),
    assemble_blockGenerator K hK u v huv]

/-- The concrete global bond action on the finite exponential, with every residual degree. -/
theorem bond_matrix_vacuum (K : V → V → ℝ) (hK : ∀ r s, K r s = K s r)
    (u v : V) (huv : u ≠ v) (s : Configuration V) :
    (Torus.pairLift (twiceBond : Matrix PairIndex PairIndex ℝ) u v *
      IsNilpotent.exp (pairKernelS K)) s TripletNumber.vacuum =
    (IsNilpotent.exp (pairKernelS K) *
      (bondResidual K u v : ConfigurationMatrix V)) s TripletNumber.vacuum := by
  have h := bond_block_exponential_vacuum (outsideGenerator K u v)
    (outsideGenerator_nilpotent K u v) (field K u v u) (field K u v v)
      (algebraMap ℝ (Coeff u v) (K u v))
  change ((twiceBond : LocalMatrix u v) * IsNilpotent.exp (blockGenerator K u v)).mulVec _ =
    (IsNilpotent.exp (blockGenerator K u v) * creationPolynomial _).mulVec _ at h
  have hh := assemble_vacuum_equality u v huv _ _ h s
  simpa only [map_mul, assemble_twiceBond, assemble_exp_block K hK u v huv,
    assemble_transformedCoefficients] using hh

local instance : Module ℚ (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- A concrete matrix acts on the actual all-singlet vector by its vacuum column. -/
@[simp] theorem matrix_vacuum_apply (M : ConfigurationMatrix V) (s : Configuration V) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) M vacuumVector s = M s TripletNumber.vacuum := by
  change (∑ t, M s t * vacuumVector t) = _
  simp [vacuumVector, EuclideanSpace.single_apply]
  rfl

/-- Exact bond identity on the actual finite-dimensional Euclidean Hilbert space. -/
theorem bond_dressedVector (K : V → V → ℝ) (hK : ∀ r s, K r s = K s r)
    (u v : V) (huv : u ≠ v) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (Torus.pairLift (twiceBond : Matrix PairIndex PairIndex ℝ) u v)
      (dressedVector K) =
    IsNilpotent.exp (pairGenerator K)
      ((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (bondResidual K u v : ConfigurationMatrix V) vacuumVector) := by
  have he : (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (IsNilpotent.exp (pairKernelS K)) =
      IsNilpotent.exp (pairGenerator K) :=
    (pair_kernel_nilpotent (fun u v => K u v / 2)).map_exp (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
  rw [dressedVector, ← he]
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply,
    ← map_mul, ← map_mul]
  ext s
  simpa only [matrix_vacuum_apply] using bond_matrix_vacuum K hK u v huv s

/-- The scalar energy shift of the complete finite graph ansatz. -/
def residualShift (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) : ℝ :=
  (g/2) * ((∑ u, 3*K u (ex u)) + (∑ u, 3*K u (ey u)))

/-- Full quadratic polynomial, including the exact number-operator contribution. -/
def residual2 (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) : creationAlgebra V :=
  (2 : ℝ) • S K + (g/2) • ((∑ u, bondResidual2 K u (ex u)) +
    (∑ u, bondResidual2 K u (ey u)))

def residual4 (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) : creationAlgebra V :=
  (g/2) • ((∑ u, bondResidual4 K u (ex u)) + (∑ u, bondResidual4 K u (ey u)))

def residual6 (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) : creationAlgebra V :=
  (g/2) • ((∑ u, bondResidual6 K u (ex u)) + (∑ u, bondResidual6 K u (ey u)))

/-- Exact algebraic grouping of the scalar and all three creation degrees. -/
theorem residual_decomposition (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ) :
    (2 : ℝ) • S K + (g/2) • ((∑ u, bondResidual K u (ex u)) +
      (∑ u, bondResidual K u (ey u))) =
    algebraMap ℝ (creationAlgebra V) (residualShift K ex ey g) +
      (residual2 K ex ey g + residual4 K ex ey g + residual6 K ex ey g) := by
  simp only [bondResidual, residualShift, residual2, residual4, residual6,
    Finset.sum_add_distrib, map_mul, map_add, map_sum,
    Algebra.smul_def]
  noncomm_ring

/-- The actual graph Hamiltonian acting on the actual finite dressed vector. -/
theorem graphHamiltonian_dressedVector (K : V → V → ℝ)
    (hK : ∀ r s, K r s = K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u, ex u ≠ u) (hy : ∀ u, ey u ≠ u) (g : ℝ) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (CartesianBasis.graphHamiltonian ex ey g) (dressedVector K) =
      IsNilpotent.exp (pairGenerator K)
        ((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (((2 : ℝ) • S K + (g/2) •
          ((∑ u, bondResidual K u (ex u)) + (∑ u, bondResidual K u (ey u))) :
            creationAlgebra V) : ConfigurationMatrix V) vacuumVector) := by
  have hbX (u : V) := bond_dressedVector K hK u (ex u) (hx u).symm
  have hbY (u : V) := bond_dressedVector K hK u (ey u) (hy u).symm
  simp only [CartesianBasis.graphHamiltonian, map_add, map_smul, map_sum,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, NumberDressing.number_dressedVector,
    hbX, hbY,
    Subalgebra.coe_add, Subalgebra.coe_smul, AddSubmonoidClass.coe_finset_sum,
    coe_S, pairKernelS, pairGenerator]

/-- Exact global residual identity with all degree-two, degree-four and degree-six terms.
No residual identity, spectral estimate, or kernel approximation is a premise. -/
theorem graph_dressed_residual (K : V → V → ℝ)
    (hK : ∀ r s, K r s = K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u, ex u ≠ u) (hy : ∀ u, ey u ≠ u) (g : ℝ) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (CartesianBasis.graphHamiltonian ex ey g) (dressedVector K) -
      residualShift K ex ey g • dressedVector K =
    IsNilpotent.exp (pairGenerator K)
      ((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) ((residual2 K ex ey g + residual4 K ex ey g +
        residual6 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) vacuumVector) := by
  rw [graphHamiltonian_dressedVector K hK ex ey hx hy g, residual_decomposition]
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_one,
    Algebra.algebraMap_eq_smul_one, map_add, map_smul, map_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, map_add, map_smul, dressedVector,
    add_sub_cancel_left]

/-- Operator form of the same exact identity, with the scalar shift inside H. -/
theorem shifted_graph_dressed_residual (K : V → V → ℝ)
    (hK : ∀ r s, K r s = K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u, ex u ≠ u) (hy : ∀ u, ey u ≠ u) (g : ℝ) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) (CartesianBasis.graphHamiltonian ex ey g -
      residualShift K ex ey g • (1 : ConfigurationMatrix V)) (dressedVector K) =
    IsNilpotent.exp (pairGenerator K)
      ((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)) ((residual2 K ex ey g + residual4 K ex ey g +
        residual6 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) vacuumVector) := by
  simpa only [map_sub, map_smul, map_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using
      graph_dressed_residual K hK ex ey hx hy g

end BilayerDressed.GlobalResidual
