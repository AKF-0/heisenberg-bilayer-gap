import Dressed.GlobalResidualAlgebra
import Dressed.GlobalResidualSplit
import Dressed.GlobalResidualDegrees
import Dressed.GlobalResidualLocalMatrix
import Dressed.PairBlockAlgebra
import Dressed.DressedVacuum
import Dressed.GlobalCartesianBasis

/-!
# Exact finite global dressed residual

The coefficient ring consists of the actual hard-core creation matrices on the
sites outside a selected bond. It is commutative, not a fermionic exterior
algebra. A genuine block algebra homomorphism transports the sixteen-state
calculation to the full configuration Hilbert space.
-/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed.GlobalResidual
open LocalBond PhysicalGram
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 40000

abbrev Coeff (u v : V) := creationAlgebra (Outside u v)
abbrev LocalMatrix (u v : V) := Matrix PairIndex PairIndex (Coeff u v)

/-- Only the genuine outside-site creation subalgebra is used as coefficients. -/
def assembleCreation (u v : V) (huv : u ≠ v) :
    LocalMatrix u v →ₐ[ℝ] ConfigurationMatrix V :=
  (PairBlock.assemble u v huv).toAlgHom.comp ((creationAlgebra (Outside u v)).val.mapMatrix)

/-- The scalar block embedding of an outside creation polynomial. -/
def coefficientLift (u v : V) (huv : u ≠ v) : Coeff u v →ₐ[ℝ] ConfigurationMatrix V :=
  (assembleCreation u v huv).comp (Matrix.scalarAlgHom PairIndex ℝ)

@[simp] theorem coefficientLift_C (u v : V) (huv : u ≠ v)
    (w : Outside u v) (α : Fin 3) :
    coefficientLift u v huv (C w α) = globalCreate w.val α := by
  change PairBlock.assemble u v huv
    (((Matrix.scalar PairIndex (C w α)).map (creationAlgebra (Outside u v)).val)) = _
  have he : (Matrix.scalar PairIndex (C w α)).map (creationAlgebra (Outside u v)).val =
      Matrix.scalar PairIndex (globalCreate w α) := by
    ext p q s t
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
    split_ifs <;> simp_all
  rw [he, PairBlock.assemble_outside_create]

theorem coefficientLift_eq_assemble_scalar (u v : V) (huv : u ≠ v) (a : Coeff u v) :
    coefficientLift u v huv a =
      PairBlock.assemble u v huv (Matrix.scalar PairIndex (a : ConfigurationMatrix (Outside u v))) := by
  change PairBlock.assemble u v huv ((Matrix.scalar PairIndex a).map
    (creationAlgebra (Outside u v)).val) = _
  congr 1
  ext p q
  by_cases hp : p=q <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, hp]

/-- The outside-site embedding lands in the actual global creation subalgebra. -/
theorem coefficientLift_mem (u v : V) (huv : u ≠ v) (a : Coeff u v) :
    coefficientLift u v huv a ∈ creationAlgebra V := by
  let f : ConfigurationMatrix (Outside u v) →ₐ[ℝ] ConfigurationMatrix V :=
    (PairBlock.assemble u v huv).toAlgHom.comp (Matrix.scalarAlgHom PairIndex ℝ)
  have hsub : creationAlgebra (Outside u v) ≤ (creationAlgebra V).comap f := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨w,α⟩,rfl⟩
    change PairBlock.assemble u v huv (Matrix.scalar PairIndex (globalCreate w α)) ∈
      creationAlgebra V
    rw [PairBlock.assemble_outside_create]
    exact (C w.val α).property
  rw [coefficientLift_eq_assemble_scalar]
  exact hsub a.property

/-- The genuine commutative-algebra version of that embedding. -/
def coefficientLiftC (u v : V) (huv : u ≠ v) : Coeff u v →ₐ[ℝ] creationAlgebra V :=
  (coefficientLift u v huv).codRestrict (creationAlgebra V) (coefficientLift_mem u v huv)

@[simp] theorem coe_coefficientLiftC (u v : V) (huv : u ≠ v) (a : Coeff u v) :
    ((coefficientLiftC u v huv a : creationAlgebra V) : ConfigurationMatrix V) =
      coefficientLift u v huv a := rfl

@[simp] theorem coefficientLiftC_C (u v : V) (huv : u ≠ v)
    (w : Outside u v) (α : Fin 3) : coefficientLiftC u v huv (C w α) = C w.val α := by
  apply Subtype.ext
  exact coefficientLift_C u v huv w α

/-- The actual kernel row, with both local endpoints excluded. -/
def field (K : V → V → ℝ) (u v r : V) (α : Fin 3) : Coeff u v :=
  ∑ w : Outside u v, K r w • C w α

@[simp] theorem coefficientLift_field (K : V → V → ℝ) (u v : V) (huv : u ≠ v)
    (r : V) (α : Fin 3) :
    coefficientLift u v huv (field K u v r α) =
      ∑ w : Outside u v, K r w • globalCreate w.val α := by
  simp only [field, map_sum, map_smul, coefficientLift_C]

@[simp] theorem coefficientLiftC_field (K : V → V → ℝ) (u v : V) (huv : u ≠ v)
    (r : V) (α : Fin 3) :
    coefficientLiftC u v huv (field K u v r α) = outsideField C K u v r α := by
  simp only [field, outsideField, map_sum, map_smul, coefficientLiftC_C]

/-- The pair generator restricted to the outside sites, still a concrete nilpotent. -/
def outsideGenerator (K : V → V → ℝ) (u v : V) : Coeff u v :=
  S (fun r s : Outside u v => K r s)

theorem outsideGenerator_nilpotent (K : V → V → ℝ) (u v : V) :
    IsNilpotent (outsideGenerator K u v) := S_nilpotent _

/-- The exact two-endpoint generator as a matrix over the outside algebra. -/
def bondGenerator (K : V → V → ℝ) (u v : V) : LocalMatrix u v :=
  generatorMatrix (field K u v u) (field K u v v) (algebraMap ℝ (Coeff u v) (K u v))

/-- Exact block representation of the full pair ansatz. -/
def blockGenerator (K : V → V → ℝ) (u v : V) : LocalMatrix u v :=
  Matrix.scalar PairIndex (outsideGenerator K u v) + bondGenerator K u v

@[simp] theorem assembleCreation_left (u v : V) (huv : u ≠ v) (α : Fin 3) :
    assembleCreation u v huv ((create α : Mat (Coeff u v)) ⊗ₖ (1 : Mat (Coeff u v))) =
      globalCreate u α := by
  change PairBlock.assemble u v huv
    (((create α : Mat (Coeff u v)) ⊗ₖ (1 : Mat (Coeff u v))).map
      (creationAlgebra (Outside u v)).val) = _
  rw [← PairBlock.assemble_left_create u v huv α]
  congr 1
  ext p q s t
  simp [Matrix.map_apply, Matrix.kronecker_apply, create, unit, Matrix.single,
    Matrix.one_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp_all [Matrix.one_apply]

@[simp] theorem assembleCreation_right (u v : V) (huv : u ≠ v) (α : Fin 3) :
    assembleCreation u v huv ((1 : Mat (Coeff u v)) ⊗ₖ (create α : Mat (Coeff u v))) =
      globalCreate v α := by
  change PairBlock.assemble u v huv
    (((1 : Mat (Coeff u v)) ⊗ₖ (create α : Mat (Coeff u v))).map
      (creationAlgebra (Outside u v)).val) = _
  rw [← PairBlock.assemble_right_create u v huv α]
  congr 1
  ext p q s t
  simp [Matrix.map_apply, Matrix.kronecker_apply, create, unit, Matrix.single,
    Matrix.one_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp_all [Matrix.one_apply]

@[simp] theorem assembleCreation_scalar (u v : V) (huv : u ≠ v) (a : Coeff u v) :
    assembleCreation u v huv (Matrix.scalar PairIndex a) = coefficientLift u v huv a := rfl

@[simp] theorem assembleCreation_pair (u v : V) (huv : u ≠ v) (α β : Fin 3) :
    assembleCreation u v huv ((create α : Mat (Coeff u v)) ⊗ₖ (create β : Mat (Coeff u v))) =
      globalCreate u α * globalCreate v β := by
  have he : (create α : Mat (Coeff u v)) ⊗ₖ (create β : Mat (Coeff u v)) =
      ((create α : Mat (Coeff u v)) ⊗ₖ (1 : Mat (Coeff u v))) *
      ((1 : Mat (Coeff u v)) ⊗ₖ (create β : Mat (Coeff u v))) := by
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rw [he, map_mul, assembleCreation_left, assembleCreation_right]

set_option synthInstance.maxHeartbeats 100000 in
/-- Scalar coefficient multiplication in its literal entrywise form. -/
theorem assembleCreation_coefficient (u v : V) (huv : u ≠ v)
    (a : Coeff u v) (M : LocalMatrix u v) :
    assembleCreation u v huv (a • M) =
      coefficientLift u v huv a * assembleCreation u v huv M := by
  exact map_coefficient_smul (assembleCreation u v huv).toRingHom a M

/-- Both endpoint fields retain their exact coefficients when assembled. -/
theorem assemble_bondGenerator (K : V → V → ℝ) (u v : V) (huv : u ≠ v) :
    assembleCreation u v huv (bondGenerator K u v) =
      ((twoSitePolynomial C K u v : creationAlgebra V) : ConfigurationMatrix V) := by
  simp only [bondGenerator, generatorMatrix_formula, map_add, map_sum,
    assembleCreation_coefficient, assembleCreation_scalar, assembleCreation_left, assembleCreation_right,
    assembleCreation_pair, coefficientLift_field]
  rw [AlgHom.commutes]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  simp only [twoSitePolynomial, outsideField, map_add, map_sum, map_smul,
    Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_mul, coe_C,
    AddSubmonoidClass.coe_finset_sum]
  congr 2
  · apply Finset.sum_congr rfl
    intro α _
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [(global_creation_commute w.val u α α).eq]
  · apply Finset.sum_congr rfl
    intro α _
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [(global_creation_commute w.val v α α).eq]

/-- The outside block is exactly the outside part of the original half-ordered sum. -/
theorem coefficientLift_outsideGenerator (K : V → V → ℝ) (u v : V) (huv : u ≠ v) :
    coefficientLift u v huv (outsideGenerator K u v) =
      ((outsidePairPolynomial C K u v : creationAlgebra V) : ConfigurationMatrix V) := by
  simp [outsideGenerator, S, outsidePairPolynomial, pairPolynomial, map_sum, map_mul,
    coefficientLift_C]

/-- The full actual pair generator, with its mandatory half-ordered convention,
is the image of the local-plus-outside block generator. -/
theorem assemble_blockGenerator (K : V → V → ℝ) (hK : ∀ r s, K r s = K s r)
    (u v : V) (huv : u ≠ v) :
    assembleCreation u v huv (blockGenerator K u v) = pairKernelS K := by
  have hs := congrArg (fun a : creationAlgebra V => (a : ConfigurationMatrix V))
    (pairPolynomial_split C C_mul_same K hK u v huv)
  change ((S K : creationAlgebra V) : ConfigurationMatrix V) = _ at hs
  rw [coe_S] at hs
  change pairKernelS K = _ at hs
  rw [blockGenerator, map_add, assemble_bondGenerator]
  change coefficientLift u v huv (outsideGenerator K u v) + _ = _
  rw [coefficientLift_outsideGenerator]
  simpa only [Subalgebra.coe_add, add_comm] using hs.symm

end BilayerDressed.GlobalResidual
