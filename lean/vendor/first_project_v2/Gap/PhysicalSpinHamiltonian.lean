import Gap.LocalRung
import Gap.TorusHamiltonian
import Gap.RealRungOperators

/-!
# The standard physical spin Hamiltonian and its global rung-basis similarity

The physical matrix is built directly from the six complex Pauli spin operators,
with positive antiferromagnetic coupling. Its change of basis is the actual
finite tensor product of the certified local rung basis, not an assumed spectral
or partition correspondence.
-/
noncomputable section
namespace BilayerGap.PhysicalSpinHamiltonian
open Matrix
open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]
abbrev Configuration (S : Type*) := S → Fin 4
abbrev Operator (S : Type*) := Matrix (Configuration S) (Configuration S) ℂ

/-- Explicit tensor product in the physical product basis. -/
def tensorMap (A : S → LocalRung.C4) : Operator S :=
  fun s t => ∏ v, A v (s v) (t v)

/-- Tensor products multiply sitewise; the proof is finite sum/product exchange. -/
theorem tensorMap_mul (A B : S → LocalRung.C4) :
    tensorMap A * tensorMap B = tensorMap (fun v => A v * B v) := by
  ext s t
  simp only [Matrix.mul_apply, tensorMap, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun v i => A v (s v) i * B v i (t v))).symm

/-- The product of local identity matrices is the global identity. -/
theorem tensorMap_one : tensorMap (fun _ : S => (1 : LocalRung.C4)) = 1 := by
  ext s t
  simp [tensorMap, Matrix.one_apply, Fintype.prod_ite_zero, funext_iff]

/-- One physical-site operator, with identities at every other site. -/
def lift (A : LocalRung.C4) (v : S) : Operator S :=
  tensorMap (Function.update (fun _ => 1) v A)

/-- Its entries have the usual product of Kronecker deltas. -/
theorem lift_entry (A : LocalRung.C4) (v : S) (s t : Configuration S) :
    lift A v s t =
      (∏ w ∈ Finset.univ.erase v, (if s w = t w then 1 else 0 : ℂ)) * A (s v) (t v) := by
  unfold lift tensorMap
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
  simp [Function.update_of_ne hwv, Matrix.one_apply]

/-- A scalar on a single local factor gives the same scalar on its global lift. -/
theorem lift_smul (z : ℂ) (A : LocalRung.C4) (v : S) :
    lift (z • A) v = z • lift A v := by
  ext s t
  simp only [lift_entry, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The actual global basis and its explicit inverse. -/
def globalBasis : Operator S := tensorMap (fun _ => LocalRung.basis)
def globalInverse : Operator S := tensorMap (fun _ => LocalRung.basisInverse)

theorem global_inverse_left : (globalInverse : Operator S) * globalBasis = 1 := by
  rw [globalInverse, globalBasis, tensorMap_mul]
  simp only [LocalRung.basis_inverse_left]
  exact tensorMap_one

theorem global_inverse_right : (globalBasis : Operator S) * globalInverse = 1 := by
  rw [globalInverse, globalBasis, tensorMap_mul]
  simp only [LocalRung.basis_inverse_right]
  exact tensorMap_one

/-- Local intertwining lifts to the full product space without assuming it. -/
theorem lift_intertwines (A B : LocalRung.C4) (hAB : A * LocalRung.basis = LocalRung.basis * B)
    (v : S) : lift A v * globalBasis = globalBasis * lift B v := by
  unfold lift globalBasis
  rw [tensorMap_mul, tensorMap_mul]
  congr 1
  funext w
  by_cases hw : w = v
  · subst w; simpa using hAB
  · simp [Function.update_of_ne hw]

/-- Real matrices embedded in the usual complex physical Hilbert space. -/
def complexify {I : Type*} (A : Matrix I I ℝ) : Matrix I I ℂ :=
  A.map Complex.ofRealHom

theorem complexify_siteLift (A : Matrix (Fin 4) (Fin 4) ℝ) (v : S) :
    complexify (Torus.siteLift A v) = lift (complexify A) v := by
  ext s t
  simp only [complexify, Matrix.map_apply, Torus.siteLift_eq_delta_product, lift_entry]
  simp only [map_mul, map_prod, apply_ite, map_one, map_zero]

/-- Each of the six physical spin-half operators in the full product basis. -/
def siteSpin (a : Fin 6) (v : S) : Operator S := lift (LocalRung.physicalSpin a) v

/-- Physical intra-rung exchange plus the fixed 3/4 shift. -/
def siteRung (v : S) : Operator S := lift LocalRung.physicalRung v

/-- Every physical single-spin operator is globally conjugate to i times the
corresponding real antisymmetric rung generator. -/
theorem siteSpin_intertwines (a : Fin 6) (v : S) :
    siteSpin a v * globalBasis =
      globalBasis * (Complex.I • lift (LocalRung.complexGenerator a) v) := by
  simpa only [siteSpin, lift_smul] using
    lift_intertwines _ _ (LocalRung.physical_spin_intertwines a) v

theorem siteRung_intertwines (v : S) :
    siteRung v * globalBasis =
      globalBasis * lift (LocalRung.rungDiagonal.map (Rat.castHom ℂ)) v :=
  lift_intertwines _ _ LocalRung.physical_rung_intertwines v

/-- Two physical spins on an edge contribute the derived minus sign i*i=-1.
The identity does not assume that the endpoints or operators commute. -/
theorem edge_intertwines (a : Fin 6) (u v : S) :
    (siteSpin a u * siteSpin a v) * globalBasis =
      globalBasis * (-(lift (LocalRung.complexGenerator a) u *
        lift (LocalRung.complexGenerator a) v)) := by
  rw [mul_assoc, siteSpin_intertwines, ← mul_assoc, siteSpin_intertwines,
    mul_assoc]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul, mul_neg]

/-- The standard positive-coupling physical Hamiltonian on an explicit pair of
neighbor maps. The six spin indices comprise both layers and all three axes. -/
def hamiltonian (nextX nextY : S → S) (g : ℝ) : Operator S :=
  (∑ v, siteRung v) + (g : ℂ) •
    ((∑ v, ∑ a : Fin 6, siteSpin a v * siteSpin a (nextX v)) +
      (∑ v, ∑ a : Fin 6, siteSpin a v * siteSpin a (nextY v)))

/-- The same operator in complexified real rung coordinates. -/
def rungHamiltonian (nextX nextY : S → S) (g : ℝ) : Operator S :=
  (∑ v, lift (LocalRung.rungDiagonal.map (Rat.castHom ℂ)) v) - (g : ℂ) •
    ((∑ v, ∑ a : Fin 6, lift (LocalRung.complexGenerator a) v *
        lift (LocalRung.complexGenerator a) (nextX v)) +
      (∑ v, ∑ a : Fin 6, lift (LocalRung.complexGenerator a) v *
        lift (LocalRung.complexGenerator a) (nextY v)))

/-- The actual entire physical Hamiltonian intertwines with the global tensor
basis; this is not just a local identity or an assigned naming convention. -/
theorem hamiltonian_intertwines (nextX nextY : S → S) (g : ℝ) :
    hamiltonian nextX nextY g * globalBasis =
      globalBasis * rungHamiltonian nextX nextY g := by
  have ho : (∑ v : S, siteRung v) * globalBasis =
      globalBasis * ∑ v : S, lift (LocalRung.rungDiagonal.map (Rat.castHom ℂ)) v := by
    simp only [Finset.sum_mul, siteRung_intertwines, Matrix.mul_sum]
  have he (next : S → S) :
      (∑ v : S, ∑ a : Fin 6, siteSpin a v * siteSpin a (next v)) * globalBasis =
        globalBasis * (-(∑ v : S, ∑ a : Fin 6,
          lift (LocalRung.complexGenerator a) v * lift (LocalRung.complexGenerator a) (next v))) := by
    simp only [Finset.sum_mul, edge_intertwines, mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum]
  simp only [hamiltonian, rungHamiltonian, add_mul, smul_mul_assoc, ho, he,
    mul_sub, mul_smul_comm, mul_add, mul_neg, smul_neg, smul_add]
  abel

/-- An exact global similarity, with the explicit inverse already proved. -/
theorem hamiltonian_similarity (nextX nextY : S → S) (g : ℝ) :
    hamiltonian nextX nextY g = globalBasis * rungHamiltonian nextX nextY g * globalInverse := by
  calc
    hamiltonian nextX nextY g = hamiltonian nextX nextY g * (globalBasis * globalInverse) := by
      rw [global_inverse_right, mul_one]
    _ = globalBasis * rungHamiltonian nextX nextY g * globalInverse := by
      rw [← mul_assoc, hamiltonian_intertwines]

/-- Entrywise real-to-complex embedding preserves multiplication. -/
theorem complexify_mul {I : Type*} [Fintype I] (A B : Matrix I I ℝ) :
    complexify (A*B) = complexify A * complexify B := Matrix.map_mul

theorem complexify_add {I : Type*} (A B : Matrix I I ℝ) :
    complexify (A+B) = complexify A + complexify B := by
  ext i j; simp [complexify]

theorem complexify_sub {I : Type*} (A B : Matrix I I ℝ) :
    complexify (A-B) = complexify A - complexify B := by
  ext i j; simp [complexify]

theorem complexify_smul {I : Type*} (r : ℝ) (A : Matrix I I ℝ) :
    complexify (r • A) = (r : ℂ) • complexify A := by
  ext i j; simp [complexify]

theorem complexify_sum {I J : Type*} [Fintype J] (A : J → Matrix I I ℝ) :
    complexify (∑ j, A j) = ∑ j, complexify (A j) := by
  ext i k; simp [complexify, Matrix.sum_apply]

/-- Similar matrices have exactly the same characteristic polynomial, with
all algebraic multiplicities retained. -/
theorem hamiltonian_charpoly (nextX nextY : S → S) (g : ℝ) :
    (hamiltonian nextX nextY g).charpoly = (rungHamiltonian nextX nextY g).charpoly := by
  rw [hamiltonian_similarity, Matrix.charpoly_mul_comm, ← mul_assoc,
    global_inverse_left, one_mul]

/-- The physical Hamiltonian on the actual L-by-M periodic square lattice. -/
def fullHamiltonian (L M : ℕ) (g : ℝ) : Operator (Torus.FullVertex L M) :=
  hamiltonian (Torus.fullXNext L M) (Torus.fullYNext L M) g

/-- The real-to-complex cast agrees exactly with the certified rational generators. -/
theorem complexify_real_generator (a : Fin 6) :
    complexify (RealRungOperators.G a) = LocalRung.complexGenerator a := by
  ext i j
  simp [complexify, RealRungOperators.G, LocalRung.complexGenerator]

theorem complexify_real_rung :
    complexify RealRungOperators.h = LocalRung.rungDiagonal.map (Rat.castHom ℂ) := by
  ext i j
  simp [complexify, RealRungOperators.h]

/-- The real matrix used by the Gibbs proof is exactly the complex rung matrix
in the global similarity, with the same sites, bonds, coupling, and energy shift. -/
theorem complexify_fullHamiltonian (L M : ℕ) (g : ℝ) :
    complexify (Torus.fullHamiltonian L M RealRungOperators.h RealRungOperators.G g) =
      rungHamiltonian (Torus.fullXNext L M) (Torus.fullYNext L M) g := by
  simp only [Torus.fullHamiltonian, complexify_sub, complexify_sum, complexify_smul,
    complexify_add, complexify_mul, complexify_siteLift,
    complexify_real_generator, complexify_real_rung, rungHamiltonian]

/-- Final global physical-basis bridge, uniform in both actual side lengths.
The conclusion is an actual matrix equation for the standard positive-g spin
Hamiltonian, not a hypothesis about an unknown spectrum. -/
theorem fullHamiltonian_intertwines (L M : ℕ) (g : ℝ) :
    fullHamiltonian L M g * globalBasis = globalBasis *
      complexify (Torus.fullHamiltonian L M RealRungOperators.h RealRungOperators.G g) := by
  rw [complexify_fullHamiltonian]
  exact hamiltonian_intertwines _ _ g

theorem fullHamiltonian_similarity (L M : ℕ) (g : ℝ) :
    fullHamiltonian L M g = globalBasis *
      complexify (Torus.fullHamiltonian L M RealRungOperators.h RealRungOperators.G g) *
      globalInverse := by
  rw [complexify_fullHamiltonian]
  exact hamiltonian_similarity _ _ g

/-- The complete characteristic polynomial, including multiplicities, is the
same for the standard physical matrix and the complexified verified real matrix. -/
theorem fullHamiltonian_charpoly (L M : ℕ) (g : ℝ) :
    (fullHamiltonian L M g).charpoly =
      (complexify (Torus.fullHamiltonian L M RealRungOperators.h RealRungOperators.G g)).charpoly := by
  rw [complexify_fullHamiltonian]
  exact hamiltonian_charpoly _ _ g

end BilayerGap.PhysicalSpinHamiltonian
