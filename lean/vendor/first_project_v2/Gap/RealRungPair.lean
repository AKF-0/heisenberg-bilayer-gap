import Gap.LocalRung
import Gap.TwoRungTrace
import Gap.ClusterProducts

/-! Exact rational bridge between the real rung-coordinate pair and the
computational-basis two-rung Hamiltonian. All similarity coefficients are checked
by the Lean kernel over ℚ, then extended uniformly to every real coupling. -/
noncomputable section
namespace BilayerGap.RealRungPair
open Matrix
open scoped Kronecker
abbrev Q16 := Matrix (Fin 16) (Fin 16) ℚ
abbrev R16 := Matrix (Fin 16) (Fin 16) ℝ

def rung : Q16 := Matrix.reindex finProdFinEquiv finProdFinEquiv
  (LocalRung.rungDiagonal ⊗ₖ 1 + 1 ⊗ₖ LocalRung.rungDiagonal)
def interaction : Q16 := - ∑ a : Fin 6,
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (LocalRung.generators a ⊗ₖ LocalRung.generators a)

def basis : Q16 := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 1/2, 0, 0, 1/2, -1/2;
    0, 0, 0, 0, 0, 0, 0, 0, 1/2, 1/2, 0, 0, 1/2, -1/2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1/2, 1/2, 0, 0, -1/2, -1/2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, -1/2, 0, 0, 1/2, 1/2;
    0, 0, 1/2, 1/2, 0, 0, 1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0;
    1/2, 1/2, 0, 0, 1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1/2, 1/2, 0, 0, -1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1/2, -1/2, 0, 0, 1/2, 1/2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1/2, -1/2, 0, 0, 1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0;
    -1/2, -1/2, 0, 0, 1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1/2, -1/2, 0, 0, -1/2, -1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1/2, 1/2, 0, 0, 1/2, 1/2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 1/2, 0, 0, -1/2, 1/2;
    0, 0, 0, 0, 0, 0, 0, 0, 1/2, 1/2, 0, 0, -1/2, 1/2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1/2, 1/2, 0, 0, 1/2, 1/2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, -1/2, 0, 0, -1/2, -1/2]

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem rung_symmetric : rung.transpose = rung := by decide +kernel
theorem interaction_symmetric : interaction.transpose = interaction := by decide +kernel
theorem rung_vacuum : rung 0 0 = 0 := by decide +kernel
theorem interaction_vacuum : interaction 0 0 = 0 := by decide +kernel

theorem basis_inverse_left : basis.transpose * basis = 1 := by decide +kernel
theorem basis_inverse_right : basis * basis.transpose = 1 := by decide +kernel

theorem rung_intertwines : TwoRung.rung * basis = basis * rung := by decide +kernel
theorem interaction_intertwines :
    TwoRung.interaction * basis = basis * interaction := by decide +kernel

def toReal (A : Q16) : R16 := A.map (Rat.castHom ℝ)
def hamiltonian (t : ℝ) : R16 := toReal rung + t • toReal interaction

theorem toReal_mul (A B : Q16) : toReal (A * B) = toReal A * toReal B :=
  Matrix.map_mul

theorem real_basis_left : toReal basis.transpose * toReal basis = 1 := by
  rw [← toReal_mul, basis_inverse_left]
  simp [toReal]
theorem real_basis_right : toReal basis * toReal basis.transpose = 1 := by
  rw [← toReal_mul, basis_inverse_right]
  simp [toReal]

theorem real_intertwines (t : ℝ) :
    TwoRung.realHamiltonian t * toReal basis = toReal basis * hamiltonian t := by
  have hR : TwoRung.toReal TwoRung.rung * toReal basis = toReal basis * toReal rung := by
    change toReal TwoRung.rung * toReal basis = _
    rw [← toReal_mul, rung_intertwines, toReal_mul]
  have hV : TwoRung.toReal TwoRung.interaction * toReal basis =
      toReal basis * toReal interaction := by
    change toReal TwoRung.interaction * toReal basis = _
    rw [← toReal_mul, interaction_intertwines, toReal_mul]
  simp only [TwoRung.realHamiltonian, hamiltonian, add_mul, smul_mul_assoc,
    mul_add, mul_smul_comm, hR, hV]

theorem hamiltonian_hermitian (t : ℝ) : (hamiltonian t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hr := congrArg (fun A : Q16 => (A i j : ℝ)) rung_symmetric
  have hi := congrArg (fun A : Q16 => (A i j : ℝ)) interaction_symmetric
  simp only [Matrix.transpose_apply] at hr hi
  simp [hamiltonian, toReal, hr, hi]

theorem hamiltonian_vacuum (t : ℝ) : hamiltonian t 0 0 = 0 := by
  simp [hamiltonian, toReal, rung_vacuum, interaction_vacuum]

theorem trace_exp_eq_partition (t b : ℝ) :
    Matrix.trace (NormedSpace.exp ℝ ((-b) • hamiltonian t)) = ClusterSeed.partition t b := by
  rw [← TwoRungTrace.trace_exp_eq_partition t b]
  exact (TwoRungTrace.trace_exp_eq_of_intertwines _ _ _ _
    real_basis_right real_basis_left (real_intertwines t) (-b)).symm

#print axioms trace_exp_eq_partition
#print axioms interaction_intertwines
end BilayerGap.RealRungPair
