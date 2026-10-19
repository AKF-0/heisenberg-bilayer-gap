import Gap.LocalRungBasis
noncomputable section
namespace BilayerGap.LocalRung
open Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem rational_rung_identity :
    -(∑ a : Fin 3, generators ⟨a.val, by omega⟩ * generators ⟨a.val+3, by omega⟩)
      + (3/4 : ℚ) • 1 = rungDiagonal := by decide +kernel

theorem complex_rung_identity :
    -(∑ a : Fin 3, complexGenerator ⟨a.val, by omega⟩ *
      complexGenerator ⟨a.val+3, by omega⟩) + (3/4 : ℂ) • 1 =
      rungDiagonal.map (Rat.castHom ℂ) := by
  have hh := congrArg (fun A : Q4 => A.map (Rat.castHom ℂ)) rational_rung_identity
  ext i j
  have he := congrArg (fun A : C4 => A i j) hh
  simpa [complexGenerator, Matrix.mul_apply, Matrix.sum_apply, Matrix.one_apply,
    Matrix.map_apply, apply_ite] using he

theorem physical_rung_intertwines :
    physicalRung * basis = basis * rungDiagonal.map (Rat.castHom ℂ) := by
  have hp (a : Fin 3) :
      (physicalSpin ⟨a.val, by omega⟩ * physicalSpin ⟨a.val+3, by omega⟩) * basis =
        basis * (-(complexGenerator ⟨a.val, by omega⟩ *
          complexGenerator ⟨a.val+3, by omega⟩)) := by
    rw [mul_assoc, physical_spin_intertwines, ← mul_assoc, physical_spin_intertwines,
      mul_assoc]
    congr 1
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [← complex_rung_identity]
  simp only [physicalRung, add_mul, Finset.sum_mul, hp, mul_add, mul_neg,
    Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Finset.sum_neg_distrib]

#print axioms physical_spin_intertwines
#print axioms physical_rung_intertwines
#print axioms basis_inverse_left
#print axioms generators_antisymmetric
end BilayerGap.LocalRung
