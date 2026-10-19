import Gap.RealRungPair

/-! Concrete real rung operators used in the lattice Hamiltonian. Their
relation to the six physical spin matrices is certified in LocalRung. -/
noncomputable section
namespace BilayerGap.RealRungOperators
open Matrix
open scoped Kronecker

def h : Matrix (Fin 4) (Fin 4) ℝ := LocalRung.rungDiagonal.map (Rat.castHom ℝ)
def G (a : Fin 6) : Matrix (Fin 4) (Fin 4) ℝ :=
  (LocalRung.generators a).map (Rat.castHom ℝ)

theorem h_symmetric : h.transpose = h := by
  ext i j
  by_cases hij : i = j
  · subst j; rfl
  · simp [h, LocalRung.rungDiagonal, hij, Ne.symm hij]

theorem G_antisymmetric (a : Fin 6) : (G a).transpose = -G a := by
  ext i j
  have hq := congrArg (fun A : LocalRung.Q4 => (A i j : ℝ))
    (LocalRung.generators_antisymmetric a)
  simpa [G] using hq

theorem G_diagonal_zero (a : Fin 6) (i : Fin 4) : G a i i = 0 := by
  simp [G, LocalRung.generators_diagonal_zero]

theorem h_vacuum : h 0 0 = 0 := by norm_num [h, LocalRung.rungDiagonal]

theorem pair_hamiltonian_eq (t : ℝ) :
    RealRungPair.hamiltonian t = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) + 1 ⊗ₖ h -
        t • ∑ a : Fin 6, G a ⊗ₖ G a) := by
  ext i j
  simp [RealRungPair.hamiltonian, RealRungPair.toReal, RealRungPair.rung,
    RealRungPair.interaction, h, G, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply, Matrix.sum_apply, Matrix.one_apply, Matrix.map_apply]
  split_ifs <;> simp_all <;> ring

#print axioms pair_hamiltonian_eq
end BilayerGap.RealRungOperators
