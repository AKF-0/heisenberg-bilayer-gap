import Gap.UniformBilayerGap
import Gap.PhysicalSpinHamiltonian

/-!
# Complete eigenbasis and uniform gap for the standard physical spin Hamiltonian

The final theorem concerns the explicit positive-coupling Pauli-spin matrix.
It supplies an invertible complete eigenbasis and a unique lowest real energy,
with a size-independent gap. No correspondence with an unnamed model is assumed.
-/
noncomputable section
namespace BilayerGap.PhysicalGap
open Matrix PhysicalSpinHamiltonian

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A checked physical similarity and a real Hermitian spectral theorem produce
an actual complete complex eigenbasis with the same real energies. -/
theorem eigenbasis_of_intertwines (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (H W V : Matrix I I ℂ) (hWV : W*V=1) (hVW : V*W=1)
    (hHW : H*W=W*complexify A) :
    ∃ P Q : Matrix I I ℂ, P*Q=1 ∧ Q*P=1 ∧
      H*P=P*Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  let R : Matrix I I ℝ := hA.eigenvectorUnitary
  let S : Matrix I I ℝ := star R
  have hRS : R*S=1 := unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hSR : S*R=1 := unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hAR : A*R=R*Matrix.diagonal hA.eigenvalues := by
    conv_lhs => rw [hA.spectral_theorem]
    change (R*Matrix.diagonal hA.eigenvalues*S)*R = _
    rw [mul_assoc, mul_assoc, hSR, mul_one]
  have hcRS : complexify R*complexify S=1 := by
    rw [← complexify_mul, hRS]
    simp [complexify]
  have hcSR : complexify S*complexify R=1 := by
    rw [← complexify_mul, hSR]
    simp [complexify]
  let P := W*complexify R
  let Q := complexify S*V
  refine ⟨P,Q,?_,?_,?_⟩
  · calc
      P*Q = W*(complexify R*complexify S)*V := by dsimp [P,Q]; noncomm_ring
      _ = 1 := by rw [hcRS, mul_one, hWV]
  · calc
      Q*P = complexify S*(V*W)*complexify R := by dsimp [P,Q]; noncomm_ring
      _ = 1 := by rw [hVW, mul_one, hcSR]
  · have hdiag : complexify (Matrix.diagonal hA.eigenvalues) =
        Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
      ext i j
      by_cases hij : i=j <;> simp [complexify, hij]
    calc
      H*P = (H*W)*complexify R := by dsimp [P]; rw [mul_assoc]
      _ = W*complexify (A*R) := by rw [hHW, mul_assoc, complexify_mul]
      _ = P*Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
        rw [hAR, complexify_mul, hdiag, ← mul_assoc]

def physicalMatrix (L M : ℕ) (g : ℝ) :
    Matrix (Fin ((BilayerModel.family g).dim L M : ℕ))
      (Fin ((BilayerModel.family g).dim L M : ℕ)) ℂ :=
  Matrix.reindex (Fintype.equivFin (Torus.FullConfig L M))
    (Fintype.equivFin (Torus.FullConfig L M)) (fullHamiltonian L M g)

theorem physical_dimension (L M : ℕ) (g : ℝ) :
    ((BilayerModel.family g).dim L M : ℕ) = 4^(L*M) := by
  simp [BilayerModel.family, Torus.FullConfig, Torus.FullVertex]

/-- The standard Pauli matrix has a complete eigenbasis with the exact energies
used in the proved Gibbs criterion. All multiplicities are preserved. -/
theorem physical_complete_eigenbasis (L M : ℕ) (g : ℝ) :
    ∃ P Q : Matrix (Fin ((BilayerModel.family g).dim L M : ℕ))
        (Fin ((BilayerModel.family g).dim L M : ℕ)) ℂ,
      P*Q=1 ∧ Q*P=1 ∧ physicalMatrix L M g*P=
        P*Matrix.diagonal (fun i => (((BilayerModel.family g).hermitian L M).eigenvalues i : ℂ)) := by
  let e := Fintype.equivFin (Torus.FullConfig L M)
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  apply eigenbasis_of_intertwines ((BilayerModel.family g).matrix L M)
    ((BilayerModel.family g).hermitian L M) (physicalMatrix L M g)
    (F (globalBasis : Operator (Torus.FullVertex L M)))
    (F (globalInverse : Operator (Torus.FullVertex L M)))
  · have hh := congrArg F (global_inverse_right (S := Torus.FullVertex L M))
    simpa only [map_mul, map_one] using hh
  · have hh := congrArg F (global_inverse_left (S := Torus.FullVertex L M))
    simpa only [map_mul, map_one] using hh
  · have hh := congrArg F (fullHamiltonian_intertwines L M g)
    simpa only [map_mul] using hh

/-- End-to-end result for the standard spin-half bilayer Hamiltonian.
The supplied P and Q prove that these are all energy levels, not selected states. -/
theorem standard_spin_uniform_gap {g : ℝ} (hg0 : 0≤g) (hg : g≤1/1000)
    (L : ℕ) (hL : ValidSize L) :
    ∃ P Q : Matrix (Fin ((BilayerModel.family g).dim L L : ℕ))
        (Fin ((BilayerModel.family g).dim L L : ℕ)) ℂ,
    ∃ i₀ : Fin ((BilayerModel.family g).dim L L : ℕ),
      P*Q=1 ∧ Q*P=1 ∧ physicalMatrix L L g*P=
        P*Matrix.diagonal (fun i => (((BilayerModel.family g).hermitian L L).eigenvalues i : ℂ)) ∧
      (∀ i, ((BilayerModel.family g).hermitian L L).eigenvalues i₀ ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues i) ∧
      ∀ i, i≠i₀ → BilayerModel.gapLowerBound <
        ((BilayerModel.family g).hermitian L L).eigenvalues i-
          ((BilayerModel.family g).hermitian L L).eigenvalues i₀ := by
  obtain ⟨P,Q,hPQ,hQP,hdiag⟩ := physical_complete_eigenbasis L L g
  obtain ⟨i₀,hmin,hgap⟩ := BilayerModel.uniform_ground_gap hg0 hg L hL
  exact ⟨P,Q,i₀,hPQ,hQP,hdiag,hmin,hgap⟩

#print axioms physical_complete_eigenbasis
#print axioms standard_spin_uniform_gap
end BilayerGap.PhysicalGap
