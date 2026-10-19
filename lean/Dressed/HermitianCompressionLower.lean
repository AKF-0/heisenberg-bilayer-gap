import Dressed.HermitianInterlacing

/-!
# Lower interlacing for genuine isometric embeddings

Unlike upper interlacing, this compares the same *increasing* index in spaces
of different dimensions. The proof is a spectral-subspace dimension argument;
no comparison of eigenvalue lists is an assumption.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An affine lower quadratic-form comparison through an isometry bounds
actual increasingly ordered eigenvalues, even when the ambient space is larger. -/
theorem symmetric_eigenvalues_affine_embedding_lower
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {m n : ℕ}
    (N : E →ₗ[ℝ] E) (H : F →ₗ[ℝ] F)
    (hN : N.IsSymmetric) (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hm : Module.finrank ℝ F = m)
    (f : F →ₗ[ℝ] E) (hf : Function.Injective f)
    (hnorm : ∀ x, ‖f x‖ = ‖x‖) (a c : ℝ) (ha : 0 ≤ a)
    (hform : ∀ x, a * ⟪f x, N (f x)⟫ - c * ‖x‖^2 ≤ ⟪x, H x⟫)
    (k : Fin m) (hkn : k.val < n) :
    a * hN.eigenvalues hn (⟨k.val, hkn⟩ : Fin n).rev - c ≤
      hH.eigenvalues hm k.rev := by
  classical
  let S := basisSubspace (hH.eigenvectorBasis hm) (Set.Ici k.rev)
  let T := basisSubspace (hN.eigenvectorBasis hn)
    (Set.Iic (⟨k.val, hkn⟩ : Fin n).rev)
  have hdimS : Module.finrank ℝ (S.map f) = k.val + 1 := by
    rw [← (Submodule.equivMapOfInjective f hf S).finrank_eq]
    simp [S, finrank_basisSubspace, Fintype.card_Ici, Fin.card_Ici]
    omega
  have hdimT : Module.finrank ℝ T = n - k.val := by
    simp [T, finrank_basisSubspace, Fintype.card_Iic, Fin.card_Iic]
    omega
  obtain ⟨y, hy, hyS, hyT⟩ := exists_ne_zero_mem_intersection (S.map f) T (by
    rw [hn, hdimS, hdimT]
    omega)
  obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hyS
  have hx : x ≠ 0 := by intro h; subst x; simpa using hy
  have hlo := lower_rayleigh_on_basisSubspace N hN (hN.eigenvectorBasis hn)
    (hN.eigenvalues hn) (by simp)
    (Set.Iic (⟨k.val, hkn⟩ : Fin n).rev)
    (hN.eigenvalues hn (⟨k.val, hkn⟩ : Fin n).rev)
    (fun i hi => hN.eigenvalues_antitone hn hi) (f x) hyT
  have hup := upper_rayleigh_on_basisSubspace H hH (hH.eigenvectorBasis hm)
    (hH.eigenvalues hm) (by simp) (Set.Ici k.rev) (hH.eigenvalues hm k.rev)
    (fun i hi => hH.eigenvalues_antitone hm hi) x hxS
  rw [hnorm x] at hlo
  have hscaled := mul_le_mul_of_nonneg_left hlo ha
  have hprod : (a * hN.eigenvalues hn (⟨k.val, hkn⟩ : Fin n).rev - c) * ‖x‖^2 ≤
      hH.eigenvalues hm k.rev * ‖x‖^2 := by nlinarith [hform x]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp hprod

/-- Matrix interface for lower interlacing through any concrete linear isometry.
The affine comparison is an operator-form premise, not a spectral premise. -/
theorem hermitian_ascendingEigenvalue_affine_embedding_lower
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : Matrix κ κ ℝ) (H : Matrix ι ι ℝ)
    (hN : N.IsHermitian) (hH : H.IsHermitian)
    (f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ)
    (hf : Function.Injective f) (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (a c : ℝ) (ha : 0 ≤ a)
    (hform : ∀ x, a * ⟪f x, N.toEuclideanLin (f x)⟫ - c * ‖x‖^2 ≤
      ⟪x, H.toEuclideanLin x⟫)
    (k : Fin (Fintype.card ι)) (hkn : k.val < Fintype.card κ) :
    a * ascendingEigenvalue hN ⟨k.val, hkn⟩ - c ≤ ascendingEigenvalue hH k :=
  symmetric_eigenvalues_affine_embedding_lower N.toEuclideanLin H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hN)
    (Matrix.isHermitian_iff_isSymmetric.mp hH)
    finrank_euclideanSpace finrank_euclideanSpace f hf hnorm a c ha hform k hkn

end BilayerDressed
