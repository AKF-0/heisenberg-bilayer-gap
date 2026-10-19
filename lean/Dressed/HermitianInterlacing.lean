import Dressed.HermitianMinMax

/-!
# Finite Hermitian compression and Gram spectra

These are statements about mathlib's actual ordered eigenvalues. The
compression inequality is proved by finite spectral-subspace intersection.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The kth largest eigenvalue cannot increase under an isometric compression. -/
theorem symmetric_eigenvalues_compression_le
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {m n : ℕ}
    (A : F →ₗ[ℝ] F) (B : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hm : Module.finrank ℝ F = m) (hn : Module.finrank ℝ E = n)
    (f : F →ₗ[ℝ] E) (hf : Function.Injective f)
    (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (hform : ∀ x, ⟪x, A x⟫ = ⟪f x, B (f x)⟫)
    (k : Fin m) (hkn : k.val < n) :
    hA.eigenvalues hm k ≤ hB.eigenvalues hn ⟨k.val, hkn⟩ := by
  classical
  let S := basisSubspace (hA.eigenvectorBasis hm) (Set.Iic k)
  let T := basisSubspace (hB.eigenvectorBasis hn) (Set.Ici (⟨k.val, hkn⟩ : Fin n))
  have hdimS : Module.finrank ℝ (S.map f) = k.val + 1 := by
    rw [← (Submodule.equivMapOfInjective f hf S).finrank_eq]
    simp [S, finrank_basisSubspace, Fintype.card_Iic, Fin.card_Iic]
  have hdimT : Module.finrank ℝ T = n - k.val := by
    simp [T, finrank_basisSubspace, Fintype.card_Ici, Fin.card_Ici]
  obtain ⟨y, hy, hyS, hyT⟩ := exists_ne_zero_mem_intersection (S.map f) T (by
    rw [hn, hdimS, hdimT]
    omega)
  obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hyS
  have hx : x ≠ 0 := by intro h; subst x; simpa using hy
  have hlo := lower_rayleigh_on_basisSubspace A hA (hA.eigenvectorBasis hm)
    (hA.eigenvalues hm) (by simp) (Set.Iic k) (hA.eigenvalues hm k)
    (fun i hi => hA.eigenvalues_antitone hm hi) x hxS
  have hup := upper_rayleigh_on_basisSubspace B hB (hB.eigenvectorBasis hn)
    (hB.eigenvalues hn) (by simp) (Set.Ici (⟨k.val, hkn⟩ : Fin n))
    (hB.eigenvalues hn ⟨k.val, hkn⟩)
    (fun i hi => hB.eigenvalues_antitone hn hi) (f x) hyT
  rw [← hform x, hnorm x] at hup
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp (hlo.trans hup)

/-- Equal characteristic polynomials give equal ordered Hermitian spectra. -/
theorem hermitian_eigenvalues₀_eq_of_charpoly_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  apply List.ofFn_inj.mp
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]

/-- The two square Gram matrices have identical actual sorted eigenvalues,
including zero multiplicities. No nonsingularity hypothesis is used. -/
theorem gram_eigenvalues₀_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues₀ =
      (Matrix.posSemidef_self_mul_conjTranspose A).1.eigenvalues₀ := by
  apply hermitian_eigenvalues₀_eq_of_charpoly_eq
  exact Matrix.charpoly_mul_comm _ _

/-- Appending a zero coordinate is the leading-coordinate embedding. -/
def leadingEmbedding (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) 0)
  map_add' x y := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem leadingEmbedding_castSucc {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    leadingEmbedding n x i.castSucc = x i := by simp [leadingEmbedding]

@[simp] theorem leadingEmbedding_last {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    leadingEmbedding n x (Fin.last n) = 0 := by simp [leadingEmbedding]

theorem leadingEmbedding_injective (n : ℕ) :
    Function.Injective (leadingEmbedding n) := by
  intro x y h
  apply PiLp.ext
  intro i
  simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.castSucc) h

theorem leadingEmbedding_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖leadingEmbedding n x‖ = ‖x‖ := by
  have h : ‖leadingEmbedding n x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc,
      leadingEmbedding_castSucc, leadingEmbedding_last, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero]
  nlinarith [norm_nonneg (leadingEmbedding n x), norm_nonneg x]

/-- The quadratic form of a leading principal block is an exact compression. -/
theorem leadingEmbedding_form {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, (B.submatrix Fin.castSucc Fin.castSucc).toEuclideanLin x⟫ =
      ⟪leadingEmbedding n x, B.toEuclideanLin (leadingEmbedding n x)⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    dotProduct, Matrix.mulVec, Matrix.submatrix_apply, star_trivial]
  rw [Fin.sum_univ_castSucc]
  simp only [leadingEmbedding, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_castSucc]
  simp

/-- Upper half of principal-block interlacing, in decreasing order. -/
theorem hermitian_leading_eigenvalues₀_le {n : ℕ}
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hB : B.IsHermitian)
    (k : Fin n) :
    (hB.submatrix Fin.castSucc).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) ≤
      hB.eigenvalues₀ (Fin.cast (Fintype.card_fin (n+1)).symm k.castSucc) := by
  exact symmetric_eigenvalues_compression_le
    (B.submatrix Fin.castSucc Fin.castSucc).toEuclideanLin B.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp (hB.submatrix Fin.castSucc))
    (Matrix.isHermitian_iff_isSymmetric.mp hB)
    finrank_euclideanSpace finrank_euclideanSpace
    (leadingEmbedding n) (leadingEmbedding_injective n) leadingEmbedding_norm
    (leadingEmbedding_form B) _ (by simpa using k.castSucc.isLt)

end BilayerDressed
