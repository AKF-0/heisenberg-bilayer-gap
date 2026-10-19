import Dressed.OperatorTemple

/-!
# Finite Hermitian eigenvalue monotonicity

The comparison is proved for the actual eigenvalues produced by mathlib's
spectral theorem. The proof uses the dimension inequality for the intersection
of two spectral subspaces, not a hypothesis about ordered eigenvalue lists.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BilayerDressed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Span of the basis vectors whose indices lie in `s`. -/
def basisSubspace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (s : Set ι) : Submodule ℝ E :=
  Submodule.span ℝ (b '' s)

theorem finrank_basisSubspace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (s : Set ι) [Fintype s] :
    Module.finrank ℝ (basisSubspace b s) = Fintype.card s := by
  unfold basisSubspace
  rw [Set.image_eq_range]
  exact finrank_span_eq_card (b.toBasis.linearIndependent.comp _ Subtype.val_injective)

theorem inner_eq_zero_of_mem_basisSubspace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (s : Set ι) {x : E}
    (hx : x ∈ basisSubspace b s) {i : ι} (hi : i ∉ s) :
    ⟪b i, x⟫ = 0 := by
  change x ∈ Submodule.span ℝ (b '' s) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact b.inner_eq_zero (fun hij => hi (hij ▸ hj))
  | zero => simp
  | add x y hx hy hix hiy => simp [inner_add_right, hix, hiy]
  | smul a x hx hix => simp [inner_smul_right, hix]

/-- If two finite-dimensional subspaces have dimensions summing to more than
that of their ambient space, their intersection contains a nonzero vector. -/
theorem exists_ne_zero_mem_intersection [FiniteDimensional ℝ E]
    (S T : Submodule ℝ E)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ S + Module.finrank ℝ T) :
    ∃ x : E, x ≠ 0 ∧ x ∈ S ∧ x ∈ T := by
  have hinf : S ⊓ T ≠ ⊥ := by
    intro h
    have hsum := S.finrank_sup_add_finrank_inf_eq T
    have hle := (S ⊔ T).finrank_le
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  exact ⟨x, hne, hx.1, hx.2⟩

/-- The spectral subspaces above and below the same ordered index intersect.
This is the finite-dimensional min-max dimension argument. -/
theorem exists_mem_upper_lower_subspaces {n : ℕ} [FiniteDimensional ℝ E]
    (b c : OrthonormalBasis (Fin n) ℝ E)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    ∃ x : E, x ≠ 0 ∧ x ∈ basisSubspace b (Set.Iic k) ∧
      x ∈ basisSubspace c (Set.Ici k) := by
  apply exists_ne_zero_mem_intersection
  rw [finrank_basisSubspace, finrank_basisSubspace, hn]
  simp only [Fintype.card_Iic, Fintype.card_Ici, Fin.card_Iic, Fin.card_Ici]
  omega

/-- A lower spectral bound on a selected spectral subspace gives the same
bound for its quadratic form. -/
theorem lower_rayleigh_on_basisSubspace {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i)
    (s : Set ι) (a : ℝ) (ha : ∀ i ∈ s, a ≤ energy i)
    (x : E) (hx : x ∈ basisSubspace b s) :
    a * ‖x‖^2 ≤ ⟪x, T x⟫ := by
  rw [← rayleigh_eq_spectralMean T hT b energy heig x,
    ← b.sum_sq_inner_right x, Finset.mul_sum]
  unfold spectralMean
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ s
  · nlinarith [sq_nonneg ⟪b i, x⟫, ha i hi]
  · simp [inner_eq_zero_of_mem_basisSubspace b s hx hi]

/-- An upper spectral bound on a selected spectral subspace gives the same
bound for its quadratic form. -/
theorem upper_rayleigh_on_basisSubspace {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i)
    (s : Set ι) (a : ℝ) (ha : ∀ i ∈ s, energy i ≤ a)
    (x : E) (hx : x ∈ basisSubspace b s) :
    ⟪x, T x⟫ ≤ a * ‖x‖^2 := by
  rw [← rayleigh_eq_spectralMean T hT b energy heig x,
    ← b.sum_sq_inner_right x, Finset.mul_sum]
  unfold spectralMean
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ s
  · nlinarith [sq_nonneg ⟪b i, x⟫, ha i hi]
  · simp [inner_eq_zero_of_mem_basisSubspace b s hx hi]

/-- Loewner comparison for any two decreasingly ordered orthonormal
spectral decompositions. The eigenvalue inequality is a conclusion. -/
theorem ordered_eigenbasis_mono {n : ℕ} [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (b c : OrthonormalBasis (Fin n) ℝ E) (α β : Fin n → ℝ)
    (heigA : ∀ i, A (b i) = α i • b i)
    (heigB : ∀ i, B (c i) = β i • c i)
    (hα : Antitone α) (hβ : Antitone β)
    (hn : Module.finrank ℝ E = n)
    (hAB : ∀ x, ⟪x, A x⟫ ≤ ⟪x, B x⟫) (k : Fin n) :
    α k ≤ β k := by
  obtain ⟨x, hx, hxb, hxc⟩ := exists_mem_upper_lower_subspaces b c hn k
  have hlo := lower_rayleigh_on_basisSubspace A hA b α heigA
    (Set.Iic k) (α k) (fun i hi => hα hi) x hxb
  have hup := upper_rayleigh_on_basisSubspace B hB c β heigB
    (Set.Ici k) (β k) (fun i hi => hβ hi) x hxc
  have hnorm : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  exact (mul_le_mul_iff_left₀ hnorm).mp (hlo.trans ((hAB x).trans hup))

/-- The actual decreasingly sorted eigenvalues of symmetric operators are
monotone under quadratic-form (Loewner) order. -/
theorem symmetric_eigenvalues_mono {n : ℕ} [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hAB : ∀ x, ⟪x, A x⟫ ≤ ⟪x, B x⟫) (k : Fin n) :
    hA.eigenvalues hn k ≤ hB.eigenvalues hn k := by
  exact ordered_eigenbasis_mono A B hA hB
    (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn)
    (by simp)
    (by simp)
    (hA.eigenvalues_antitone hn) (hB.eigenvalues_antitone hn) hn hAB k

/-- The actual decreasingly sorted eigenvalues of real Hermitian matrices
are monotone under quadratic-form order. -/
theorem hermitian_eigenvalues₀_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℝ ι,
      ⟪x, A.toEuclideanLin x⟫ ≤ ⟪x, B.toEuclideanLin x⟫)
    (k : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  exact symmetric_eigenvalues_mono A.toEuclideanLin B.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hA)
    (Matrix.isHermitian_iff_isSymmetric.mp hB) finrank_euclideanSpace hAB k

/-- Increasingly ordered eigenvalues, obtained by reversing mathlib's actual
spectral ordering. Every eigenvalue retains its algebraic multiplicity. -/
def ascendingEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card ι)) : ℝ :=
  hA.eigenvalues₀ k.rev

theorem ascendingEigenvalue_monotone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : Monotone (ascendingEigenvalue hA) :=
  fun _ _ h => hA.eigenvalues₀_antitone (Fin.rev_le_rev.mpr h)

/-- Finite Hermitian Loewner monotonicity in increasing spectral order. -/
theorem hermitian_ascendingEigenvalue_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℝ ι,
      ⟪x, A.toEuclideanLin x⟫ ≤ ⟪x, B.toEuclideanLin x⟫)
    (k : Fin (Fintype.card ι)) :
    ascendingEigenvalue hA k ≤ ascendingEigenvalue hB k :=
  hermitian_eigenvalues₀_mono A B hA hB hAB k.rev

/-- Quadratic-form interpretation of a positive-semidefinite difference. -/
theorem quadraticForm_le_of_sub_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hAB : (B - A).PosSemidef)
    (x : EuclideanSpace ℝ ι) :
    ⟪x, A.toEuclideanLin x⟫ ≤ ⟪x, B.toEuclideanLin x⟫ := by
  have h : 0 ≤ ⟪x, (B - A).toEuclideanLin x⟫ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanLin_apply, dotProduct_comm] using hAB.2 (WithLp.ofLp x)
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_right, sub_nonneg] using h

/-- Positive-semidefinite-difference form of finite Hermitian min-max. -/
theorem hermitian_ascendingEigenvalue_mono_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card ι)) :
    ascendingEigenvalue hA k ≤ ascendingEigenvalue hB k :=
  hermitian_ascendingEigenvalue_mono A B hA hB
    (quadraticForm_le_of_sub_posSemidef A B hAB) k

/-- Increasingly sorted eigenvalues are exactly the characteristic-polynomial
roots as a multiset, so repeated eigenvalues are not discarded. -/
theorem roots_charpoly_eq_ascendingEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.charpoly.roots = Multiset.map (ascendingEigenvalue hA) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  change Multiset.map hA.eigenvalues₀ Finset.univ.val =
    Multiset.map (hA.eigenvalues₀ ∘ Fin.revPerm) Finset.univ.val
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Any function of the spectrum can be summed using the increasing ordering
without changing its value or multiplicities. -/
theorem sum_ascendingEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ k, f (ascendingEigenvalue hA k)) = ∑ i, f (hA.eigenvalues i) := by
  calc
    (∑ k, f (ascendingEigenvalue hA k)) = ∑ k, f (hA.eigenvalues₀ k) :=
      (Equiv.sum_comp Fin.revPerm (fun k => f (hA.eigenvalues₀ k)))
    _ = ∑ i, f (hA.eigenvalues i) := by
      symm
      exact (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.sum_comp
        (fun k => f (hA.eigenvalues₀ k))

/-- Direct affine min-max comparison. A quadratic form bound `H ≥ a N - c I`
with `a ≥ 0` bounds each actual ordered eigenvalue; `c` need not be positive. -/
theorem symmetric_eigenvalues_affine_lower {n : ℕ} [FiniteDimensional ℝ E]
    (N H : E →ₗ[ℝ] E) (hN : N.IsSymmetric) (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x, a * ⟪x, N x⟫ - c * ‖x‖^2 ≤ ⟪x, H x⟫)
    (k : Fin n) :
    a * hN.eigenvalues hn k - c ≤ hH.eigenvalues hn k := by
  obtain ⟨x, hx, hxN, hxH⟩ := exists_mem_upper_lower_subspaces
    (hN.eigenvectorBasis hn) (hH.eigenvectorBasis hn) hn k
  have hlo := lower_rayleigh_on_basisSubspace N hN (hN.eigenvectorBasis hn)
    (hN.eigenvalues hn) (by simp)
    (Set.Iic k) (hN.eigenvalues hn k)
    (fun i hi => hN.eigenvalues_antitone hn hi) x hxN
  have hup := upper_rayleigh_on_basisSubspace H hH (hH.eigenvectorBasis hn)
    (hH.eigenvalues hn) (by simp)
    (Set.Ici k) (hH.eigenvalues hn k)
    (fun i hi => hH.eigenvalues_antitone hn hi) x hxH
  have hscaled := mul_le_mul_of_nonneg_left hlo ha
  have hnorm : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hprod : (a * hN.eigenvalues hn k - c) * ‖x‖^2 ≤
      hH.eigenvalues hn k * ‖x‖^2 := by
    nlinarith [hNH x]
  exact (mul_le_mul_iff_left₀ hnorm).mp hprod

/-- Concrete finite Hermitian `H ≥ a N - c I` bounds in increasing order. -/
theorem hermitian_ascendingEigenvalue_affine_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (k : Fin (Fintype.card ι)) :
    a * ascendingEigenvalue hN k - c ≤ ascendingEigenvalue hH k := by
  exact symmetric_eigenvalues_affine_lower N.toEuclideanLin H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hN)
    (Matrix.isHermitian_iff_isSymmetric.mp hH) finrank_euclideanSpace a c ha hNH k.rev

/-- Finite excitation-count consequence. All occurrences are counted with
multiplicity; this is a consequence of operator order, not an extra spectral
assumption. -/
theorem hermitian_count_below_le_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (t : ℝ) :
    (Finset.univ.filter (fun k => ascendingEigenvalue hH k < t)).card ≤
      (Finset.univ.filter (fun k => a * ascendingEigenvalue hN k - c < t)).card := by
  classical
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_le_of_lt
    (hermitian_ascendingEigenvalue_affine_lower N H hN hH a c ha hNH k) hk

/-- A reference-energy-subtracted exponential sum over any chosen index set
is controlled by the comparison spectrum. Taking `s = univ.erase 0` removes
exactly one lowest eigenvalue, even when it is degenerate. No claim that a
comparison frequency equals the interacting physical gap is made. -/
theorem hermitian_exp_sum_le_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (β ground : ℝ) (hβ : 0 ≤ β) (s : Finset (Fin (Fintype.card ι))) :
    (∑ k ∈ s, Real.exp (-β * (ascendingEigenvalue hH k - ground))) ≤
      Real.exp (β * (ground + c)) *
        ∑ k ∈ s, Real.exp (-β * a * ascendingEigenvalue hN k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have he := hermitian_ascendingEigenvalue_affine_lower N H hN hH a c ha hNH k
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr he)]

end BilayerDressed
