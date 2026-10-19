import Dressed.HermitianMinMax

/-!
# From finite Hermitian comparison to the physical thermal tail

The partition function uses the actual eigenvalues of `H`, shifted by its
actual lowest eigenvalue. Exactly one lowest term is removed; any further
ground-state degeneracy remains in the tail. A nonpositive ground energy is
proved from a normalized trial vector, rather than hidden in the comparison.
The exact number-operator distribution is a separate, explicit input.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BilayerDressed

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The actual lowest eigenvalue of a finite real Hermitian matrix. -/
def groundEnergy {H : Matrix ι ι ℝ} (hH : H.IsHermitian) : ℝ :=
  ascendingEigenvalue hH 0

/-- Actual ground-energy-shifted finite spectral partition function. -/
def relativePartition {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  ∑ k, Real.exp (-β * (ascendingEigenvalue hH k - groundEnergy hH))

/-- Exclude one actual lowest eigenvalue, with all other multiplicities intact. -/
def excitedPartition {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase 0,
    Real.exp (-β * (ascendingEigenvalue hH k - groundEnergy hH))

/-- Ground energy is no larger than any normalized Rayleigh quotient. -/
theorem groundEnergy_le_rayleigh (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (x : EuclideanSpace ℝ ι) (hx : ‖x‖ = 1) :
    groundEnergy hH ≤ ⟪x, H.toEuclideanLin x⟫ := by
  have heig (i : ι) : H.toEuclideanLin (hH.eigenvectorBasis i) =
      hH.eigenvalues i • hH.eigenvectorBasis i := by
    ext j
    exact congrFun (hH.mulVec_eigenvectorBasis i) j
  have hmin (i : ι) : groundEnergy hH ≤ hH.eigenvalues i := by
    unfold groundEnergy ascendingEigenvalue Matrix.IsHermitian.eigenvalues
    apply hH.eigenvalues₀_antitone
    apply Fin.rev_le_rev.mp
    simp
  have hmem : x ∈ basisSubspace hH.eigenvectorBasis Set.univ := by
    simpa only [basisSubspace, Set.image_univ, OrthonormalBasis.coe_toBasis] using
      hH.eigenvectorBasis.toBasis.mem_span x
  have hb := lower_rayleigh_on_basisSubspace H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hH) hH.eigenvectorBasis hH.eigenvalues
    heig Set.univ (groundEnergy hH) (fun i _ => hmin i) x hmem
  simpa [hx] using hb

/-- A normalized trial state with nonpositive expectation proves that the
actual lowest energy is nonpositive. No physical-gap premise is used. -/
theorem groundEnergy_nonpos_of_trial (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (x : EuclideanSpace ℝ ι) (hx : ‖x‖ = 1)
    (htrial : ⟪x, H.toEuclideanLin x⟫ ≤ 0) : groundEnergy hH ≤ 0 :=
  (groundEnergy_le_rayleigh H hH x hx).trans htrial

/-- A diagonal matrix entry is the Rayleigh quotient of the corresponding
normalized coordinate vector, hence bounds the actual ground energy above. -/
theorem groundEnergy_le_diagonal (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (i : ι) :
    groundEnergy hH ≤ H i i := by
  have h := groundEnergy_le_rayleigh H hH (EuclideanSpace.basisFun ι ℝ i)
    ((EuclideanSpace.basisFun ι ℝ).norm_eq_one i)
  rw [EuclideanSpace.basisFun_inner] at h
  simpa [Matrix.toEuclideanLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one] using h

/-- In particular, a zero (or negative) vacuum diagonal supplies the
nonpositive ground-energy premise without assuming the physical spectrum. -/
theorem groundEnergy_nonpos_of_diagonal (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (i : ι) (hii : H i i ≤ 0) : groundEnergy hH ≤ 0 :=
  (groundEnergy_le_diagonal H hH i).trans hii

/-- Removing one lowest term subtracts precisely one from the shifted
partition function, regardless of ground-state degeneracy. -/
theorem relativePartition_sub_one_eq_excited {H : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (β : ℝ) :
    relativePartition hH β - 1 = excitedPartition hH β := by
  have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin (Fintype.card ι)))
    (fun k => Real.exp (-β * (ascendingEigenvalue hH k - groundEnergy hH)))
    (Finset.mem_univ (0 : Fin (Fintype.card ι)))
  change _ + excitedPartition hH β = relativePartition hH β at hs
  simp only [groundEnergy, sub_self, mul_zero, Real.exp_zero] at hs
  linarith

theorem excitedPartition_nonneg {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) :
    0 ≤ excitedPartition hH β :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

/-- Exact finite comparison tail before substituting a specific number
operator's product partition function. The ground-energy assumption is
explicit and is derivable from `groundEnergy_nonpos_of_trial`. -/
theorem relativePartition_tail_le_number_sum
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (β : ℝ) (hβ : 0 ≤ β) (hH0 : groundEnergy hH ≤ 0)
    (hN0 : groundEnergy hN = 0) :
    relativePartition hH β - 1 ≤ Real.exp (β * c) *
      ((∑ k, Real.exp (-β * a * ascendingEigenvalue hN k)) - 1) := by
  rw [relativePartition_sub_one_eq_excited]
  have hbound := hermitian_exp_sum_le_affine N H hN hH a c ha hNH
    β (groundEnergy hH) hβ (Finset.univ.erase 0)
  have hpref : Real.exp (β * (groundEnergy hH + c)) ≤ Real.exp (β * c) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hH0]
  have hsum : (∑ k ∈ Finset.univ.erase 0,
        Real.exp (-β * a * ascendingEigenvalue hN k)) =
      (∑ k, Real.exp (-β * a * ascendingEigenvalue hN k)) - 1 := by
    have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin (Fintype.card ι)))
      (fun k => Real.exp (-β * a * ascendingEigenvalue hN k))
      (Finset.mem_univ (0 : Fin (Fintype.card ι)))
    have hz : ascendingEigenvalue hN 0 = 0 := hN0
    simp only [hz, mul_zero, Real.exp_zero] at hs
    linarith
  calc
    excitedPartition hH β ≤ Real.exp (β * (groundEnergy hH + c)) *
        ∑ k ∈ Finset.univ.erase 0, Real.exp (-β * a * ascendingEigenvalue hN k) := hbound
    _ ≤ Real.exp (β * c) *
        ∑ k ∈ Finset.univ.erase 0, Real.exp (-β * a * ascendingEigenvalue hN k) :=
      mul_le_mul_of_nonneg_right hpref
        (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
    _ = _ := by rw [hsum]

/-- Physical ground-subtracted thermal tail for a comparison number operator
with the exact four-state-per-rung partition function. All hypotheses concern
operator forms, a ground trial energy, or the comparison operator's exact
finite spectrum; no interacting-gap or desired-tail hypothesis occurs. -/
theorem relativePartition_tail_le_triplet_product
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (β : ℝ) (hβ : 0 ≤ β) (hH0 : groundEnergy hH ≤ 0)
    (hN0 : groundEnergy hN = 0) (area : ℕ)
    (hnumber : (∑ k, Real.exp (-β * a * ascendingEigenvalue hN k)) =
      (1 + 3 * Real.exp (-β * a))^area) :
    relativePartition hH β - 1 ≤
      Real.exp (β * c) * ((1 + 3 * Real.exp (-β * a))^area - 1) := by
  simpa only [hnumber] using relativePartition_tail_le_number_sum
    N H hN hH a c ha hNH β hβ hH0 hN0

/-- End-to-end finite spectral tail with a concrete vacuum coordinate. -/
theorem relativePartition_tail_le_triplet_product_of_vacuum
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (β : ℝ) (hβ : 0 ≤ β) (vacuum : ι) (hvacuum : H vacuum vacuum ≤ 0)
    (hN0 : groundEnergy hN = 0) (area : ℕ)
    (hnumber : (∑ k, Real.exp (-β * a * ascendingEigenvalue hN k)) =
      (1 + 3 * Real.exp (-β * a))^area) :
    relativePartition hH β - 1 ≤
      Real.exp (β * c) * ((1 + 3 * Real.exp (-β * a))^area - 1) :=
  relativePartition_tail_le_triplet_product N H hN hH a c ha hNH β hβ
    (groundEnergy_nonpos_of_diagonal H hH vacuum hvacuum) hN0 area hnumber

/-- The same form comparison bounds an actual excitation energy once the
corresponding exact number eigenvalue is known to be at least one. The
physical ground subtraction is explicit. -/
theorem excitationEnergy_lower_of_number_ge_one
    (N H : Matrix ι ι ℝ) (hN : N.IsHermitian) (hH : H.IsHermitian)
    (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ ι,
      a * ⟪x, N.toEuclideanLin x⟫ - c * ‖x‖^2 ≤ ⟪x, H.toEuclideanLin x⟫)
    (hH0 : groundEnergy hH ≤ 0) (k : Fin (Fintype.card ι))
    (hNk : 1 ≤ ascendingEigenvalue hN k) :
    a - c ≤ ascendingEigenvalue hH k - groundEnergy hH := by
  have he := hermitian_ascendingEigenvalue_affine_lower N H hN hH a c ha hNH k
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hNk)]

omit [Nonempty ι] in
/-- Exact root multiset for a real diagonal matrix, including repetitions. -/
theorem diagonal_charpoly_roots (d : ι → ℝ) :
    (Matrix.diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

omit [Nonempty ι] in
/-- A diagonal number operator's actual sorted spectral sum equals its
explicit configuration sum for every real-valued spectral function. -/
theorem sum_ascendingEigenvalue_diagonal (d : ι → ℝ)
    (hD : (Matrix.diagonal d).IsHermitian) (f : ℝ → ℝ) :
    (∑ k, f (ascendingEigenvalue hD k)) = ∑ i, f (d i) := by
  have hroots : Multiset.map (ascendingEigenvalue hD) Finset.univ.val =
      Multiset.map d Finset.univ.val := by
    rw [← roots_charpoly_eq_ascendingEigenvalue hD, diagonal_charpoly_roots]
  have hf := congrArg (fun s : Multiset ℝ => (s.map f).sum) hroots
  simpa only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using hf

/-- Positive semidefiniteness bounds the actual ground energy below by zero. -/
theorem groundEnergy_nonneg_of_posSemidef (H : Matrix ι ι ℝ)
    (hH : H.IsHermitian) (hpos : H.PosSemidef) : 0 ≤ groundEnergy hH := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  have h := hpos.eigenvalues_nonneg (e ((0 : Fin (Fintype.card ι)).rev))
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply,
    groundEnergy, ascendingEigenvalue] using h

/-- A nonnegative diagonal number operator with one explicit zero entry has
actual lowest eigenvalue zero. Uniqueness is not required for this statement. -/
theorem groundEnergy_diagonal_eq_zero (d : ι → ℝ)
    (hD : (Matrix.diagonal d).IsHermitian) (hd : ∀ i, 0 ≤ d i)
    (vacuum : ι) (hzero : d vacuum = 0) : groundEnergy hD = 0 := by
  apply le_antisymm
  · simpa [hzero] using groundEnergy_le_diagonal (Matrix.diagonal d) hD vacuum
  · exact groundEnergy_nonneg_of_posSemidef (Matrix.diagonal d) hD
      (Matrix.PosSemidef.diagonal hd)

omit [Nonempty ι] in
/-- Spectral sublevel counts of a diagonal matrix agree exactly with the
explicit diagonal-data counts, including repeated eigenvalues. -/
theorem card_ascendingEigenvalue_lt_diagonal (d : ι → ℝ)
    (hD : (Matrix.diagonal d).IsHermitian) (t : ℝ) :
    (Finset.univ.filter (fun k => ascendingEigenvalue hD k < t)).card =
      (Finset.univ.filter (fun i => d i < t)).card := by
  classical
  have hroots : Multiset.map (ascendingEigenvalue hD) Finset.univ.val =
      Multiset.map d Finset.univ.val := by
    rw [← roots_charpoly_eq_ascendingEigenvalue hD, diagonal_charpoly_roots]
  have hc := congrArg (Multiset.countP (fun r : ℝ => r < t)) hroots
  simpa only [Multiset.countP_map] using hc

/-- If a diagonal number operator has one zero vacuum and every non-vacuum
configuration has energy at least one, every nonlowest actual sorted
eigenvalue is at least one. This proves the spectral threshold from concrete
diagonal data and multiplicities, rather than assuming it. -/
theorem ascendingEigenvalue_diagonal_ge_one (d : ι → ℝ)
    (hD : (Matrix.diagonal d).IsHermitian) (vacuum : ι) (hzero : d vacuum = 0)
    (hother : ∀ i, i ≠ vacuum → 1 ≤ d i)
    (k : Fin (Fintype.card ι)) (hk : k ≠ 0) :
    1 ≤ ascendingEigenvalue hD k := by
  classical
  have hnonneg (i : ι) : 0 ≤ d i := by
    by_cases hi : i = vacuum
    · simp [hi, hzero]
    · linarith [hother i hi]
  have hg := groundEnergy_diagonal_eq_zero d hD hnonneg vacuum hzero
  have hfilter : Finset.univ.filter (fun i => d i < 1) = {vacuum} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      by_contra hne
      exact (not_lt_of_ge (hother i hne)) hi
    · intro hi
      simp [hi, hzero]
  have hcard : (Finset.univ.filter
      (fun j => ascendingEigenvalue hD j < 1)).card ≤ 1 := by
    rw [card_ascendingEigenvalue_lt_diagonal, hfilter]
    simp
  apply le_of_not_gt
  intro hlt
  apply hk
  apply Finset.card_le_one.mp hcard k
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt) 0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change groundEnergy hD < 1
  rw [hg]
  norm_num

end BilayerDressed
