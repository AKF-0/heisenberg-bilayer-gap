import Dressed.FiniteOscillator
import Dressed.NumberThermalTail

/-!
# The full finite occupation-cutoff oscillator spectrum

The two parity blocks are merged through exact characteristic polynomials and
Loewner comparison of diagonal matrices, retaining all multiplicities.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOscillator
open Matrix
set_option maxHeartbeats 800000

/-- Increasing spectral enumeration with the concrete finite matrix index. -/
def increasingValue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (j : Fin n) : ℝ :=
  ascendingEigenvalue hA (Fin.cast (Fintype.card_fin n).symm j)

theorem prod_ascendingEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {R : Type*} [CommMonoid R] (f : ℝ → R) :
    (∏ k, f (ascendingEigenvalue hA k)) = ∏ i, f (hA.eigenvalues i) := by
  calc
    _ = ∏ k, f (hA.eigenvalues₀ k) :=
      Equiv.prod_comp Fin.revPerm (fun k => f (hA.eigenvalues₀ k))
    _ = _ := by
      symm
      exact (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.prod_comp
        (fun k => f (hA.eigenvalues₀ k))

/-- Diagonalizing and increasing reordering preserve the full characteristic
polynomial, rather than just the set of distinct eigenvalues. -/
theorem charpoly_eq_diagonal_increasing {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : A.charpoly = (diagonal (increasingValue hA)).charpoly := by
  rw [hA.charpoly_eq, charpoly_diagonal]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hp := prod_ascendingEigenvalue hA (fun x => Polynomial.X-Polynomial.C x)
  rw [← hp]
  exact ((finCongr (Fintype.card_fin n).symm).prod_comp
    (fun k => Polynomial.X-Polynomial.C (ascendingEigenvalue hA k))).symm

/-- Increasing diagonal entries are exactly the actual ordered eigenvalues. -/
theorem increasingValue_diagonal {n : ℕ} (d : Fin n → ℝ) (hd : Monotone d) :
    increasingValue (isHermitian_diagonal d) = d := by
  have hroots : Multiset.map (increasingValue (isHermitian_diagonal d)) Finset.univ.val =
      Multiset.map d Finset.univ.val := by
    have hr := roots_charpoly_eq_ascendingEigenvalue (isHermitian_diagonal d)
    rw [diagonal_charpoly_roots] at hr
    rw [hr]
    unfold increasingValue
    change Multiset.map (ascendingEigenvalue (isHermitian_diagonal d) ∘
      (finCongr (Fintype.card_fin n).symm)) Finset.univ.val = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  apply List.ofFn_inj.mp
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · simpa only [Fin.univ_val_map, Multiset.coe_eq_coe] using hroots
  · apply Monotone.ofFn_sorted
    intro i j hij
    exact ascendingEigenvalue_monotone (isHermitian_diagonal d) hij
  · exact hd.ofFn_sorted

/-- The two finite parity index sets for levels `0,...,m-1`. -/
abbrev ParityIndex (m : ℕ) := Fin ((m+1)/2) ⊕ Fin (m/2)

/-- Interleave the even and odd occupation labels. -/
def parityLabel (m : ℕ) : ParityIndex m → Fin m
  | .inl i => ⟨2*i.val, by have hi := i.isLt; omega⟩
  | .inr i => ⟨2*i.val+1, by have hi := i.isLt; omega⟩

theorem parityLabel_bijective (m : ℕ) : Function.Bijective (parityLabel m) := by
  constructor
  · intro i j h
    have hval := congrArg Fin.val h
    cases i with
    | inl i =>
      cases j with
      | inl j => congr 1; apply Fin.ext; dsimp [parityLabel] at hval; omega
      | inr j => dsimp [parityLabel] at hval; omega
    | inr i =>
      cases j with
      | inl j => dsimp [parityLabel] at hval; omega
      | inr j => congr 1; apply Fin.ext; dsimp [parityLabel] at hval; omega
  · intro i
    by_cases hi : i.val % 2 = 0
    · refine ⟨.inl ⟨i.val/2, by have h := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp [parityLabel]
      omega
    · refine ⟨.inr ⟨i.val/2, by have h := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp [parityLabel]
      omega

/-- Exact parity permutation, including the empty odd block when `m=1`. -/
def parityEquiv (m : ℕ) : ParityIndex m ≃ Fin m :=
  Equiv.ofBijective (parityLabel m) (parityLabel_bijective m)

/-- The parity permutation block diagonalizes the actual finite cutoff. -/
theorem occupationMatrix_parity_reindex (m : ℕ) (ω z : ℝ) :
    (occupationMatrix m ω z).submatrix (parityEquiv m) (parityEquiv m) =
      fromBlocks (parityBlock ((m+1)/2) 0 ω z) 0 0 (parityBlock (m/2) 1 ω z) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hcut (i : Fin ((m+1)/2)) : 2*i.val+(0 : Fin 2).val < m := by
        have hi := i.isLt
        simp only [Fin.val_zero]
        omega
      have hh := congrFun (congrFun (occupationMatrix_parity_submatrix m ((m+1)/2)
        0 hcut ω z) i) j
      simpa [submatrix_apply, parityIndex, parityEquiv, parityLabel] using hh
    | inr j =>
      have hne : (parityEquiv m) (.inl i) ≠ (parityEquiv m) (.inr j) := by
        intro h
        have hh := (parityEquiv m).injective h
        cases hh
      have hu : 2*i.val+2 ≠ 2*j.val+1 := by omega
      have hl : (2*j.val+1)+2 ≠ 2*i.val := by omega
      simp [submatrix_apply, occupationMatrix, diagonal_apply, hne, pairUpper,
        parityEquiv, parityLabel, hu, hl]
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hne : (parityEquiv m) (.inr i) ≠ (parityEquiv m) (.inl j) := by
        intro h
        have hh := (parityEquiv m).injective h
        cases hh
      have hu : (2*i.val+1)+2 ≠ 2*j.val := by omega
      have hl : 2*j.val+2 ≠ 2*i.val+1 := by omega
      simp [submatrix_apply, occupationMatrix, diagonal_apply, hne, pairUpper,
        parityEquiv, parityLabel, hu, hl]
      omega
    | inr j =>
      have hcut (i : Fin (m/2)) : 2*i.val+(1 : Fin 2).val < m := by
        have hi := i.isLt
        simp only [Fin.val_one]
        omega
      have hh := congrFun (congrFun (occupationMatrix_parity_submatrix m (m/2)
        1 hcut ω z) i) j
      simpa [submatrix_apply, parityIndex, parityEquiv, parityLabel] using hh

/-- Actual ordered parity eigenvalues, labelled by their occupation number. -/
def parityEnergy (m : ℕ) (ω z : ℝ) : ParityIndex m → ℝ :=
  Sum.elim (increasingValue (parityBlock_hermitian ((m+1)/2) 0 ω z))
    (increasingValue (parityBlock_hermitian (m/2) 1 ω z))

/-- The full occupation matrix is isospectral, with multiplicity, to the
finite diagonal list of its two actual parity spectra. -/
theorem occupationMatrix_charpoly_diagonal (m : ℕ) (ω z : ℝ) :
    (occupationMatrix m ω z).charpoly =
      (diagonal (fun i : Fin m => parityEnergy m ω z ((parityEquiv m).symm i))).charpoly := by
  have hperm := charpoly_reindex (parityEquiv m).symm (occupationMatrix m ω z)
  change ((occupationMatrix m ω z).submatrix (parityEquiv m) (parityEquiv m)).charpoly = _ at hperm
  rw [occupationMatrix_parity_reindex, charpoly_fromBlocks_zero₁₂] at hperm
  rw [charpoly_eq_diagonal_increasing (parityBlock_hermitian ((m+1)/2) 0 ω z),
    charpoly_eq_diagonal_increasing (parityBlock_hermitian (m/2) 1 ω z)] at hperm
  have hd : (diagonal (parityEnergy m ω z)).charpoly =
      (diagonal (increasingValue (parityBlock_hermitian ((m+1)/2) 0 ω z))).charpoly *
      (diagonal (increasingValue (parityBlock_hermitian (m/2) 1 ω z))).charpoly := by
    simp [charpoly_diagonal, Fintype.prod_sum_type, parityEnergy]
  have hr := charpoly_reindex (parityEquiv m) (diagonal (parityEnergy m ω z))
  have hdiag : reindex (parityEquiv m) (parityEquiv m) (diagonal (parityEnergy m ω z)) =
      diagonal (fun i : Fin m => parityEnergy m ω z ((parityEquiv m).symm i)) := by
    ext i j
    simp [reindex_apply, diagonal_apply, (parityEquiv m).symm.injective.eq_iff]
  rw [hdiag, hd] at hr
  exact hperm.symm.trans hr.symm

/-- Pointwise comparison between the labelled finite parity spectrum and the
linear occupation template. -/
theorem parityEnergy_lower (m : ℕ) (ω z : ℝ) (h : |z| < ω) (i : ParityIndex m) :
    vacuumEnergy ω z + ((parityEquiv m i).val:ℝ)*frequency ω z ≤ parityEnergy m ω z i := by
  cases i with
  | inl i =>
    simpa [parityEnergy, increasingValue, parityEquiv, parityLabel] using
      parityBlock_ascendingEigenvalue_lower ((m+1)/2) 0 ω z (by norm_num) h i
  | inr i =>
    simpa [parityEnergy, increasingValue, parityEquiv, parityLabel] using
      parityBlock_ascendingEigenvalue_lower (m/2) 1 ω z (by norm_num) h i

/-- Full finite single-mode oscillator theorem. Every actual increasingly
ordered eigenvalue of the cutoff on levels `0,...,m-1` is at least `e+jΩ`.
There are no spectral hypotheses, and both parity blocks may have unequal size. -/
theorem occupationMatrix_ascendingEigenvalue_lower (m : ℕ) (ω z : ℝ)
    (h : |z| < ω) (j : Fin m) :
    vacuumEnergy ω z + (j.val:ℝ)*frequency ω z ≤
      ascendingEigenvalue (occupationMatrix_hermitian m ω z)
        (Fin.cast (Fintype.card_fin m).symm j) := by
  let d : Fin m → ℝ := fun i => vacuumEnergy ω z+(i.val:ℝ)*frequency ω z
  let a : Fin m → ℝ := fun i => parityEnergy m ω z ((parityEquiv m).symm i)
  have hda (i : Fin m) : d i ≤ a i := by
    simpa [d, a] using parityEnergy_lower m ω z h ((parityEquiv m).symm i)
  have hmono : Monotone d := by
    intro i k hik
    dsimp [d]
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hik
    · exact (stable_parameters ω z h).1.le
  have hpsd : (diagonal a-diagonal d).PosSemidef := by
    rw [diagonal_sub]
    exact PosSemidef.diagonal (fun i => sub_nonneg.mpr (hda i))
  have hcomp := hermitian_ascendingEigenvalue_mono_of_posSemidef
    (diagonal d) (diagonal a) (isHermitian_diagonal d) (isHermitian_diagonal a)
    hpsd (Fin.cast (Fintype.card_fin m).symm j)
  have hspec : (occupationMatrix_hermitian m ω z).eigenvalues₀ =
      (isHermitian_diagonal a).eigenvalues₀ :=
    hermitian_eigenvalues₀_eq_of_charpoly_eq _ _ (occupationMatrix_charpoly_diagonal m ω z)
  have hval := congrFun (increasingValue_diagonal d hmono) j
  unfold increasingValue at hval
  rw [hval] at hcomp
  unfold ascendingEigenvalue at hcomp ⊢
  rw [hspec]
  exact hcomp

/-- The exact negative reference energy has the useful common-frequency
lower bound. This permits a single occupation template after mode summation. -/
theorem vacuumEnergy_common_lower (ω z a : ℝ) (h : |z| < ω)
    (ha : 0 < a) (haΩ : a ≤ frequency ω z) :
    -z^2/(2*(ω+a)) ≤ vacuumEnergy ω z := by
  obtain ⟨hΩ, hs, ht, hst⟩ := stable_parameters ω z h
  have hω : 0 < ω := lt_of_le_of_lt (abs_nonneg z) h
  have hden : 0 < 2*(ω+a) := by positivity
  apply (div_le_iff₀ hden).mpr
  unfold vacuumEnergy
  nlinarith [mul_nonneg hs (sub_nonneg.mpr haΩ)]

/-- Common-frequency finite oscillator bound, suitable for a reference of
the form `constant I + a N` after summing the individual modes. -/
theorem occupationMatrix_common_frequency_lower (m : ℕ) (ω z a : ℝ)
    (h : |z| < ω) (ha : 0 < a) (haΩ : a ≤ frequency ω z) (j : Fin m) :
    -z^2/(2*(ω+a)) + a*(j.val:ℝ) ≤
      ascendingEigenvalue (occupationMatrix_hermitian m ω z)
        (Fin.cast (Fintype.card_fin m).symm j) := by
  have he := vacuumEnergy_common_lower ω z a h ha haΩ
  have hmode := occupationMatrix_ascendingEigenvalue_lower m ω z h j
  have hlevel := mul_le_mul_of_nonneg_left haΩ (Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val)
  nlinarith

end BilayerDressed.FiniteOscillator
