import Dressed.FiniteProductSpectrum
import Dressed.HermitianCompressionLower

/-!
# Finite common-frequency product oscillator reference

The reference is a sum of the actual finite occupation-cutoff oscillators.
Its tensor eigenbasis and local eigenvalues come from proved finite spectral
theorems. Only the still-separate physical embedding and operator comparison
are hypotheses in the final compression interface.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteProduct
open Matrix
set_option maxHeartbeats 800000
variable {I : Type*} [Fintype I] [DecidableEq I]

section MatrixForms
variable {S : Type*} [Fintype S] [DecidableEq S]
/-- An explicitly orthogonal real matrix acts isometrically on the Euclidean space. -/
theorem orthogonalMatrix_norm (Q : Matrix S S ℝ) (hQ : Q.transpose * Q = 1)
    (x : EuclideanSpace ℝ S) : ‖Q.toEuclideanLin x‖ = ‖x‖ := by
  have hi : ⟪Q.toEuclideanLin x, Q.toEuclideanLin x⟫ = ⟪x, x⟫ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      star_trivial]
    calc
      (Q *ᵥ WithLp.ofLp x) ⬝ᵥ (Q *ᵥ WithLp.ofLp x) =
          WithLp.ofLp x ⬝ᵥ (Q.transpose *ᵥ (Q *ᵥ WithLp.ofLp x)) := by
        conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = _ := by rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (Q.toEuclideanLin x), norm_nonneg x]

/-- Exact scalar-affine quadratic form of diagonal data. -/
theorem diagonal_affine_form (d : S → ℝ) (a c : ℝ) (x : EuclideanSpace ℝ S) :
    ⟪x, (diagonal (fun i => c+a*d i)).toEuclideanLin x⟫ =
      a * ⟪x, (diagonal d).toEuclideanLin x⟫ + c * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    star_trivial, Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (c+a*d i)*x i*x i = a*(d i*x i*x i)+c*‖x i‖^2
  rw [Real.norm_eq_abs, sq_abs]
  ring
end MatrixForms

/-- Integer total label number, represented as a real diagonal entry. -/
def numberEnergy {m : ℕ} (s : I → Fin m) : ℝ := ∑ i, ((s i).val : ℝ)

/-- The simple number operator on the product spectral-label space. -/
def number (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) :
    Matrix (I → Fin m) (I → Fin m) ℝ := diagonal numberEnergy

theorem numberEnergy_nonneg {m : ℕ} (s : I → Fin m) : 0 ≤ numberEnergy s := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

@[simp] theorem numberEnergy_zero (M : ℕ) :
    numberEnergy (fun _ : I => (0 : Fin (M+1))) = 0 := by
  simp [numberEnergy]

/-- Every label other than the unique zero label has total number at least one. -/
theorem one_le_numberEnergy {M : ℕ} (s : I → Fin (M+1))
    (hs : s ≠ fun _ => 0) : 1 ≤ numberEnergy s := by
  classical
  have hex : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  obtain ⟨i, hi⟩ := hex
  have hval : 1 ≤ (s i).val := by
    have hn : (s i).val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  have hterm : (1 : ℝ) ≤ ((s i).val : ℝ) := by exact_mod_cast hval
  exact hterm.trans (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (s j).val)
    (Finset.mem_univ i))

/-- Exact finite product partition, with no infinite-mode or convergence input. -/
theorem number_configuration_partition (m : ℕ) (t : ℝ) :
    (∑ s : I → Fin m, Real.exp (t * numberEnergy s)) =
      (∑ j : Fin m, Real.exp (t * (j.val : ℝ))) ^ Fintype.card I := by
  classical
  simp_rw [numberEnergy, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (_ : I) (j : Fin m) => Real.exp (t * (j.val : ℝ)))]
  simp

theorem number_spectral_partition (m : ℕ) (t : ℝ) :
    (∑ k, Real.exp (t * ascendingEigenvalue (isHermitian_diagonal
      (numberEnergy (I := I) (m := m))) k)) =
      (∑ j : Fin m, Real.exp (t * (j.val : ℝ))) ^ Fintype.card I := by
  rw [sum_ascendingEigenvalue_diagonal _ _ (fun x => Real.exp (t * x))]
  exact number_configuration_partition m t

theorem number_groundEnergy (M : ℕ) :
    groundEnergy (isHermitian_diagonal (numberEnergy (I := I) (m := M+1))) = 0 :=
  groundEnergy_diagonal_eq_zero _ _ numberEnergy_nonneg (fun _ => 0) (numberEnergy_zero M)

theorem number_excitedEigenvalue (M : ℕ) (k : Fin (Fintype.card (I → Fin (M+1))))
    (hk : k ≠ 0) :
    1 ≤ ascendingEigenvalue (isHermitian_diagonal
      (numberEnergy (I := I) (m := M+1))) k :=
  ascendingEigenvalue_diagonal_ge_one _ _ (fun _ => 0) (numberEnergy_zero M)
    one_le_numberEnergy k hk

/-- Summed affine lower bounds for the actual product spectral labels. -/
theorem spectralEnergy_affine_lower {m : ℕ}
    (A : I → Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i, (A i).IsHermitian)
    (e : I → ℝ) (a c : ℝ) (hc : c ≤ ∑ i, e i)
    (hloc : ∀ i j, e i + a * (j.val : ℝ) ≤ FiniteOscillator.increasingValue (hA i) j)
    (s : I → Fin m) : c + a * numberEnergy s ≤ spectralEnergy A hA s := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hloc i (s i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact (add_le_add_right hc _).trans hsum

/-- Common-frequency lower operator bound in the genuine product eigenbasis. -/
theorem spectralMatrix_affine_lower {m : ℕ}
    (A : I → Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i, (A i).IsHermitian)
    (e : I → ℝ) (a c : ℝ) (hc : c ≤ ∑ i, e i)
    (hloc : ∀ i j, e i + a * (j.val : ℝ) ≤ FiniteOscillator.increasingValue (hA i) j) :
    ((spectralMatrix A hA).transpose * hamiltonian A * spectralMatrix A hA -
      diagonal (fun s => c + a * numberEnergy s)).PosSemidef := by
  rw [spectralMatrix_diagonalization, diagonal_sub]
  exact PosSemidef.diagonal (fun s => sub_nonneg.mpr
    (spectralEnergy_affine_lower A hA e a c hc hloc s))

/-- Genuine finite product oscillator, with heterogeneous pair couplings. -/
def oscillator (m : ℕ) (ω : ℝ) (z : I → ℝ) : Matrix (I → Fin m) (I → Fin m) ℝ :=
  hamiltonian (fun i => FiniteOscillator.occupationMatrix m ω (z i))

/-- Instantiation by the proved finite oscillator theorem, not by a supplied
spectral lower bound. A common positive frequency is the only scalar input. -/
theorem oscillator_common_frequency_lower (m : ℕ) (ω a c : ℝ) (z : I → ℝ)
    (hstable : ∀ i, |z i| < ω) (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency ω (z i))
    (hc : c ≤ ∑ i, -(z i)^2 / (2 * (ω+a))) :
    ((spectralMatrix (fun i => FiniteOscillator.occupationMatrix m ω (z i))
      (fun i => FiniteOscillator.occupationMatrix_hermitian m ω (z i))).transpose *
      oscillator m ω z *
      spectralMatrix (fun i => FiniteOscillator.occupationMatrix m ω (z i))
        (fun i => FiniteOscillator.occupationMatrix_hermitian m ω (z i)) -
      diagonal (fun s => c + a * numberEnergy s)).PosSemidef := by
  apply spectralMatrix_affine_lower _ _ (fun i => -(z i)^2 / (2*(ω+a))) a c hc
  intro i j
  exact FiniteOscillator.occupationMatrix_common_frequency_lower m ω (z i) a
    (hstable i) ha (hfreq i) j

/-- The actual tensor spectral matrix is a norm-preserving basis transformation. -/
theorem spectralMatrix_norm {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ (I → Fin m)) :
    ‖(spectralMatrix A hA).toEuclideanLin x‖ = ‖x‖ :=
  orthogonalMatrix_norm _ (spectralMatrix_orthogonal A hA) x

/-- The full tensor eigenbasis transformation is injective. -/
theorem spectralMatrix_injective {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    Function.Injective (spectralMatrix A hA).toEuclideanLin := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← spectralMatrix_norm A hA (x-y), map_sub, h, sub_self, norm_zero]

/-- Concrete common-frequency operator form in the actual finite oscillator
eigenbasis. The isometry used here is constructed, not hypothesized. -/
theorem oscillator_common_frequency_form (m : ℕ) (ω a c : ℝ) (z : I → ℝ)
    (hstable : ∀ i, |z i| < ω) (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency ω (z i))
    (hc : c ≤ ∑ i, -(z i)^2 / (2 * (ω+a)))
    (x : EuclideanSpace ℝ (I → Fin m)) :
    a * ⟪x, (number I m).toEuclideanLin x⟫ + c * ‖x‖^2 ≤
      ⟪x, ((spectralMatrix (fun i => FiniteOscillator.occupationMatrix m ω (z i))
        (fun i => FiniteOscillator.occupationMatrix_hermitian m ω (z i))).transpose *
        oscillator m ω z *
        spectralMatrix (fun i => FiniteOscillator.occupationMatrix m ω (z i))
          (fun i => FiniteOscillator.occupationMatrix_hermitian m ω (z i))).toEuclideanLin x⟫ := by
  have h := quadraticForm_le_of_sub_posSemidef _ _
    (oscillator_common_frequency_lower m ω a c z hstable ha hfreq hc) x
  rw [diagonal_affine_form] at h
  exact h

end BilayerDressed.FiniteProduct

namespace BilayerDressed
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Zero-excluded thermal comparison through an isometry into a larger space.
The extra ambient levels can only enlarge the template sum. Exactly one actual
lowest physical term and one lowest template term are removed. -/
theorem relativePartition_tail_le_embedded_number
    (N : Matrix κ κ ℝ) (H : Matrix ι ι ℝ)
    (hN : N.IsHermitian) (hH : H.IsHermitian)
    (f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ)
    (hf : Function.Injective f) (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (a c U β : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hform : ∀ x, a * ⟪f x, N.toEuclideanLin (f x)⟫ + c * ‖x‖^2 ≤
      ⟪x, H.toEuclideanLin x⟫)
    (hU : groundEnergy hH ≤ U) (hN0 : groundEnergy hN = 0) :
    relativePartition hH β - 1 ≤ Real.exp (β * (U-c)) *
      ((∑ j, Real.exp (-β * a * ascendingEigenvalue hN j)) - 1) := by
  classical
  have hdim : Fintype.card ι ≤ Fintype.card κ := by
    simpa only [finrank_euclideanSpace] using LinearMap.finrank_le_finrank_of_injective hf
  let e : Fin (Fintype.card ι) → Fin (Fintype.card κ) := Fin.castLE hdim
  have hpoint (k : Fin (Fintype.card ι)) :
      Real.exp (-β * (ascendingEigenvalue hH k-groundEnergy hH)) ≤
        Real.exp (β * (U-c)) * Real.exp (-β*a*ascendingEigenvalue hN (e k)) := by
    have he := hermitian_ascendingEigenvalue_affine_embedding_lower N H hN hH f hf hnorm
      a (-c) ha (by intro x; simpa using hform x) k (lt_of_lt_of_le k.isLt hdim)
    change a * ascendingEigenvalue hN (e k) - (-c) ≤ ascendingEigenvalue hH k at he
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr he),
      mul_nonneg hβ (sub_nonneg.mpr hU)]
  have hsub : (Finset.univ.erase (0 : Fin (Fintype.card ι))).image e ⊆
      Finset.univ.erase (0 : Fin (Fintype.card κ)) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    apply (Finset.mem_erase.mp hk).1
    apply Fin.ext
    simpa only [e, Fin.coe_castLE, Fin.val_zero] using
      congrArg (fun j : Fin (Fintype.card κ) => j.val) h
  have hsum : (∑ k ∈ Finset.univ.erase (0 : Fin (Fintype.card ι)),
        Real.exp (-β*a*ascendingEigenvalue hN (e k))) ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin (Fintype.card κ)),
        Real.exp (-β*a*ascendingEigenvalue hN j) := by
    have hi : Function.Injective e := Fin.castLE_injective hdim
    rw [← Finset.sum_image (f := fun j => Real.exp (-β*a*ascendingEigenvalue hN j)) hi.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => (Real.exp_pos _).le)
  have hremove : (∑ j ∈ Finset.univ.erase (0 : Fin (Fintype.card κ)),
        Real.exp (-β*a*ascendingEigenvalue hN j)) =
      (∑ j, Real.exp (-β*a*ascendingEigenvalue hN j))-1 := by
    have hh := Finset.add_sum_erase (Finset.univ : Finset (Fin (Fintype.card κ)))
      (fun j => Real.exp (-β*a*ascendingEigenvalue hN j)) (Finset.mem_univ 0)
    have hz : ascendingEigenvalue hN 0 = 0 := hN0
    simp only [hz, mul_zero, Real.exp_zero] at hh
    linarith
  rw [relativePartition_sub_one_eq_excited]
  calc
    excitedPartition hH β ≤ Real.exp (β*(U-c)) *
        ∑ k ∈ Finset.univ.erase (0 : Fin (Fintype.card ι)),
          Real.exp (-β*a*ascendingEigenvalue hN (e k)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k _ => hpoint k)
    _ ≤ Real.exp (β*(U-c)) *
        ∑ j ∈ Finset.univ.erase (0 : Fin (Fintype.card κ)),
          Real.exp (-β*a*ascendingEigenvalue hN j) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by rw [hremove]

end BilayerDressed

namespace BilayerDressed.FiniteProduct
open Matrix
variable {I ι : Type*} [Fintype I] [DecidableEq I]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Final finite product-label thermal interface. The isometry and its physical
operator-form comparison remain explicit, so this does not assert that the
hard-core model has already been connected to the oscillator reference. -/
theorem relativePartition_tail_le_product_number (M : ℕ)
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (I → Fin (M+1)))
    (hf : Function.Injective f) (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (a c U β : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hform : ∀ x, a * ⟪f x, (number I (M+1)).toEuclideanLin (f x)⟫ + c * ‖x‖^2 ≤
      ⟪x, H.toEuclideanLin x⟫)
    (hU : groundEnergy hH ≤ U) :
    relativePartition hH β - 1 ≤ Real.exp (β*(U-c)) *
      ((∑ j : Fin (M+1), Real.exp (-β*a*(j.val : ℝ))) ^ Fintype.card I - 1) := by
  have ht := relativePartition_tail_le_embedded_number (number I (M+1)) H
    (isHermitian_diagonal _) hH f hf hnorm a c U β ha hβ hform hU (number_groundEnergy M)
  rw [number_spectral_partition (M+1) (-β*a)] at ht
  exact ht

/-- Every nonlowest physical level lies above the same common-frequency
threshold. Subtracting a proven physical ground upper bound gives a true gap
bound; the reference constant is not presumed to be attained. -/
theorem excitationEnergy_lower_of_product_number (M : ℕ)
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (I → Fin (M+1)))
    (hf : Function.Injective f) (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (a c U : ℝ) (ha : 0 ≤ a)
    (hform : ∀ x, a * ⟪f x, (number I (M+1)).toEuclideanLin (f x)⟫ + c * ‖x‖^2 ≤
      ⟪x, H.toEuclideanLin x⟫)
    (hU : groundEnergy hH ≤ U) (k : Fin (Fintype.card ι)) (hk : k ≠ 0) :
    c+a-U ≤ ascendingEigenvalue hH k-groundEnergy hH := by
  have hdim : Fintype.card ι ≤ Fintype.card (I → Fin (M+1)) := by
    simpa only [finrank_euclideanSpace] using LinearMap.finrank_le_finrank_of_injective hf
  have he := hermitian_ascendingEigenvalue_affine_embedding_lower (number I (M+1)) H
    (isHermitian_diagonal _) hH f hf hnorm a (-c) ha
    (by intro x; simpa using hform x) k (lt_of_lt_of_le k.isLt hdim)
  have hnonzero : (⟨k.val, lt_of_lt_of_le k.isLt hdim⟩ :
      Fin (Fintype.card (I → Fin (M+1)))) ≠ 0 := by
    intro h
    apply hk
    apply Fin.ext
    simpa using congrArg (fun j : Fin (Fintype.card (I → Fin (M+1))) => j.val) h
  have hn := number_excitedEigenvalue (I := I) M _ hnonzero
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hn)]

end BilayerDressed.FiniteProduct
