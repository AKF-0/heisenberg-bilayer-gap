import Dressed.PhysicalProductComparison
import Dressed.ReferenceAdjacencyBounds
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Explicit reference constants through coupling one tenth

Both the sharp common frequency sqrt(1-4g) and the fixed rational constants
used by the separate scalar certificates are retained. The fixed reference is
exactly a=387/500 and c=-(750/787) A g²; no certificate constant is changed.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.PhysicalReferencePointOne
open Matrix FiniteOccupation PhysicalProduct BilayerGap
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Sharp degree-four common oscillator frequency. -/
def commonFrequency (g : ℝ) : ℝ := Real.sqrt (1-4*g)

/-- Summed sharp common-frequency reference shift for area A. -/
def referenceShift (A g : ℝ) : ℝ := -(3*A*g^2) / (2*((1-2*g)+commonFrequency g))

/-- The exact rational frequency used by the fixed finite certificates. -/
def fixedFrequency : ℝ := 387/500

/-- The exact rational reference shift used by those certificates. -/
def fixedShift (A g : ℝ) : ℝ := -(750*A*g^2)/787

@[simp] theorem fixedFrequency_pos : 0 < fixedFrequency := by norm_num [fixedFrequency]

theorem fixedFrequency_le_common (g : ℝ) (hgmax : g ≤ 1/10) :
    fixedFrequency ≤ commonFrequency g := by
  unfold fixedFrequency commonFrequency
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem commonFrequency_pos (g : ℝ) (hgmax : g ≤ 1/10) : 0 < commonFrequency g :=
  lt_of_lt_of_le fixedFrequency_pos (fixedFrequency_le_common g hgmax)

theorem mode_stable (g z : ℝ) (hgmax : g ≤ 1/10) (hz : |z| ≤ 2*g) :
    |z| < 1-2*g := by
  have ht : 2*g < 1-2*g := by linarith
  exact hz.trans_lt ht

theorem mode_square_bound (g z : ℝ) (hz : |z| ≤ 2*g) : z^2 ≤ (2*g)^2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  have hp := mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0 ≤ 2*g+z)
  nlinarith

theorem commonFrequency_le_mode (g z : ℝ) (hz : |z| ≤ 2*g) :
    commonFrequency g ≤ FiniteOscillator.frequency (1-2*g) z := by
  apply Real.sqrt_le_sqrt
  have hs := mode_square_bound g z hz
  nlinarith

theorem fixedFrequency_le_mode (g z : ℝ) (hgmax : g ≤ 1/10) (hz : |z| ≤ 2*g) :
    fixedFrequency ≤ FiniteOscillator.frequency (1-2*g) z :=
  (fixedFrequency_le_common g hgmax).trans (commonFrequency_le_mode g z hz)

section Sums
variable {I : Type*} [Fintype I]

/-- The actual squared trace gives the sharp summed reference constant exactly. -/
theorem referenceShift_eq_sum (A g : ℝ) (z : I → ℝ)
    (hsq : ∑ i, (z i)^2 = 3*A*g^2) :
    referenceShift A g = ∑ i, -(z i)^2 / (2*((1-2*g)+commonFrequency g)) := by
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hsq]
  rfl

/-- The fixed rational shift is conservative throughout the entire interval,
not just at g=1/10. -/
theorem fixedShift_le_sum (A g : ℝ) (hA : 0 ≤ A) (hgmax : g ≤ 1/10)
    (z : I → ℝ) (hsq : ∑ i, (z i)^2 = 3*A*g^2) :
    fixedShift A g ≤ ∑ i, -(z i)^2 / (2*((1-2*g)+fixedFrequency)) := by
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hsq]
  have hd : (787/250 : ℝ) ≤ 2*((1-2*g)+fixedFrequency) := by
    unfold fixedFrequency
    linarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 3*A*g^2)
    (by norm_num : (0 : ℝ) < 787/250) hd
  calc
    fixedShift A g = -(3*A*g^2/(787/250)) := by unfold fixedShift; ring
    _ ≤ -(3*A*g^2/(2*((1-2*g)+fixedFrequency))) := neg_le_neg hh
    _ = _ := by ring
end Sums

/-- Mode multiplicity is exactly three per physical rung. -/
theorem torus_mode_card (n m : ℕ) :
    Fintype.card (Mode (Torus.FullVertex (2*n) (2*m))) = 3*((2*n)*(2*m)) := by
  simp [Mode, Torus.FullVertex, Nat.mul_comm, Nat.mul_left_comm]

/-- Sharp actual-H reference form on the whole interval [0,1/10]. -/
theorem fullHamiltonian_number_lower_sharp {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (x : EuclideanSpace ℝ (Torus.FullConfig (2*n) (2*m))) :
    commonFrequency g *
      ⟪(graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x,
        (FiniteProduct.number (Mode (Torus.FullVertex (2*n) (2*m))) (M+1)).toEuclideanLin
          ((graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x)⟫ +
      referenceShift ((2*n)*(2*m)) g * ‖x‖^2 ≤
      ⟪x, (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).toEuclideanLin x⟫ := by
  apply fullHamiltonian_spectral_number_lower hM n m hn hm hAM g hg
  · intro i
    exact mode_stable g _ hgmax (ReferenceAdjacency.graphModeEigenvalue_bound _ _ g hg i)
  · exact commonFrequency_pos g hgmax
  · intro i
    exact commonFrequency_le_mode g _ (ReferenceAdjacency.graphModeEigenvalue_bound _ _ g hg i)
  · exact le_of_eq (referenceShift_eq_sum _ _ _
      (ReferenceAdjacency.torus_graphModeEigenvalue_square_sum n m hn hm g))

/-- The exact fixed rational reference used by the scalar certificates, now
proved for the actual physical Hamiltonian without spectral/form premises. -/
theorem fullHamiltonian_number_lower_fixed {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (x : EuclideanSpace ℝ (Torus.FullConfig (2*n) (2*m))) :
    fixedFrequency *
      ⟪(graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x,
        (FiniteProduct.number (Mode (Torus.FullVertex (2*n) (2*m))) (M+1)).toEuclideanLin
          ((graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x)⟫ +
      fixedShift ((2*n)*(2*m)) g * ‖x‖^2 ≤
      ⟪x, (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).toEuclideanLin x⟫ := by
  apply fullHamiltonian_spectral_number_lower hM n m hn hm hAM g hg
  · intro i
    exact mode_stable g _ hgmax (ReferenceAdjacency.graphModeEigenvalue_bound _ _ g hg i)
  · exact fixedFrequency_pos
  · intro i
    exact fixedFrequency_le_mode g _ hgmax (ReferenceAdjacency.graphModeEigenvalue_bound _ _ g hg i)
  · exact fixedShift_le_sum _ _ (by positivity) hgmax _
      (ReferenceAdjacency.torus_graphModeEigenvalue_square_sum n m hn hm g)

/-- Sharp physical thermal bound with all reference spectral hypotheses discharged. -/
theorem fullHamiltonian_thermal_sharp {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U β : ℝ) (hβ : 0 ≤ β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β - 1 ≤
      Real.exp (β*(U-referenceShift ((2*n)*(2*m)) g)) *
        ((∑ j : Fin (M+1), Real.exp (-β*commonFrequency g*(j.val : ℝ))) ^
          (3*((2*n)*(2*m))) - 1) := by
  have h := FiniteProduct.relativePartition_tail_le_product_number M _
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin
    (graphSpectralEmbedding_injective hM hAM _ _ _)
    (graphSpectralEmbedding_norm hM hAM _ _ _) (commonFrequency g)
    (referenceShift ((2*n)*(2*m)) g) U β (commonFrequency_pos g hgmax).le hβ
    (fullHamiltonian_number_lower_sharp hM n m hn hm hAM g hg hgmax) hU
  simpa only [torus_mode_card] using h

/-- The fixed-certificate thermal bound retains exactly 387/500 and 750/787. -/
theorem fullHamiltonian_thermal_fixed {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U β : ℝ) (hβ : 0 ≤ β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β - 1 ≤
      Real.exp (β*(U+750*((2*n)*(2*m) : ℝ)*g^2/787)) *
        ((∑ j : Fin (M+1), Real.exp (-β*(387/500)*(j.val : ℝ))) ^
          (3*((2*n)*(2*m))) - 1) := by
  have h := FiniteProduct.relativePartition_tail_le_product_number M _
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin
    (graphSpectralEmbedding_injective hM hAM _ _ _)
    (graphSpectralEmbedding_norm hM hAM _ _ _) fixedFrequency
    (fixedShift ((2*n)*(2*m)) g) U β fixedFrequency_pos.le hβ
    (fullHamiltonian_number_lower_fixed hM n m hn hm hAM g hg hgmax) hU
  simpa only [torus_mode_card, fixedFrequency, fixedShift, neg_div, sub_neg_eq_add] using h

/-- Fixed-certificate excitation bound for every nonlowest actual eigenvalue. -/
theorem fullHamiltonian_excitation_fixed {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U : ℝ)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    387/500 - 750*((2*n)*(2*m) : ℝ)*g^2/787 - U ≤
      ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k -
        groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  have h := FiniteProduct.excitationEnergy_lower_of_product_number M _
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin
    (graphSpectralEmbedding_injective hM hAM _ _ _)
    (graphSpectralEmbedding_norm hM hAM _ _ _) fixedFrequency
    (fixedShift ((2*n)*(2*m)) g) U fixedFrequency_pos.le
    (fullHamiltonian_number_lower_fixed hM n m hn hm hAM g hg hgmax) hU k hk
  convert h using 1
  dsimp only [fixedFrequency, fixedShift]
  ring

/-- The unchanged physical all-singlet vector supplies an unconditional ground
upper bound, independently of every dressed-trial improvement. -/
theorem physical_ground_le_zero (n m : ℕ) (g : ℝ) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ 0 :=
  (groundEnergy_le_diagonal _ (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    TripletNumber.vacuum).trans (le_of_eq (PhysicalGram.fullHamiltonian_vacuum n m g))

/-- The canonical coordinate cutoff equals the physical site count and is
large enough on every torus covered by the theorem. -/
theorem area_cutoff (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : 2 ≤ (2*n)*(2*m) := by
  have hprod := Nat.mul_le_mul (show 2 ≤ 2*n by omega) (show 1 ≤ 2*m by omega)
  omega

/-- Absolute nonlowest energy, in the form needed by Temple's inequality.
There is no ground-energy premise and no auxiliary cutoff parameter. -/
theorem fullHamiltonian_nonlowest_energy_fixed
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    387/500 - 750*((2*n)*(2*m) : ℝ)*g^2/787 ≤
      ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k := by
  have h := fullHamiltonian_excitation_fixed (area_cutoff n m hn hm) n m hn hm
    (by simp [Torus.FullVertex]) g hg hgmax
    (groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)) le_rfl k hk
  linarith

/-- A baseline actual physical gap from the vacuum alone. Better dressed-trial
upper bounds can be substituted in the stronger theorem above. -/
theorem fullHamiltonian_gap_fixed_vacuum
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    387/500 - 750*((2*n)*(2*m) : ℝ)*g^2/787 ≤
      ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k -
        groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  have h := fullHamiltonian_nonlowest_energy_fixed n m hn hm g hg hgmax k hk
  have hground := physical_ground_le_zero n m g
  linarith

/-- A strictly positive, entirely unconditional finite-volume baseline on all
covered tori of at most 64 rungs throughout 0 ≤ g ≤ 1/10. -/
theorem fullHamiltonian_gap_area_le_64
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (harea : (2*n)*(2*m) ≤ 64)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    (64569/393500 : ℝ) ≤
      ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k -
        groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  have h := fullHamiltonian_gap_fixed_vacuum n m hn hm g hg hgmax k hk
  have hareaR : ((2*n)*(2*m) : ℝ) ≤ 64 := by exact_mod_cast harea
  have hsq : g^2 ≤ (1/10 : ℝ)^2 := by
    have hp := mul_nonneg hg (sub_nonneg.mpr hgmax)
    nlinarith
  have hprod := mul_le_mul hareaR hsq (sq_nonneg g) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith

/-- A finite geometric estimate only; no infinite occupation space is introduced. -/
theorem finite_exp_sum_le_geometric (M : ℕ) (β a : ℝ) (hβ : 0 < β) (ha : 0 < a) :
    (∑ j : Fin (M+1), Real.exp (-β*a*(j.val : ℝ))) ≤
      (1-Real.exp (-β*a))⁻¹ := by
  have hq : Real.exp (-β*a) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  calc
    _ = ∑ j ∈ Finset.range (M+1), (Real.exp (-β*a))^j := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Real.exp (-β*a*(j : ℝ)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := M+1) (Real.exp_nonneg (-β*a)) hq)

/-- Canonical-cutoff thermal theorem with the standard scalar geometric bound.
The rational constants exactly match the fixed warmup certificates. -/
theorem fullHamiltonian_thermal_fixed_geometric
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U β : ℝ) (hβ : 0 < β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β - 1 ≤
      Real.exp (β*(U+750*((2*n)*(2*m) : ℝ)*g^2/787)) *
        (((1-Real.exp (-β*(387/500)))⁻¹) ^ (3*((2*n)*(2*m))) - 1) := by
  have h := fullHamiltonian_thermal_fixed (area_cutoff n m hn hm) n m hn hm
    (by simp [Torus.FullVertex]) g hg hgmax U β hβ.le hU
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply sub_le_sub_right
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
    (finite_exp_sum_le_geometric _ β (387/500) hβ (by norm_num)) _

end BilayerDressed.PhysicalReferencePointOne
