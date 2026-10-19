import Dressed.CartesianTrialCertificate

/-! A concrete actual-Hamiltonian energy-defect certificate for the finite
backup interval 0 ≤ g ≤ 3/200. All physical residual and Temple hypotheses
are discharged. This is a seed energy bound, not yet an all-size gap theorem. -/
noncomputable section
namespace BilayerDressed.FiniteTrial
open BilayerGap SeedGraphs

 theorem reference_nonpos (A : ℕ) (g : ℝ) (hg : 0≤g) : reference A g≤0 := by
  unfold reference
  have h₂ : 0≤(3/4 : ℝ)*A*g^2 := by positivity
  have h₃ : 0≤(3/8 : ℝ)*A*g^3 := by positivity
  nlinarith

 theorem eta_nonneg (A : ℕ) (g : ℝ) (hg : 0≤g) : 0≤eta A g := by
  unfold eta
  positivity

 theorem epsilon_nonneg (A : ℕ) (g : ℝ) (hg : 0≤g) : 0≤epsilon A g := by
  unfold epsilon
  positivity

 theorem eta_mono (A : ℕ) (g t : ℝ) (hgt : g≤t) : eta A g≤eta A t := by
  unfold eta
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgt (by norm_num))
    (Real.sqrt_nonneg _)

 theorem epsilon_mono (A : ℕ) (g t : ℝ) (hg : 0≤g) (hgt : g≤t) :
    epsilon A g≤epsilon A t := by
  have h₃ := pow_le_pow_left₀ hg hgt 3
  have h₅ := pow_le_pow_left₀ hg hgt 5
  unfold epsilon
  exact mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left h₃ (by positivity))
    (mul_le_mul_of_nonneg_left h₅ (by positivity))) (by norm_num)

 theorem eta16_bound (g : ℝ) (hmax : g≤3/200) : eta 16 g≤1/10 := by
  have h := eta_mono 16 g (3/200) hmax
  norm_num [eta] at h ⊢
  exact h

 theorem eta64_bound (g : ℝ) (hmax : g≤3/200) : eta 64 g≤1/5 := by
  have h := eta_mono 64 g (3/200) hmax
  norm_num [eta] at h ⊢
  exact h

 theorem epsilon16_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) : epsilon 16 g≤21/10000 := by
  have h := epsilon_mono 16 g (3/200) hg hmax
  norm_num [epsilon] at h ⊢
  linarith

 theorem epsilon64_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) : epsilon 64 g≤13/2000 := by
  have h := epsilon_mono 64 g (3/200) hg hmax
  norm_num [epsilon] at h ⊢
  linarith

 theorem four_by_four_temple_denominator (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    (1/2 : ℝ)≤179/250-(reference 16 g+eta 16 g*epsilon 16 g) := by
  have hr := reference_nonpos 16 g hg
  have hm := mul_le_mul (eta16_bound g hmax) (epsilon16_bound g hg hmax)
    (epsilon_nonneg 16 g hg) (by norm_num : (0 : ℝ)≤1/10)
  linarith

/-- The actual physical 4×4 ground energy has the derived Temple lower bound. -/
 theorem four_by_four_energy_lower (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    reference 16 g-eta 16 g*epsilon 16 g-2*(epsilon 16 g)^2 ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) := by
  have h := physical_energy_lower 2 2 (by norm_num) (by norm_num)
    four_by_four_conditions four_by_four_incidence (by norm_num [Torus.Vertex])
    g hg hmax (179/250)
    (PhysicalGram.four_by_four_absolute_threshold g hg hmax)
    (by simpa [Torus.Vertex] using four_by_four_temple_denominator g hg hmax)
  simpa [Torus.Vertex] using h

/-- The actual physical 8×8 ground energy has the derived variational upper bound. -/
 theorem eight_by_eight_energy_upper (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g) ≤
      reference 64 g+eta 64 g*epsilon 64 g := by
  have h := physical_energy_upper 4 4 (by norm_num) (by norm_num)
    eight_by_eight_conditions eight_by_eight_incidence (by norm_num [Torus.Vertex])
    g hg hmax
  simpa [Torus.Vertex] using h

/-- Exact extensive reference cancellation makes the physical sewing defect small. -/
 theorem physical_energy_defect_le (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g)-
      4*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤
      (27191/12500000 : ℝ) := by
  have hu := eight_by_eight_energy_upper g hg hmax
  have hl := four_by_four_energy_lower g hg hmax
  have hm64 := mul_le_mul (eta64_bound g hmax) (epsilon64_bound g hg hmax)
    (epsilon_nonneg 64 g hg) (by norm_num : (0 : ℝ)≤1/5)
  have hm16 := mul_le_mul (eta16_bound g hmax) (epsilon16_bound g hg hmax)
    (epsilon_nonneg 16 g hg) (by norm_num : (0 : ℝ)≤1/10)
  have hs := pow_le_pow_left₀ (epsilon_nonneg 16 g hg) (epsilon16_bound g hg hmax) 2
  have hc : reference 64 g=4*reference 16 g := by unfold reference; ring
  rw [hc] at hu
  nlinarith

/-- The final finite seed energy condition is proved for the actual Hamiltonian,
not supplied as a certificate premise. -/
 theorem physical_energy_defect_lt_one_four_hundredth (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g)-
      4*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) < (1/400 : ℝ) :=
  (physical_energy_defect_le g hg hmax).trans_lt (by norm_num)

end BilayerDressed.FiniteTrial
