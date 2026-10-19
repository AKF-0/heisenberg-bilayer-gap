import Dressed.ScalarThermalCertificate
import Mathlib.Tactic

/-! Whole-real-interval scalar bounds for the cubic shifts. Identifying these
polynomials with the actual Hamiltonian residual shift is a separate theorem. -/
noncomputable section
namespace BilayerDressed.ScalarInterval
open ScalarThermal
set_option maxHeartbeats 1000000

def shift16 (g : ℝ) : ℝ := -12*g^2-6*g^3-(15/2)*g^4
def shift32 (g : ℝ) : ℝ := -24*g^2-12*g^3-(45/4)*g^4
def shift64 (g : ℝ) : ℝ := -48*g^2-24*g^3-15*g^4

theorem powers {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    g^2≤1/100 ∧ g^3≤1/1000 ∧ g^4≤1/10000 := by
  have h2 : g^2≤1/100 := by nlinarith
  have h3 : g^3≤1/1000 := by
    have h := mul_le_mul h2 hg hg0 (by norm_num : (0:ℝ)≤1/100)
    nlinarith
  have h4 : g^4≤1/10000 := by nlinarith [sq_nonneg (g^2-1/100)]
  exact ⟨h2,h3,h4⟩

theorem denominator16_lower {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    (den16:ℝ) ≤ (a:ℝ)-750*16*g^2/787-shift16 g-(167/1000000) := by
  obtain ⟨h2,h3,h4⟩ := powers hg0 hg
  have hb : 0 ≤ (16:ℝ)*(750/787-3/4)*(1/10+g)-
      (3*16/8)*(1/100+g/10+g^2)-
      (15/2)*(1/1000+g/100+g^2/10+g^3) := by
    nlinarith
  have hp := mul_nonneg (show 0≤1/10-g by linarith) hb
  norm_num [den16,a,shift16]
  nlinarith [hp]

theorem denominator32_lower {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    (den32:ℝ) ≤ (a:ℝ)-750*32*g^2/787-shift32 g-(346/1000000) := by
  obtain ⟨h2,h3,h4⟩ := powers hg0 hg
  have hb : 0 ≤ (32:ℝ)*(750/787-3/4)*(1/10+g)-
      (3*32/8)*(1/100+g/10+g^2)-
      (45/4)*(1/1000+g/100+g^2/10+g^3) := by
    nlinarith
  have hp := mul_nonneg (show 0≤1/10-g by linarith) hb
  norm_num [den32,a,shift32]
  nlinarith [hp]

theorem denominator64_lower {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    (den64:ℝ) ≤ (a:ℝ)-750*64*g^2/787-shift64 g-(800/1000000) := by
  obtain ⟨h2,h3,h4⟩ := powers hg0 hg
  have hb : 0 ≤ (64:ℝ)*(750/787-3/4)*(1/10+g)-
      (3*64/8)*(1/100+g/10+g^2)-
      (15)*(1/1000+g/100+g^2/10+g^3) := by
    nlinarith
  have hp := mul_nonneg (show 0≤1/10-g by linarith) hb
  norm_num [den64,a,shift64]
  nlinarith [hp]

theorem shift_dx {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    shift32 g-2*shift16 g ≤ 3/8000 := by
  have h4 := (powers hg0 hg).2.2
  dsimp [shift32,shift16]
  nlinarith

theorem shift_dy {g : ℝ} (hg0 : 0≤g) (hg : g≤1/10) :
    shift64 g-2*shift32 g ≤ 3/4000 := by
  have h4 := (powers hg0 hg).2.2
  dsimp [shift64,shift32]
  nlinarith

end BilayerDressed.ScalarInterval
