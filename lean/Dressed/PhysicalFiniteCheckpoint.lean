import Dressed.PhysicalGramLowerBound

/-! Explicit finite-volume spectral thresholds for the actual bilayer matrices.
These are inputs to a subsequent trial/Temple certificate. The area dependence
is retained; this file alone asserts no uniform infinite-volume gap. -/
noncomputable section
namespace BilayerDressed.PhysicalGram
open BilayerGap

/-- Absolute nonlowest eigenvalue threshold, distinct from a ground-subtracted gap. -/
theorem fullHamiltonian_absolute_excitation_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : ℝ) (hg : 0≤g) (hgmax : g≤2/5)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k≠0) :
    (4/5-2*g)-15*((2*n)*(2*m) : ℝ)*g^2 ≤
      ascendingEigenvalue (fullHamiltonian_hermitian (2*n) (2*m) g) k := by
  have ha : 0≤4/5-2*g := by linarith
  have hh := hermitian_ascendingEigenvalue_affine_lower TripletNumber.number
    (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g)
    TripletNumber.number_hermitian (fullHamiltonian_hermitian (2*n) (2*m) g)
    (4/5-2*g) (15*((2*n)*(2*m) : ℝ)*g^2) ha
    (fullHamiltonian_inner_lower_bound n m hn hm g hg) k
  have hN := TripletNumber.one_le_ascendingEigenvalue k hk
  have hmul := mul_le_mul_of_nonneg_left hN ha
  linarith

/-- A rational endpoint bound, with the physical rung area explicit. -/
theorem finite_gram_threshold (A : ℕ) (g : ℝ) (hg : 0≤g) (hgmax : g≤3/200) :
    77/100-(27/8000 : ℝ)*A ≤ (4/5-2*g)-15*A*g^2 := by
  have hs : g^2≤(3/200 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0≤(15 : ℝ)*A)
  nlinarith

/-- Every nonlowest eigenvalue on the physical 4×4 rung torus is at least 0.716. -/
theorem four_by_four_absolute_threshold (g : ℝ) (hg : 0≤g) (hgmax : g≤3/200)
    (k : Fin (Fintype.card (Torus.FullConfig 4 4))) (hk : k≠0) :
    (179/250 : ℝ)≤ascendingEigenvalue (fullHamiltonian_hermitian 4 4 g) k := by
  have hh := fullHamiltonian_absolute_excitation_lower 2 2 (by norm_num) (by norm_num)
    g hg (by linarith) k hk
  have hc := finite_gram_threshold 16 g hg hgmax
  norm_num at hh hc ⊢
  linarith

/-- The actual finite 8×8 rung spectrum has gap at least 0.554 in the smaller interval. -/
theorem eight_by_eight_finite_gap (g : ℝ) (hg : 0≤g) (hgmax : g≤3/200)
    (k : Fin (Fintype.card (Torus.FullConfig 8 8))) (hk : k≠0) :
    (277/500 : ℝ) ≤ ascendingEigenvalue (fullHamiltonian_hermitian 8 8 g) k -
      groundEnergy (fullHamiltonian_hermitian 8 8 g) := by
  have hh := fullHamiltonian_excitation_lower 4 4 (by norm_num) (by norm_num)
    g hg (by linarith) k hk
  have hc := finite_gram_threshold 64 g hg hgmax
  norm_num at hh hc ⊢
  linarith

end BilayerDressed.PhysicalGram
