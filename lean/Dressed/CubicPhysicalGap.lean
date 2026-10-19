import Dressed.QuarticIntegerActualNorm16
import Dressed.QuarticIntegerActualNorm32
import Dressed.QuarticIntegerActualMean16
import Dressed.QuarticIntegerActualMean32
import Dressed.QuarticIntegerActualMean64
import Dressed.CubicQuarticNumericMeanBridge
import Dressed.CubicQuarticSeedReduction
import Dressed.PhysicalStandardCriterion

/-! Actual finite periodic-square bilayer gap from complete cubic certificates.
All five actual quartic endpoint inputs are proved by the imported finite
Hamiltonian certificates. The final statement has no seed, residual, numerical-
table, transfer, spectral-comparison, or ground-simplicity premise.

The conclusion is for finite even periodic squares L >= 256 and real couplings
0 <= g <= 1/10. It is not a claim about infinite-volume GNS uniqueness. -/
noncomputable section
namespace BilayerDressed.CubicPhysicalGap
open BilayerGap

/-- The five actual quartic quantities, from complete finite kernel certificates. -/
theorem quartic_inputs (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    CubicQuarticSeed.Inputs g := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact CubicQuarticNumericMean.mean16_of_coefficient
      (QuarticRowMajor.enumeration 2 2) g hg hmax
      (QuarticIntegerActual.mean16 g hg hmax)
  · exact CubicQuarticNumericMean.mean32_of_coefficient
      (QuarticRowMajor.enumeration 4 2) g hg hmax
      (QuarticIntegerActual.mean32 g hg hmax)
  · exact CubicQuarticNumericMean.mean64_of_coefficient
      (QuarticRowMajor.enumeration 4 4) g hg hmax
      (QuarticIntegerActual.mean64 g hg hmax)
  · exact QuarticIntegerActual.vacuum16 g hg hmax
  · exact QuarticIntegerActual.vacuum32 g hg hmax

/-- Actual cubic-state residual bounds on all three seed boxes. -/
theorem trial_bounds (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    CubicTrialSeed.Bounds g :=
  CubicQuarticSeed.trial_bounds hg hmax (quartic_inputs g hg hmax)

/-- Actual spatial and thermal seed ratios, before the six ordered warmups. -/
theorem coordinate_bounds (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition ⟨4,4,16⟩
      ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0 :=
  CubicTrialSeed.coordinate_bounds hg hmax (trial_bounds g hg hmax)

/-- The size-independent lower separation is strictly positive. -/
theorem gap_constant_positive : 0 < Real.log (200/13)/1024 :=
  PhysicalWarmup.gapLowerBound_pos

/-- Every energy level of the actual standard Pauli spin-half bilayer, with
multiplicity, has a unique lowest level and the stated strict uniform separation.
The only hypotheses are the coupling interval and even square side length. -/
theorem standard_spin_uniform_gap (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (L : ℕ) (hEven : Even L) (hlarge : 256 ≤ L) :
    ∃ P Q : Matrix (Fin ((BilayerModel.family g).dim L L : ℕ))
        (Fin ((BilayerModel.family g).dim L L : ℕ)) ℂ,
    ∃ i₀ : Fin ((BilayerModel.family g).dim L L : ℕ),
      P*Q=1 ∧ Q*P=1 ∧ PhysicalGap.physicalMatrix L L g*P=
        P*Matrix.diagonal (fun i => (((BilayerModel.family g).hermitian L L).eigenvalues i : ℂ)) ∧
      (∀ i, ((BilayerModel.family g).hermitian L L).eigenvalues i₀ ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues i) ∧
      (∀ i, ((∀ j, ((BilayerModel.family g).hermitian L L).eigenvalues i ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues j)) → i=i₀) ∧
      ∀ i, i≠i₀ → Real.log (200/13)/1024 <
        ((BilayerModel.family g).hermitian L L).eigenvalues i-
          ((BilayerModel.family g).hermitian L L).eigenvalues i₀ := by
  have hL : ValidSize L := ⟨by omega, hEven⟩
  exact PhysicalStandard.standard_spin_gap_of_seed hg
    (coordinate_bounds g hg hmax) L hL hlarge

end BilayerDressed.CubicPhysicalGap
