import Dressed.MeanTrialCertificate
import Dressed.CartesianTrialCertificate
import Dressed.PhysicalReferencePointOne

/-! Generic actual Cartesian dressed-trial energy certificate for the larger
coupling interval. The actual residual mean/norm bounds remain explicit until
the faithful cubic coefficient and Wick certificates are connected. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicTrialEnergy
open BilayerGap

/-- Actual Cartesian variational upper bound transferred to the magic-rung H. -/
theorem physical_upper
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ)
    (K : Torus.Vertex n m → Torus.Vertex n m → ℝ) (e mean : ℝ)
    (hmean : |⟪dressedVector K,(CartesianBasis.fullHamiltonian n m g).toEuclideanLin
      (dressedVector K)-e • dressedVector K⟫| ≤ mean) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ e+mean := by
  have hh := mean_trial_energy_upper (CartesianBasis.fullHamiltonian n m g)
    (CartesianBasis.fullHamiltonian_hermitian n m hn hm g) (dressedVector K)
    (one_le_norm_dressedVector K) e mean hmean
  rwa [CartesianBasis.fullHamiltonian_ground_eq n m hn hm] at hh

/-- Actual Temple lower bound, with its absolute nonlowest threshold fully
proved from the finite reference through g=1/10. -/
theorem physical_lower
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (K : Torus.Vertex n m → Torus.Vertex n m → ℝ) (e mean ε d : ℝ)
    (hmean : |⟪dressedVector K,(CartesianBasis.fullHamiltonian n m g).toEuclideanLin
      (dressedVector K)-e • dressedVector K⟫| ≤ mean)
    (heps : ‖(CartesianBasis.fullHamiltonian n m g).toEuclideanLin
      (dressedVector K)-e • dressedVector K‖ ≤ ε)
    (hd : 0 < d)
    (hden : d ≤ 387/500-750*((2*n)*(2*m):ℝ)*g^2/787-(e+mean)) :
    e-mean-ε^2/d ≤ groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hh := mean_trial_energy_lower (CartesianBasis.fullHamiltonian n m g)
    (CartesianBasis.fullHamiltonian_hermitian n m hn0 hm0 g) (dressedVector K)
    (one_le_norm_dressedVector K) e mean ε
    (387/500-750*((2*n)*(2*m):ℝ)*g^2/787) d hmean heps
    (fun k hk => by
      rw [CartesianBasis.fullHamiltonian_ascending_eq n m hn0 hm0]
      exact PhysicalReferencePointOne.fullHamiltonian_nonlowest_energy_fixed n m hn hm g hg hgmax k hk)
    hd hden
  rwa [CartesianBasis.fullHamiltonian_ground_eq n m hn0 hm0] at hh

end BilayerDressed.CubicTrialEnergy
