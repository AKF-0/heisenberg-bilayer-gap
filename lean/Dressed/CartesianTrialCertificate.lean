import Dressed.DressedTrialBounds
import Dressed.ResidualVacuumOrthogonality
import Dressed.MatrixTrialCertificate
import Dressed.PhysicalFiniteCheckpoint
import Dressed.HermitianInterlacing

/-! Actual Cartesian trial energy certificates and exact transfer back to the
real magic-rung Hamiltonian. The global orthogonal parity map is used, not the
unrelated two-site sign adapter. This file is the finite g ≤ 3/200 backup route. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed
open BilayerGap
namespace CartesianBasis

 theorem fullHamiltonian_inverse_conjugation (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    U * Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g * U =
      fullHamiltonian n m g := by
  rw [←fullHamiltonian_conjugation n m hn hm]
  simp only [←Matrix.mul_assoc,U_mul_U,Matrix.one_mul]
  rw [Matrix.mul_assoc,U_mul_U,Matrix.mul_one]

 theorem fullHamiltonian_hermitian (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    (fullHamiltonian n m g).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul
    (U : Op (Torus.Vertex n m)) (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,U_transpose,
    fullHamiltonian_inverse_conjugation n m hn hm] using h

/-- Exact actual ordered spectra agree, including multiplicities. -/
 theorem fullHamiltonian_ascending_eq (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) :
    ascendingEigenvalue (fullHamiltonian_hermitian n m hn hm g) k =
      ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k := by
  have h := hermitian_eigenvalues₀_eq_of_charpoly_eq
    (fullHamiltonian_hermitian n m hn hm g)
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (fullHamiltonian_charpoly n m hn hm g).symm
  exact congrFun h k.rev

 theorem fullHamiltonian_ground_eq (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (g : ℝ) :
    groundEnergy (fullHamiltonian_hermitian n m hn hm g)=
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) :=
  fullHamiltonian_ascending_eq n m hn hm g 0

end CartesianBasis

namespace FiniteTrial

def reference (A : ℕ) (g : ℝ) : ℝ := -(3/4 : ℝ)*A*g^2-(3/8 : ℝ)*A*g^3

def eta (A : ℕ) (g : ℝ) : ℝ := (5/3 : ℝ)*g*Real.sqrt (A : ℝ)

def epsilon (A : ℕ) (g : ℝ) : ℝ :=
  (5/2 : ℝ)*((24*Real.sqrt (A : ℝ)+9*A)*g^3+4*A*g^5)

open SeedGraphs

/-- The concrete physical upper bound uses the actual dressed trial. No residual
or spectrum comparison is supplied by a caller. -/
 theorem physical_energy_upper (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (h : Conditions n m) (hi : IncidenceIdentity n m) (hcard : Fintype.card (Torus.Vertex n m)≤64)
    (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤
      reference (Fintype.card (Torus.Vertex n m)) g+
      eta (Fintype.card (Torus.Vertex n m)) g*epsilon (Fintype.card (Torus.Vertex n m)) g := by
  have hx : ∀ u,Torus.xNext n m u≠u := fun u => Torus.xNext_ne n m hn u
  have hy : ∀ u,Torus.yNext n m u≠u := fun u => Torus.yNext_ne n m hm u
  have hh := dressed_trial_energy_upper (CartesianBasis.fullHamiltonian n m g)
    (CartesianBasis.fullHamiltonian_hermitian n m hn hm g)
    (dressedVector ((graph n m h).kernel g)) vacuumVector
    (one_le_norm_dressedVector _) _
    (eta (Fintype.card (Torus.Vertex n m)) g)
    (epsilon (Fintype.card (Torus.Vertex n m)) g)
    (graph_dressed_residual_vacuum_orthogonal n m h hi g hx hy)
    ((graph n m h).dressedVector_distance_small g hg hmax hcard)
    (graph_dressed_residual_norm_small n m h hi g hg hmax hcard hx hy)
  rw [CartesianBasis.fullHamiltonian_ground_eq n m hn hm,
    (graph n m h).residualShift_eq g _ _ (graph_x_edge n m h) (graph_y_edge n m h)] at hh
  exact hh

/-- The lower bound has only the explicit actual nonlowest threshold as a
remaining caller premise; the concrete small-box instance discharges it. -/
 theorem physical_energy_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (h : Conditions n m) (hi : IncidenceIdentity n m) (hcard : Fintype.card (Torus.Vertex n m)≤64)
    (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) (threshold : ℝ)
    (hnext : ∀ k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m))), k≠0 →
      threshold≤ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k)
    (hden : (1/2 : ℝ)≤threshold-(reference (Fintype.card (Torus.Vertex n m)) g+
      eta (Fintype.card (Torus.Vertex n m)) g*epsilon (Fintype.card (Torus.Vertex n m)) g)) :
    reference (Fintype.card (Torus.Vertex n m)) g-
      eta (Fintype.card (Torus.Vertex n m)) g*epsilon (Fintype.card (Torus.Vertex n m)) g-
      2*(epsilon (Fintype.card (Torus.Vertex n m)) g)^2 ≤
        groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  have hx : ∀ u,Torus.xNext n m u≠u := fun u => Torus.xNext_ne n m hn u
  have hy : ∀ u,Torus.yNext n m u≠u := fun u => Torus.yNext_ne n m hm u
  have hs := (graph n m h).residualShift_eq g _ _ (graph_x_edge n m h) (graph_y_edge n m h)
  have hh := dressed_trial_energy_lower (CartesianBasis.fullHamiltonian n m g)
    (CartesianBasis.fullHamiltonian_hermitian n m hn hm g)
    (dressedVector ((graph n m h).kernel g)) vacuumVector
    (one_le_norm_dressedVector _) _
    (eta (Fintype.card (Torus.Vertex n m)) g)
    (epsilon (Fintype.card (Torus.Vertex n m)) g) threshold
    (graph_dressed_residual_vacuum_orthogonal n m h hi g hx hy)
    ((graph n m h).dressedVector_distance_small g hg hmax hcard)
    (graph_dressed_residual_norm_small n m h hi g hg hmax hcard hx hy)
    (fun k hk => by rw [CartesianBasis.fullHamiltonian_ascending_eq n m hn hm]; exact hnext k hk)
    (by rw [hs]; exact hden)
  rw [CartesianBasis.fullHamiltonian_ground_eq n m hn hm,hs] at hh
  exact hh

end FiniteTrial
end BilayerDressed
