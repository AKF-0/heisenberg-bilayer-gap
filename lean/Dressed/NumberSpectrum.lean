import Dressed.NumberThermalTail
import Gap.TorusLifts
import Gap.RealRungOperators

/-!
# Exact spectrum of the physical total triplet number

The operator here is the sum of the actual tensor-identity lifts of the
physical rung projector `RealRungOperators.h`. Its diagonal form, unique
zero configuration, and exact thermal product are proved from those entries.
No energy list or physical spectral hypothesis is supplied as an assumption.
-/
noncomputable section
namespace BilayerDressed.TripletNumber
open Matrix BilayerGap
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 800000

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Config (V : Type*) := V → Fin 4
abbrev Op (V : Type*) := Matrix (Config V) (Config V) ℝ

/-- The singlet has number zero; each of the three triplets has number one. -/
def localEnergy (i : Fin 4) : ℝ := if i = 0 then 0 else 1

/-- The exact triplet count of a tensor-basis configuration. -/
def energy (s : Config V) : ℝ := ∑ v, localEnergy (s v)

/-- The all-singlet tensor-basis configuration. -/
def vacuum : Config V := fun _ => 0

/-- Sum of the concrete physical single-rung triplet projectors. -/
def number : Op V := ∑ v, Torus.siteLift RealRungOperators.h v

/-- The local matrix in the physical model is precisely `diag(0,1,1,1)`. -/
theorem rung_h_eq_diagonal : RealRungOperators.h = Matrix.diagonal localEnergy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [RealRungOperators.h, LocalRung.rungDiagonal, localEnergy,
      Matrix.diagonal_apply]

/-- A diagonal one-site observable stays diagonal under the genuine lift. -/
theorem siteLift_diagonal (d : Fin 4 → ℝ) (v : V) :
    Torus.siteLift (Matrix.diagonal d) v =
      Matrix.diagonal (fun s : Config V => d (s v)) := by
  classical
  ext s t
  by_cases hst : s = t
  · subst t
    simp [Torus.siteLift]
  · have h : ¬ ((∀ w, w ≠ v → s w = t w) ∧ s v = t v) := by
      intro hh
      apply hst
      funext w
      by_cases hw : w = v
      · simpa [hw] using hh.2
      · exact hh.1 w hw
    simp only [Torus.siteLift, Matrix.diagonal_apply, hst, if_false]
    split_ifs with hout hv <;> simp_all

/-- Exact diagonalization of the actual total number operator. -/
theorem number_eq_diagonal : (number : Op V) = Matrix.diagonal energy := by
  classical
  unfold number
  rw [rung_h_eq_diagonal]
  simp_rw [siteLift_diagonal]
  ext s t
  by_cases hst : s = t
  · subst t
    simp [energy, Matrix.sum_apply]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply, hst]

@[simp] theorem number_diagonal (s : Config V) : number s s = energy s := by
  rw [number_eq_diagonal, Matrix.diagonal_apply_eq]

theorem number_hermitian : (number : Op V).IsHermitian := by
  rw [number_eq_diagonal]
  exact Matrix.isHermitian_diagonal _

theorem localEnergy_nonneg (i : Fin 4) : 0 ≤ localEnergy i := by
  unfold localEnergy
  split_ifs <;> norm_num

theorem energy_nonneg (s : Config V) : 0 ≤ energy s :=
  Finset.sum_nonneg (fun v _ => localEnergy_nonneg (s v))

@[simp] theorem energy_vacuum : energy (vacuum : Config V) = 0 := by
  simp [energy, vacuum, localEnergy]

/-- Every non-vacuum basis configuration contains at least one triplet. -/
theorem one_le_energy_of_ne_vacuum (s : Config V) (hs : s ≠ vacuum) :
    1 ≤ energy s := by
  classical
  have hex : ∃ v, s v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs
    funext v
    exact h v
  obtain ⟨v,hv⟩ := hex
  calc
    1 = localEnergy (s v) := by simp [localEnergy,hv]
    _ ≤ energy s := Finset.single_le_sum
      (fun w _ => localEnergy_nonneg (s w)) (Finset.mem_univ v)

/-- The actual number matrix has exactly one zero diagonal configuration. -/
theorem energy_eq_zero_iff (s : Config V) : energy s = 0 ↔ s = vacuum := by
  constructor
  · intro h
    by_contra hs
    have he := one_le_energy_of_ne_vacuum s hs
    linarith
  · rintro rfl
    exact energy_vacuum

theorem energy_le_card (s : Config V) : energy s ≤ Fintype.card V := by
  calc
    energy s ≤ ∑ _v : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      unfold localEnergy
      split_ifs <;> norm_num
    _ = Fintype.card V := by simp

/-- The finite physical Hilbert-space dimension is four to the site count. -/
theorem card_config : Fintype.card (Config V) = 4 ^ Fintype.card V := by
  simp [Config]

/-- The real Hilbert-space dimension is the physical configuration count. -/
theorem finrank_hilbert : Module.finrank ℝ (EuclideanSpace ℝ (Config V)) =
    4 ^ Fintype.card V := by
  rw [finrank_euclideanSpace, card_config]

/-- The exact local partition factor, with all three triplet states counted. -/
theorem local_partition (t : ℝ) :
    (∑ i : Fin 4, Real.exp (t * localEnergy i)) = 1 + 3 * Real.exp t := by
  simp [Fin.sum_univ_succ, localEnergy]

/-- Exact configuration-space partition function of the actual number matrix. -/
theorem configuration_partition (t : ℝ) :
    (∑ s : Config V, Real.exp (t * energy s)) =
      (1 + 3 * Real.exp t) ^ Fintype.card V := by
  classical
  simp_rw [energy, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (_ : V) (i : Fin 4) => Real.exp (t * localEnergy i))]
  simp_rw [local_partition]
  simp

/-- The actual sorted spectral sum equals the physical configuration sum. -/
theorem sum_ascendingEigenvalue (f : ℝ → ℝ) :
    (∑ k, f (ascendingEigenvalue (number_hermitian (V := V)) k)) =
      ∑ s : Config V, f (energy s) := by
  have h := BilayerDressed.sum_ascendingEigenvalue_diagonal
    (energy (V := V)) (Matrix.isHermitian_diagonal _) f
  simpa only [← number_eq_diagonal] using h

/-- The actual lowest number eigenvalue is zero. -/
theorem groundEnergy_eq_zero : groundEnergy (number_hermitian (V := V)) = 0 := by
  have h := BilayerDressed.groundEnergy_diagonal_eq_zero
    (energy (V := V)) (Matrix.isHermitian_diagonal _) energy_nonneg
    vacuum energy_vacuum
  simpa only [← number_eq_diagonal] using h

/-- Every actual nonlowest number eigenvalue is at least one; its zero
eigenvalue is simple by the unique physical vacuum configuration. -/
theorem one_le_ascendingEigenvalue (k : Fin (Fintype.card (Config V))) (hk : k ≠ 0) :
    1 ≤ ascendingEigenvalue (number_hermitian (V := V)) k := by
  have h := BilayerDressed.ascendingEigenvalue_diagonal_ge_one
    (energy (V := V)) (Matrix.isHermitian_diagonal _) vacuum energy_vacuum
    one_le_energy_of_ne_vacuum k hk
  simpa only [← number_eq_diagonal] using h

/-- The physical number operator's actual eigenvalues have the exact product
partition function, including multiplicity and at every real temperature. -/
theorem spectral_partition (β a : ℝ) :
    (∑ k, Real.exp (-β * a * ascendingEigenvalue (number_hermitian (V := V)) k)) =
      (1 + 3 * Real.exp (-β * a)) ^ Fintype.card V := by
  rw [sum_ascendingEigenvalue (fun t => Real.exp (-β * a * t))]
  exact configuration_partition (-β * a)

/-- Finite thermal comparison against the concrete physical number operator.
The only remaining physical inputs are the actual Hamiltonian's affine form
bound and its vacuum expectation; no number-spectrum premise remains. -/
theorem relativePartition_tail_le_of_vacuum
    (H : Op V) (hH : H.IsHermitian) (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ (Config V),
      a * ⟪x, (number : Op V).toEuclideanLin x⟫ - c * ‖x‖^2 ≤
        ⟪x, H.toEuclideanLin x⟫)
    (β : ℝ) (hβ : 0 ≤ β) (hvacuum : H vacuum vacuum ≤ 0) :
    relativePartition hH β - 1 ≤ Real.exp (β * c) *
      ((1 + 3 * Real.exp (-β * a)) ^ Fintype.card V - 1) :=
  BilayerDressed.relativePartition_tail_le_triplet_product_of_vacuum
    number H number_hermitian hH a c ha hNH β hβ vacuum hvacuum
    groundEnergy_eq_zero (Fintype.card V) (spectral_partition β a)

/-- Every nonlowest actual Hamiltonian eigenvalue obeys the finite excitation
bound once the affine physical-number comparison and vacuum energy hold.
A positive gap follows only when `a - c` is positive; no uniform claim is made. -/
theorem excitationEnergy_lower_of_vacuum
    (H : Op V) (hH : H.IsHermitian) (a c : ℝ) (ha : 0 ≤ a)
    (hNH : ∀ x : EuclideanSpace ℝ (Config V),
      a * ⟪x, (number : Op V).toEuclideanLin x⟫ - c * ‖x‖^2 ≤
        ⟪x, H.toEuclideanLin x⟫)
    (hvacuum : H vacuum vacuum ≤ 0)
    (k : Fin (Fintype.card (Config V))) (hk : k ≠ 0) :
    a - c ≤ ascendingEigenvalue hH k - groundEnergy hH :=
  BilayerDressed.excitationEnergy_lower_of_number_ge_one
    number H number_hermitian hH a c ha hNH
    (BilayerDressed.groundEnergy_nonpos_of_diagonal H hH vacuum hvacuum)
    k (one_le_ascendingEigenvalue k hk)

#print axioms number_eq_diagonal
#print axioms energy_eq_zero_iff
#print axioms configuration_partition
#print axioms groundEnergy_eq_zero
#print axioms spectral_partition
#print axioms one_le_ascendingEigenvalue
#print axioms relativePartition_tail_le_of_vacuum
#print axioms excitationEnergy_lower_of_vacuum

end BilayerDressed.TripletNumber
