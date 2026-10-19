import Gap.SpatialInterpolation
import Gap.MomentPurity
import Gap.Thermal
import Gap.Staircase

/-!
# An actual finite Gibbs family with spatial moment data

The finite energies determine the partition function. Its purity upper and
squaring bounds are derived here, using the finite Gibbs distribution in time
and the supplied countable spectral moment representations in space.
No spectral-gap or purity-recurrence premise is included in the family.
-/

noncomputable section
namespace BilayerGap

/-- Eigenvector-resolved finite energies, with a positive dimension at each size. -/
structure SpectralFamily where
  dim : ℕ → ℕ → ℕ+
  energy : ∀ L M, Fin (dim L M : ℕ) → ℝ

/-- The physical finite Gibbs partition function. -/
def SpectralFamily.partition (F : SpectralFamily) (v : Volume) : ℝ :=
  gibbsZ (F.energy v.x v.y) v.beta

/-- The even spatial domain and positive inverse temperatures. -/
def ValidVolume (v : Volume) : Prop :=
  ValidSize v.x ∧ ValidSize v.y ∧ 0 < v.beta

theorem ValidVolume.double {v : Volume} (hv : ValidVolume v) (i : Axis) :
    ValidVolume (doubleCoord i v) := by
  rcases hv with ⟨hx, hy, hb⟩
  cases i with
  | x => exact ⟨hx.double, hy, hb⟩
  | y => exact ⟨hx, hy.double, hb⟩
  | time => exact ⟨hx, hy, by change 0 < 2 * v.beta; positivity⟩

theorem SpectralFamily.partition_pos (F : SpectralFamily) (v : Volume) :
    0 < F.partition v := gibbsZ_pos _ _

/-- The time ratio is identified with its complete Gibbs eigenvector purity. -/
theorem SpectralFamily.time_ratio (F : SpectralFamily) (v : Volume) :
    partitionRatio F.partition .time v =
      finitePurity (gibbsWeight (F.energy v.x v.y) v.beta) := by
  exact (gibbs_purity_partition_ratio _ _).symm

/-- Derive the x-ratio's probability bounds from its supplied moment spectrum. -/
theorem SpectralFamily.x_ratio_bounds (F : SpectralFamily) {b : ℝ}
    (D : SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩))
    {n m : ℕ} (hn : ValidSize n) (hm : ValidSize m) :
    0 < partitionRatio F.partition .x ⟨n, m, b⟩ ∧
      partitionRatio F.partition .x ⟨n, m, b⟩ ≤ 1 := by
  have hs := (absMoment_upper (by norm_num : 0 < 4) hn.1 (D.x_summable m hm)).1
  have hp : 0 < absMoment (D.xSpectrum m) n := by
    rw [← D.x_moment n m hn hm]
    exact F.partition_pos _
  have h := moment_ratio_bounds (D.xSpectrum m) n hs hp
  change 0 < F.partition ⟨2*n, m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2 ∧
    F.partition ⟨2*n, m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2 ≤ 1
  rw [D.x_moment (2*n) m hn.double hm, D.x_moment n m hn hm]
  exact h

theorem SpectralFamily.y_ratio_bounds (F : SpectralFamily) {b : ℝ}
    (D : SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩))
    {n m : ℕ} (hn : ValidSize n) (hm : ValidSize m) :
    0 < partitionRatio F.partition .y ⟨n, m, b⟩ ∧
      partitionRatio F.partition .y ⟨n, m, b⟩ ≤ 1 := by
  have hs := (absMoment_upper (by norm_num : 0 < 4) hm.1 (D.y_summable n hn)).1
  have hp : 0 < absMoment (D.ySpectrum n) m := by
    rw [← D.y_moment n m hn hm]
    exact F.partition_pos _
  have h := moment_ratio_bounds (D.ySpectrum n) m hs hp
  change 0 < F.partition ⟨n, 2*m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2 ∧
    F.partition ⟨n, 2*m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2 ≤ 1
  rw [D.y_moment n (2*m) hn hm.double, D.y_moment n m hn hm]
  exact h

/-- Own-direction squaring in x follows from the countable moment purity theorem. -/
theorem SpectralFamily.x_ratio_squaring (F : SpectralFamily) {b : ℝ}
    (D : SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩))
    {n m : ℕ} (hn : ValidSize n) (hm : ValidSize m) :
    1 - partitionRatio F.partition .x (doubleCoord .x ⟨n, m, b⟩) ≤
      purityStep (1 - partitionRatio F.partition .x ⟨n, m, b⟩) := by
  have hs := (absMoment_upper (by norm_num : 0 < 4) hn.1 (D.x_summable m hm)).1
  have hp : 0 < absMoment (D.xSpectrum m) n := by
    rw [← D.x_moment n m hn hm]
    exact F.partition_pos _
  have h := moment_ratio_squaring (D.xSpectrum m) n hs hp
  change 1 - F.partition ⟨2*(2*n), m, b⟩ / F.partition ⟨2*n, m, b⟩ ^ 2 ≤
    purityStep (1 - F.partition ⟨2*n, m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2)
  rw [D.x_moment (2*(2*n)) m hn.double.double hm,
    D.x_moment (2*n) m hn.double hm, D.x_moment n m hn hm]
  simpa only [purityStep, sub_sub_cancel] using h

theorem SpectralFamily.y_ratio_squaring (F : SpectralFamily) {b : ℝ}
    (D : SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩))
    {n m : ℕ} (hn : ValidSize n) (hm : ValidSize m) :
    1 - partitionRatio F.partition .y (doubleCoord .y ⟨n, m, b⟩) ≤
      purityStep (1 - partitionRatio F.partition .y ⟨n, m, b⟩) := by
  have hs := (absMoment_upper (by norm_num : 0 < 4) hm.1 (D.y_summable n hn)).1
  have hp : 0 < absMoment (D.ySpectrum n) m := by
    rw [← D.y_moment n m hn hm]
    exact F.partition_pos _
  have h := moment_ratio_squaring (D.ySpectrum n) m hs hp
  change 1 - F.partition ⟨n, 2*(2*m), b⟩ / F.partition ⟨n, 2*m, b⟩ ^ 2 ≤
    purityStep (1 - F.partition ⟨n, 2*m, b⟩ / F.partition ⟨n, m, b⟩ ^ 2)
  rw [D.y_moment n (2*(2*m)) hn hm.double.double,
    D.y_moment n (2*m) hn hm.double, D.y_moment n m hn hm]
  simpa only [purityStep, sub_sub_cancel] using h

/-- All abstract purity-domain fields are derived from actual Gibbs and moment
data. In particular, neither an upper bound nor a squaring recurrence is assumed. -/
def SpectralFamily.purityDomain (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b →
      SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩)) :
    PurityDomain F.partition ValidVolume where
  closed := fun i v hv => hv.double i
  positive := fun v _ => F.partition_pos v
  upper := by
    intro i v hv
    rcases v with ⟨n, m, b⟩
    rcases hv with ⟨hn, hm, hb⟩
    cases i with
    | x => exact (F.x_ratio_bounds (moments b hb) hn hm).2
    | y => exact (F.y_ratio_bounds (moments b hb) hn hm).2
    | time =>
      rw [F.time_ratio]
      exact finitePurity_le_one _ (fun i => (gibbsWeight_pos _ _ i).le) (gibbsWeight_sum _ _)
  squaring := by
    intro i v hv
    rcases v with ⟨n, m, b⟩
    rcases hv with ⟨hn, hm, hb⟩
    cases i with
    | x => exact F.x_ratio_squaring (moments b hb) hn hm
    | y => exact F.y_ratio_squaring (moments b hb) hn hm
    | time =>
      rw [F.time_ratio, F.time_ratio]
      simpa only [doubleCoord, purityStep, sub_sub_cancel] using
        (gibbs_purity_squaring (F.energy n m) b)

/-- The actual coordinate staircase controls thermal purity at every valid
rectangle in its spatial scale box, at the same inverse temperature. -/
theorem SpectralFamily.rectangle_purity (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b →
      SpatialMomentData (fun L M => F.partition ⟨L, M, b⟩))
    (v : Volume) (hv : ValidVolume v) {L M : ℕ}
    (hL : ValidSize L) (hM : ValidSize M)
    (hnL : v.x ≤ L) (hL2n : L ≤ 2 * v.x)
    (hmM : v.y ≤ M) (hM2m : M ≤ 2 * v.y) :
    (staircaseA F.partition v ^ 4 * staircaseB F.partition v ^ 2 *
      staircaseC F.partition v) ^
        (((L : ℝ) * M) / (4 * (v.x : ℝ) * v.y)) ≤
      partitionRatio F.partition .time ⟨L, M, v.beta⟩ := by
  rcases v with ⟨n, m, b⟩
  rcases hv with ⟨hn, hm, hb⟩
  have h2b : 0 < 2 * b := by positivity
  have h := spatial_purity_interpolation (moments b hb) (moments (2*b) h2b)
    (fun n m _ _ => F.partition_pos ⟨n, m, b⟩)
    hn hm hL hM hnL hL2n hmM hM2m
  simpa only [staircaseA, staircaseB, staircaseC, partitionRatio, doubleCoord] using h

#print axioms SpectralFamily.x_ratio_squaring
#print axioms SpectralFamily.y_ratio_squaring
#print axioms SpectralFamily.purityDomain
#print axioms SpectralFamily.rectangle_purity

end BilayerGap
