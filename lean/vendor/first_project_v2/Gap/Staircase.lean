import Gap.Bootstrap
import Gap.Coordinates

/-!
# Coordinate-indexed staircase: no index diagram is assumed

`PurityDomain` is an explicit interface for valid volumes. Its squaring field
must be supplied from the actual moment/Gibbs representation; it is not a
spectral-gap axiom. The transport identities are proved from `Z` itself.
-/
noncomputable section
namespace BilayerGap

structure PurityDomain (Z : Volume → ℝ) (D : Volume → Prop) where
  closed : ∀ i v, D v → D (doubleCoord i v)
  positive : ∀ v, D v → 0 < Z v
  upper : ∀ i v, D v → partitionRatio Z i v ≤ 1
  squaring : ∀ i v, D v →
    1-partitionRatio Z i (doubleCoord i v) ≤
      purityStep (1-partitionRatio Z i v)

theorem domain_ratio_pos {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (i : Axis) (v : Volume) (hv : D v) :
    0 < partitionRatio Z i v :=
  partitionRatio_pos Z i v (h.positive v hv) (h.positive _ (h.closed i v hv))

theorem domain_cross_transport {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (i j : Axis) (v : Volume) (hv : D v) :
    (partitionRatio Z i v)^2*partitionRatio Z j (doubleCoord i v) ≤
      partitionRatio Z i (doubleCoord j v) :=
  partitionRatio_cross_transport Z i j v (h.positive v hv)
    (h.positive _ (h.closed i v hv)) (h.positive _ (h.closed j v hv))
    (h.positive _ (h.closed j _ (h.closed i v hv))) (h.upper j v hv)

/-- The ordered `i,j,k` update is derived from two exact commuting-square
transports followed by squaring in `i`. -/
theorem domain_component_update {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (i j k : Axis) (v : Volume) (hv : D v) :
    1-partitionRatio Z i (doubleCoord i (doubleCoord k (doubleCoord j v))) ≤
      purityStep (stairDefect (1-partitionRatio Z i v)
        (1-partitionRatio Z j (doubleCoord i v))
        (1-partitionRatio Z k (doubleCoord j (doubleCoord i v)))) := by
  have hi := h.closed i v hv
  have hj := h.closed j v hv
  have hji := h.closed j _ hi
  have hkj := h.closed k _ hj
  have hA := domain_ratio_pos h i v hv
  have hB := domain_ratio_pos h j _ hi
  have hC := domain_ratio_pos h k _ hji
  have hproduct := two_transports_product hA.le hB.le hC.le
    (domain_cross_transport h i j v hv)
    (by simpa only [doubleCoord_comm i j v] using domain_cross_transport h i k (doubleCoord j v) hj)
  apply transport_then_square_bound
    (sub_nonneg.mpr (h.upper i v hv)) (by linarith)
    (sub_nonneg.mpr (h.upper j _ hi)) (by linarith)
    (sub_nonneg.mpr (h.upper k _ hji)) (by linarith)
    (by simp) (by simp) (by simp) (h.upper i _ hkj) hproduct
  exact h.squaring i _ hkj

def diagonalStep (v : Volume) : Volume :=
  doubleCoord .x (doubleCoord .y (doubleCoord .time v))

def staircaseA (Z : Volume → ℝ) (v : Volume) : ℝ := partitionRatio Z .x v

def staircaseB (Z : Volume → ℝ) (v : Volume) : ℝ := partitionRatio Z .y (doubleCoord .x v)

def staircaseC (Z : Volume → ℝ) (v : Volume) : ℝ :=
  partitionRatio Z .time (doubleCoord .y (doubleCoord .x v))

/-- The actual partition-function staircase closes with the exact update order:
old (A,B,C), then new A, then new B. -/
theorem coordinate_staircase_update {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (v : Volume) (hv : D v) :
    (1-staircaseA Z (diagonalStep v) ≤
      purityStep (stairDefect (1-staircaseA Z v) (1-staircaseB Z v) (1-staircaseC Z v))) ∧
    (1-staircaseB Z (diagonalStep v) ≤
      purityStep (stairDefect (1-staircaseB Z v) (1-staircaseC Z v)
        (1-staircaseA Z (diagonalStep v)))) ∧
    (1-staircaseC Z (diagonalStep v) ≤
      purityStep (stairDefect (1-staircaseC Z v) (1-staircaseA Z (diagonalStep v))
        (1-staircaseB Z (diagonalStep v)))) := by
  constructor
  · simpa [staircaseA, staircaseB, staircaseC, diagonalStep, doubleCoord] using
      domain_component_update h .x .y .time v hv
  constructor
  · simpa [staircaseA, staircaseB, staircaseC, diagonalStep, doubleCoord] using
      domain_component_update h .y .time .x (doubleCoord .x v) (h.closed .x v hv)
  · simpa [staircaseA, staircaseB, staircaseC, diagonalStep, doubleCoord] using
      domain_component_update h .time .x .y (doubleCoord .y (doubleCoord .x v))
        (h.closed .y _ (h.closed .x v hv))

/-- The scale sequence doubles both physical sizes and inverse temperature. -/
def scaledVolume (v : Volume) : ℕ → Volume
  | 0 => v
  | j+1 => diagonalStep (scaledVolume v j)

theorem scaledVolume_valid {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (v : Volume) (hv : D v) : ∀ j, D (scaledVolume v j) := by
  intro j
  induction j with
  | zero => exact hv
  | succ j ih => exact h.closed .x _ (h.closed .y _ (h.closed .time _ ih))

/-- Coordinate-level finite-seed propagation, not merely a recurrence on
unnamed scalar sequences. Moment representations still supply `PurityDomain`. -/
theorem coordinate_staircase_bootstrap {Z : Volume → ℝ} {D : Volume → Prop}
    (h : PurityDomain Z D) (v : Volume) (hv : D v) (K r : ℝ)
    (hK : 0 < K) (hr0 : 0 < r) (hr1 : r < 1) (hu0 : r/K < 1)
    (hG : G7 (r/K) ≤ K)
    (hseed : 1-staircaseA Z v ≤ r/K ∧ 1-staircaseB Z v ≤ r/K ∧
      1-staircaseC Z v ≤ r/K) :
    ∀ j, 1-staircaseA Z (scaledVolume v j) ≤ dyadicBound K r j ∧
      1-staircaseB Z (scaledVolume v j) ≤ dyadicBound K r j ∧
      1-staircaseC Z (scaledVolume v j) ≤ dyadicBound K r j := by
  apply dyadic_staircase_bound_of_G7 hK hr0 hr1 hu0 hG
  · intro j
    have hj := scaledVolume_valid h v hv j
    exact ⟨sub_nonneg.mpr (h.upper .x _ hj),
      sub_nonneg.mpr (h.upper .y _ (h.closed .x _ hj)),
      sub_nonneg.mpr (h.upper .time _ (h.closed .y _ (h.closed .x _ hj)))⟩
  · exact hseed
  · intro j
    exact (coordinate_staircase_update h _ (scaledVolume_valid h v hv j)).1
  · intro j
    exact (coordinate_staircase_update h _ (scaledVolume_valid h v hv j)).2.1
  · intro j
    exact (coordinate_staircase_update h _ (scaledVolume_valid h v hv j)).2.2

#print axioms coordinate_staircase_bootstrap
#print axioms domain_component_update
#print axioms coordinate_staircase_update
end BilayerGap
