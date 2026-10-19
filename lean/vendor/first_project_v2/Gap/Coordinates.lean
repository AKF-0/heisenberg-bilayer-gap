import Mathlib

/-!
# Partition ratios on actual coordinate doublings

The partition function is supplied as an explicit parameter. Positivity and the
upper bound are required only at the displayed nodes, not at invalid/odd sizes.
The premise that every ratio is at most one is NOT inferred from positivity.
For the physical application it has to come from the moment/Gibbs representations.
-/
noncomputable section

namespace BilayerGap

inductive Axis where
  | x | y | time
  deriving DecidableEq

structure Volume where
  x : ℕ
  y : ℕ
  beta : ℝ

/-- Doubling one of the two spatial sizes or the inverse temperature. -/
def doubleCoord (i : Axis) (v : Volume) : Volume :=
  match i with
  | .x => {v with x := 2*v.x}
  | .y => {v with y := 2*v.y}
  | .time => {v with beta := 2*v.beta}

theorem doubleCoord_comm (i j : Axis) (v : Volume) :
    doubleCoord i (doubleCoord j v) = doubleCoord j (doubleCoord i v) := by
  cases i <;> cases j <;> rfl

/-- The exact partition ratio, rather than an abstract variable called purity. -/
def partitionRatio (Z : Volume → ℝ) (i : Axis) (v : Volume) : ℝ :=
  Z (doubleCoord i v) / Z v ^ 2

theorem partitionRatio_pos (Z : Volume → ℝ) (i : Axis) (v : Volume)
    (hv : 0 < Z v) (hi : 0 < Z (doubleCoord i v)) :
    0 < partitionRatio Z i v := by
  exact div_pos hi (sq_pos_of_pos hv)

/-- Commuting-square identity with all coordinate indices retained. -/
theorem partitionRatio_commuting_square (Z : Volume → ℝ)
    (i j : Axis) (v : Volume)
    (hv : Z v ≠ 0) (hi : Z (doubleCoord i v) ≠ 0)
    (hj : Z (doubleCoord j v) ≠ 0) :
    partitionRatio Z i (doubleCoord j v) =
      (partitionRatio Z i v)^2 * partitionRatio Z j (doubleCoord i v) /
        (partitionRatio Z j v)^2 := by
  unfold partitionRatio
  rw [doubleCoord_comm i j v]
  field_simp [hv, hi, hj]

/-- Transverse transport needs the genuine-purity upper bound as an explicit premise. -/
theorem partitionRatio_cross_transport (Z : Volume → ℝ) (i j : Axis) (v : Volume)
    (hv : 0 < Z v) (hi : 0 < Z (doubleCoord i v))
    (hj : 0 < Z (doubleCoord j v))
    (hij : 0 < Z (doubleCoord j (doubleCoord i v)))
    (hupper : partitionRatio Z j v ≤ 1) :
    (partitionRatio Z i v)^2 * partitionRatio Z j (doubleCoord i v) ≤
      partitionRatio Z i (doubleCoord j v) := by
  rw [partitionRatio_commuting_square Z i j v hv.ne' hi.ne' hj.ne']
  have hp := partitionRatio_pos Z j v hv hj
  have hs : (partitionRatio Z j v)^2 ≤ 1 := by nlinarith
  have hnum : 0 ≤ (partitionRatio Z i v)^2 * partitionRatio Z j (doubleCoord i v) := by
    exact mul_nonneg (sq_nonneg _) (partitionRatio_pos Z j (doubleCoord i v) hi hij).le
  exact le_div_self hnum (by positivity) hs

#print axioms doubleCoord_comm
#print axioms partitionRatio_commuting_square
#print axioms partitionRatio_cross_transport
end BilayerGap
