import Mathlib
import Gap.HistoryCycles

/-!
# Finite collision-excluding transfer kernels

Time is discrete. A bond history assigns either no event or one generator to
each time slot. Two incident occupied bonds at the same slot receive weight
zero. This hard exclusion produces a matching polynomial in the time step.
The transfer is genuinely real symmetric, even for antisymmetric generators:
swapping the two histories leaves every matrix factor unchanged. No transpose,
reversal of time, positive entries, or positive semidefiniteness is used.
-/
noncomputable section
namespace BilayerGap.History
open scoped BigOperators

section FiniteNetwork
variable {S T V B : Type*} [Fintype S] [Fintype T] [Fintype V] [Fintype B]
  [DecidableEq S] [DecidableEq T]

/-- Contraction around an arbitrary finite successor diagram. Cyclic addition
on `Fin L` recovers the usual closed walk sum, for positive `L`. -/
def cyclePartition (next : S → S) (K : Matrix V V ℝ) : ℝ :=
  ∑ x : S → V, ∏ s, K (x s) (x (next s))

/-- A transfer entry after contraction of the physical states along time. -/
def spatialKernel (nextT : T → T) (W : B → B → Matrix V V ℝ) :
    Matrix (T → B) (T → B) ℝ :=
  fun x y => ∑ a : T → V, ∏ t, W (x t) (y t) (a t) (a (nextT t))

/-- A physical one-step operator after contraction of the bond states along
space. This is a sum of tensor products, written in its product basis. -/
def temporalKernel (nextS : S → S) (W : B → B → Matrix V V ℝ) :
    Matrix (S → V) (S → V) ℝ :=
  fun a b => ∑ x : S → B, ∏ s, W (x s) (x (nextS s)) (a s) (b s)

/-- The real symmetry is proved before and independently of any spectral
argument. Signed entries and antisymmetric insertion matrices are allowed. -/
theorem spatialKernel_symmetric (nextT : T → T) (W : B → B → Matrix V V ℝ)
    (hW : ∀ x y, W x y = W y x) :
    (spatialKernel nextT W).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, spatialKernel]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro t _
  rw [hW]

/-- Exact finite space-time exchange. Both sides are evaluations of the same
finite rectangular tensor network, and all products here are real scalars.
This is not an infinite-dimensional trace or a limit interchange. -/
theorem cyclePartition_space_time_exchange (nextS : S → S) (nextT : T → T)
    (W : B → B → Matrix V V ℝ) :
    cyclePartition nextS (spatialKernel nextT W) =
      cyclePartition nextT (temporalKernel nextS W) := by
  classical
  unfold cyclePartition spatialKernel temporalKernel
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : S) (_ : T) => V))
  intro a
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : S) (_ : T) => B))
  intro x
  exact Finset.prod_comm

/-- Exact equality of the spatial and temporal matrix-power traces on a
positive finite rectangular space-time torus. -/
theorem trace_powers_space_time_exchange [DecidableEq V] [DecidableEq B] (space time : ℕ)
    (W : B → B → Matrix V V ℝ) :
    Matrix.trace ((spatialKernel (fun t : Fin (time+1) => t+1) W)^(space+1)) =
      Matrix.trace ((temporalKernel (fun s : Fin (space+1) => s+1) W)^(time+1)) := by
  classical
  rw [HistoryCycles.trace_pow_eq_cycle_sum, HistoryCycles.trace_pow_eq_cycle_sum]
  exact cyclePartition_space_time_exchange (fun s : Fin (space+1) => s+1)
    (fun t : Fin (time+1) => t+1) W

/-- The same exact exchange in explicit permutation coordinates. -/
theorem trace_powers_space_time_exchange_rotate [DecidableEq V] [DecidableEq B]
    (space time : ℕ) (W : B → B → Matrix V V ℝ) :
    Matrix.trace ((spatialKernel (finRotate (time+1)) W)^(space+1)) =
      Matrix.trace ((temporalKernel (finRotate (space+1)) W)^(time+1)) := by
  classical
  rw [HistoryCycles.trace_pow_eq_rotate_sum, HistoryCycles.trace_pow_eq_rotate_sum]
  exact cyclePartition_space_time_exchange (finRotate (space+1)) (finRotate (time+1)) W

end FiniteNetwork

section CollisionExclusion
variable {V B : Type*} [Fintype V] [DecidableEq V]

/-- Symmetric local vertex with all same-time adjacent collisions excluded.
Each selected horizontal bond receives two factors `sqrt(δ*g)`, one at each
endpoint, so its total scalar weight is `δ*g` when `δ*g ≥ 0`. -/
def collisionVertex (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (δ g : ℝ) :
    Option B → Option B → Matrix V V ℝ
  | none, none => 1-δ • h
  | some a, none => Real.sqrt (δ*g) • G a
  | none, some b => Real.sqrt (δ*g) • G b
  | some _, some _ => 0

/-- The collision rule is invariant under swapping incident bond histories. -/
theorem collisionVertex_swap (h : Matrix V V ℝ) (G : B → Matrix V V ℝ)
    (δ g : ℝ) (x y : Option B) :
    collisionVertex h G δ g x y = collisionVertex h G δ g y x := by
  cases x <;> cases y <;> rfl

/-- The scalar weight of an event is exactly the required interaction weight;
there is no unaccounted square root or sign in the finite contraction. -/
theorem collision_event_weight (δ g : ℝ) (hδg : 0 ≤ δ*g) :
    Real.sqrt (δ*g)*Real.sqrt (δ*g) = δ*g := Real.mul_self_sqrt hδg

/-- A concrete finite real symmetric transfer matrix for every number of time
slots. Its state type depends on time resolution and generator count, never
on spatial circumference. -/
def collisionTransfer {T : Type*} [Fintype T] [DecidableEq T] [Fintype B]
    (nextT : T → T) (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (δ g : ℝ) :
    Matrix (T → Option B) (T → Option B) ℝ :=
  spatialKernel nextT (collisionVertex h G δ g)

theorem collisionTransfer_symmetric {T : Type*} [Fintype T] [DecidableEq T] [Fintype B]
    (nextT : T → T) (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (δ g : ℝ) :
    (collisionTransfer nextT h G δ g).IsSymm :=
  spatialKernel_symmetric nextT _ (collisionVertex_swap h G δ g)

#print axioms cyclePartition_space_time_exchange
#print axioms collisionTransfer_symmetric
end CollisionExclusion
end BilayerGap.History
