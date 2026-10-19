import Dressed.FourRegularKernel
import Gap.TorusGeometry

/-! Exact small graph certificates for the seed tori. These enumerate only
adjacency/walk identities on at most 64 vertices, never the many-spin Hamiltonian. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.SeedGraphs
open BilayerGap

def adjacent (n m : ℕ) (u v : Torus.Vertex n m) : Prop :=
  v=Torus.xNext n m u ∨ u=Torus.xNext n m v ∨
  v=Torus.yNext n m u ∨ u=Torus.yNext n m v
instance adjacentDecidable (n m : ℕ) (u v : Torus.Vertex n m) : Decidable (adjacent n m u v) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def adjacencyNat (n m : ℕ) : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ :=
  fun u v => if adjacent n m u v then 1 else 0

def Conditions (n m : ℕ) : Prop :=
  (∀ u, adjacencyNat n m u u=0 ∧ (∑ v, adjacencyNat n m u v)=4) ∧
  (∀ u v, adjacencyNat n m u v=1 →
    (adjacencyNat n m*adjacencyNat n m) u v=0)

set_option maxHeartbeats 0 in
theorem four_by_four_conditions : Conditions 2 2 := by unfold Conditions; decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_eight_conditions : Conditions 4 4 := by unfold Conditions; decide +kernel

/-- Cast exact finite natural adjacency facts into the real graph interface. -/
def graph (n m : ℕ) (h : Conditions n m) : FourRegularData (Torus.Vertex n m) where
  adjacency := fun u v => (adjacencyNat n m u v : ℝ)
  symmetric := by
    intro u v
    have hh : adjacent n m u v ↔ adjacent n m v u := by unfold adjacent; tauto
    simp [adjacencyNat, hh]
  binary := by
    intro u v
    unfold adjacencyNat
    split_ifs <;> simp
  diagonal := by intro u; rw [(h.1 u).1]; norm_num
  degree := by
    intro u
    exact_mod_cast (h.1 u).2
  triangle_free := by
    intro u v huv
    have hn : adjacencyNat n m u v=1 := by exact_mod_cast huv
    have ht := h.2 u v hn
    have hc := congrArg (fun x : ℕ => (x : ℝ)) ht
    simpa only [Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul, Nat.cast_zero] using hc

def fourByFour : FourRegularData (Torus.Vertex 2 2) := graph 2 2 four_by_four_conditions

def eightByEight : FourRegularData (Torus.Vertex 4 4) := graph 4 4 eight_by_eight_conditions

/-- The physical Hamiltonian has one forward horizontal and one forward vertical
bond per vertex. This certificate identifies their undirected incidence sum
with the simple adjacency, so no accidental multiple-edge convention is used. -/
def IncidenceIdentity (n m : ℕ) : Prop := ∀ u v : Torus.Vertex n m,
  adjacencyNat n m u v =
    (if v=Torus.xNext n m u then 1 else 0) +
    (if u=Torus.xNext n m v then 1 else 0) +
    (if v=Torus.yNext n m u then 1 else 0) +
    (if u=Torus.yNext n m v then 1 else 0)

set_option maxHeartbeats 0 in
theorem four_by_four_incidence : IncidenceIdentity 2 2 := by
  unfold IncidenceIdentity; decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_eight_incidence : IncidenceIdentity 4 4 := by
  unfold IncidenceIdentity; decide +kernel

 theorem graph_incidence (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) :
    (graph n m h).adjacency u v =
      (if v=Torus.xNext n m u then (1 : ℝ) else 0) +
      (if u=Torus.xNext n m v then 1 else 0) +
      (if v=Torus.yNext n m u then 1 else 0) +
      (if u=Torus.yNext n m v then 1 else 0) := by
  change (adjacencyNat n m u v : ℝ) = _
  have hh := congrArg (fun x : ℕ => (x : ℝ)) (hi u v)
  simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh

end BilayerDressed.SeedGraphs
