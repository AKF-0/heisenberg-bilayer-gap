import Dressed.ConcreteSeedGraphs

/-! Small exact graph checks. Only 16/32/64 rung vertices are enumerated;
no many-body Hilbert space is enumerated. Kernel reduction, not native_decide. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicSeedChecks
open BilayerGap BilayerDressed.SeedGraphs

def step (n m : ℕ) (F : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ) :
    Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ := fun u v =>
  F (Torus.xNext n m u) v + F ((Torus.xNext n m).symm u) v +
  F (Torus.yNext n m u) v + F ((Torus.yNext n m).symm u) v

def walk2 (n m : ℕ) := step n m (adjacencyNat n m)
def walk3 (n m : ℕ) := step n m (walk2 n m)
def offWalk2 (n m : ℕ) : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ :=
  fun u v => if u=v then 0 else walk2 n m u v

theorem adjacency_mul (n m : ℕ) (hi : IncidenceIdentity n m)
    (F : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ) :
    adjacencyNat n m*F=step n m F := by
  unfold IncidenceIdentity at hi
  ext u v
  have hx (k : Torus.Vertex n m) : (u=Torus.xNext n m k) ↔ k=(Torus.xNext n m).symm u := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  have hy (k : Torus.Vertex n m) : (u=Torus.yNext n m k) ↔ k=(Torus.yNext n m).symm u := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  simp only [Matrix.mul_apply,hi,add_mul,Finset.sum_add_distrib,hx,hy]
  simp [step,ite_mul]

theorem walk2_eq (n m : ℕ) (hi : IncidenceIdentity n m) :
    walk2 n m=adjacencyNat n m*adjacencyNat n m :=
  (adjacency_mul n m hi _).symm

theorem walk3_eq (n m : ℕ) (hi : IncidenceIdentity n m) :
    walk3 n m=adjacencyNat n m*adjacencyNat n m*adjacencyNat n m := by
  rw [walk3,←adjacency_mul n m hi,walk2_eq n m hi,←mul_assoc]

def CubicConditions (n m total : ℕ) : Prop :=
  (∀ u v, adjacencyNat n m u v=1 → 8≤walk3 n m u v) ∧
  (∀ u v, offWalk2 n m u v=0 ∨ walk3 n m u v=0) ∧
  (∀ u, ∑ v, (1640*adjacencyNat n m u v+84*offWalk2 n m u v+5*walk3 n m u v)^2=total)

section Translation
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

private theorem rotate_apply {q : ℕ} [NeZero q] (u : Fin q) : finRotate q u=u+1 := by
  cases q with
  | zero => exact Fin.elim0 u
  | succ q => exact finRotate_succ_apply u

 theorem xNext_add (u t : Torus.Vertex n m) :
    Torus.xNext n m (u+t)=Torus.xNext n m u+t := by
  ext <;> simp [Torus.xNext,rotate_apply,add_assoc,add_comm,add_left_comm]

 theorem yNext_add (u t : Torus.Vertex n m) :
    Torus.yNext n m (u+t)=Torus.yNext n m u+t := by
  ext <;> simp [Torus.yNext,rotate_apply,add_assoc,add_comm,add_left_comm]

 theorem xPrev_add (u t : Torus.Vertex n m) :
    (Torus.xNext n m).symm (u+t)=(Torus.xNext n m).symm u+t := by
  apply (Torus.xNext n m).injective
  rw [Equiv.apply_symm_apply,xNext_add,Equiv.apply_symm_apply]

 theorem yPrev_add (u t : Torus.Vertex n m) :
    (Torus.yNext n m).symm (u+t)=(Torus.yNext n m).symm u+t := by
  apply (Torus.yNext n m).injective
  rw [Equiv.apply_symm_apply,yNext_add,Equiv.apply_symm_apply]

 theorem adjacency_translate (u v t : Torus.Vertex n m) :
    adjacencyNat n m (u+t) (v+t)=adjacencyNat n m u v := by
  simp [adjacencyNat,adjacent,xNext_add,yNext_add]

 theorem step_translate (F : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℕ)
    (hF : ∀ u v t, F (u+t) (v+t)=F u v) (u v t : Torus.Vertex n m) :
    step n m F (u+t) (v+t)=step n m F u v := by
  simp only [step,xNext_add,yNext_add,xPrev_add,yPrev_add,hF]

 theorem walk2_translate (u v t : Torus.Vertex n m) :
    walk2 n m (u+t) (v+t)=walk2 n m u v :=
  step_translate n m _ (adjacency_translate n m) u v t

 theorem walk3_translate (u v t : Torus.Vertex n m) :
    walk3 n m (u+t) (v+t)=walk3 n m u v :=
  step_translate n m _ (walk2_translate n m) u v t

 theorem offWalk2_translate (u v t : Torus.Vertex n m) :
    offWalk2 n m (u+t) (v+t)=offWalk2 n m u v := by
  simp [offWalk2,walk2_translate]

 theorem adjacency_rooted (u v : Torus.Vertex n m) :
    adjacencyNat n m u v=adjacencyNat n m 0 (v-u) := by
  simpa using adjacency_translate n m 0 (v-u) u

 theorem walk3_rooted (u v : Torus.Vertex n m) :
    walk3 n m u v=walk3 n m 0 (v-u) := by
  simpa using walk3_translate n m 0 (v-u) u

 theorem offWalk2_rooted (u v : Torus.Vertex n m) :
    offWalk2 n m u v=offWalk2 n m 0 (v-u) := by
  simpa using offWalk2_translate n m 0 (v-u) u

def RootedCubicConditions (total : ℕ) : Prop :=
  (∀ v, adjacencyNat n m 0 v=1 → 8≤walk3 n m 0 v) ∧
  (∀ v, offWalk2 n m 0 v=0 ∨ walk3 n m 0 v=0) ∧
  ((∑ v, (1640*adjacencyNat n m 0 v+84*offWalk2 n m 0 v+5*walk3 n m 0 v)^2)=total)

 theorem rooted_implies_cubic (total : ℕ) (h : RootedCubicConditions n m total) :
    CubicConditions n m total := by
  constructor
  · intro u v huv
    rw [adjacency_rooted n m u v] at huv
    rw [walk3_rooted n m u v]
    exact h.1 (v-u) huv
  constructor
  · intro u v
    rw [offWalk2_rooted n m u v,walk3_rooted n m u v]
    exact h.2.1 (v-u)
  · intro u
    simp_rw [adjacency_rooted n m u,offWalk2_rooted n m u,walk3_rooted n m u]
    have hh := (Equiv.subRight u).sum_comp (fun v : Torus.Vertex n m =>
      (1640*adjacencyNat n m 0 v+84*offWalk2 n m 0 v+5*walk3 n m 0 v)^2)
    rw [show (∑ v, (1640*adjacencyNat n m 0 (v-u)+84*offWalk2 n m 0 (v-u)+5*walk3 n m 0 (v-u))^2) =
      ∑ v, (1640*adjacencyNat n m 0 v+84*offWalk2 n m 0 v+5*walk3 n m 0 v)^2 by
      simpa using hh]
    exact h.2.2
end Translation

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem four_by_four_cubic : CubicConditions 2 2 11597344 := by
  apply rooted_implies_cubic
  unfold RootedCubicConditions
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_four_conditions : Conditions 4 2 := by unfold Conditions; decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_four_incidence : IncidenceIdentity 4 2 := by
  unfold IncidenceIdentity; decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_four_cubic : CubicConditions 4 2 11548632 := by
  apply rooted_implies_cubic
  unfold RootedCubicConditions
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem eight_by_eight_cubic : CubicConditions 4 4 11499920 := by
  apply rooted_implies_cubic
  unfold RootedCubicConditions
  decide +kernel

end BilayerDressed.CubicSeedChecks
