import Gap.HistoryApproximation
import Gap.TorusHamiltonian
import Gap.HistorySingletons
import Gap.TraceConvexity

/-!
# Exact regrouping of rectangular configurations into columns

All equalities below concern explicit finite matrices in their product bases.
The basis permutation is the ordinary curry/uncurry equivalence. This connects
the history transfer's column operators to the same two-dimensional local
Hamiltonian, rather than assuming equality of partition functions.
-/
noncomputable section
namespace BilayerGap.History
open Torus Matrix
open scoped BigOperators Kronecker Matrix.Norms.Operator

variable {S T V B : Type*} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V]

/-- Flatten the column configuration into the actual rectangular site labeling. -/
def flattenColumns : (S → T → V) ≃ (S×T → V) := (Equiv.curry S T V).symm

def flattenMatrix : Matrix (S → T → V) (S → T → V) ℝ ≃ₐ[ℝ]
    Matrix (S×T → V) (S×T → V) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ flattenColumns

/-- Tensoring an on-site lift through a column is exactly the corresponding
single physical-site lift after regrouping. -/
theorem flatten_nested_siteLift (A : Matrix V V ℝ) (s : S) (t : T) :
    flattenMatrix (siteLift (siteLift A t) s) = siteLift A (s,t) := by
  ext a b
  change siteLift (siteLift A t) s (fun i j => a (i,j)) (fun i j => b (i,j)) = _
  have he : ((∀ i, i ≠ s → (fun j => a (i,j)) = (fun j => b (i,j))) ∧
      (∀ j, j ≠ t → a (s,j)=b (s,j))) ↔
      (∀ p : S×T, p ≠ (s,t) → a p=b p) := by
    constructor
    · rintro ⟨ho,hi⟩ ⟨i,j⟩ hp
      by_cases his : i=s
      · subst i
        exact hi j (fun hjt => hp (by simp [hjt]))
      · exact congrFun (ho i his) j
    · intro h
      constructor
      · intro i hi
        funext j
        exact h (i,j) (fun hh => hi (congrArg Prod.fst hh))
      · intro j hj
        exact h (s,j) (fun hh => hj (congrArg Prod.snd hh))
  simp only [siteLift, ← ite_and, he]
  split_ifs <;> rfl

/-- The same exact regrouping for a vertical two-site operator inside one column. -/
theorem flatten_nested_pairLift (A : Matrix (V×V) (V×V) ℝ) (s : S) (t u : T) :
    flattenMatrix (siteLift (pairLift A t u) s) = pairLift A (s,t) (s,u) := by
  ext a b
  change siteLift (pairLift A t u) s (fun i j => a (i,j)) (fun i j => b (i,j)) = _
  have he : ((∀ i, i ≠ s → (fun j => a (i,j)) = (fun j => b (i,j))) ∧
      (∀ j, j ≠ t → j ≠ u → a (s,j)=b (s,j))) ↔
      (∀ p : S×T, p ≠ (s,t) → p ≠ (s,u) → a p=b p) := by
    constructor
    · rintro ⟨ho,hi⟩ ⟨i,j⟩ hpt hpu
      by_cases his : i=s
      · subst i
        exact hi j (fun hjt => hpt (by simp [hjt])) (fun hju => hpu (by simp [hju]))
      · exact congrFun (ho i his) j
    · intro h
      constructor
      · intro i hi
        funext j
        exact h (i,j) (fun hh => hi (congrArg Prod.fst hh))
          (fun hh => hi (congrArg Prod.fst hh))
      · intro j hjt hju
        exact h (s,j) (fun hh => hjt (congrArg Prod.snd hh))
          (fun hh => hju (congrArg Prod.snd hh))
  simp only [siteLift, pairLift, ← ite_and, he]
  split_ifs <;> rfl

/-- A product of two column generators on distinct columns becomes the
corresponding horizontal pair insertion at their physical rung sites. -/
theorem flatten_horizontal_pair (A B : Matrix V V ℝ) {s u : S} (hsu : s ≠ u) (t : T) :
    flattenMatrix (pairLift ((siteLift A t) ⊗ₖ (siteLift B t)) s u) =
      pairLift (A ⊗ₖ B) (s,t) (u,t) := by
  rw [← siteLift_mul_distinct _ _ hsu, map_mul,
    flatten_nested_siteLift, flatten_nested_siteLift]
  exact siteLift_mul_distinct A B (fun hh => hsu (congrArg Prod.fst hh))

/-- On-site lift is linear in the local operator. -/
theorem siteLift_sum {I : Type*} [Fintype I] (A : I → Matrix V V ℝ) (s : S) :
    siteLift (∑ i, A i) s = ∑ i, siteLift (A i) s := by
  classical
  ext a b
  simp only [siteLift, Matrix.sum_apply]
  split <;> simp

theorem siteLift_sub (A B : Matrix V V ℝ) (s : S) :
    siteLift (A-B) s = siteLift A s-siteLift B s := by
  classical
  ext a b
  simp only [siteLift, Matrix.sub_apply]
  split <;> simp

theorem siteLift_smul (r : ℝ) (A : Matrix V V ℝ) (s : S) :
    siteLift (r • A) s = r • siteLift A s := by
  classical
  ext a b
  simp only [siteLift, Matrix.smul_apply, smul_eq_mul]
  split <;> simp

/-- Relabel all physical sites by an explicit equivalence. -/
def relabelSites (e : S ≃ T) : Matrix (S→V) (S→V) ℝ ≃ₐ[ℝ] Matrix (T→V) (T→V) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (Equiv.arrowCongr e (Equiv.refl V))

theorem relabel_siteLift (e : S ≃ T) (A : Matrix V V ℝ) (s : S) :
    relabelSites e (siteLift A s) = siteLift A (e s) := by
  ext a b
  change siteLift A s (fun i => a (e i)) (fun i => b (e i)) = _
  have he : (∀ i, i ≠ s → a (e i)=b (e i)) ↔
      (∀ j, j ≠ e s → a j=b j) := by
    constructor
    · intro h j hj
      obtain ⟨i,rfl⟩ := e.surjective j
      exact h i (fun hi => hj (by rw [hi]))
    · intro h i hi
      exact h (e i) (fun hh => hi (e.injective hh))
  simp only [siteLift, he]
  split_ifs <;> rfl

theorem relabel_pairLift (e : S ≃ T) (A : Matrix (V×V) (V×V) ℝ) (s u : S) :
    relabelSites e (pairLift A s u) = pairLift A (e s) (e u) := by
  ext a b
  change pairLift A s u (fun i => a (e i)) (fun i => b (e i)) = _
  have he : (∀ i, i ≠ s → i ≠ u → a (e i)=b (e i)) ↔
      (∀ j, j ≠ e s → j ≠ e u → a j=b j) := by
    constructor
    · intro h j hjs hju
      obtain ⟨i,rfl⟩ := e.surjective j
      exact h i (fun hi => hjs (by rw [hi])) (fun hi => hju (by rw [hi]))
    · intro h i his hiu
      exact h (e i) (fun hh => his (e.injective hh)) (fun hh => hiu (e.injective hh))
  simp only [pairLift, he]
  split_ifs <;> rfl

/-- Trace of an exponential is unchanged by a product-basis permutation. -/
theorem trace_exp_reindex {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℝ) :
    Matrix.trace (NormedSpace.exp ℝ ((Matrix.reindexAlgEquiv ℝ ℝ e) A)) =
      Matrix.trace (NormedSpace.exp ℝ A) := by
  have hc : Continuous (Matrix.reindexAlgEquiv ℝ ℝ e) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun M : Matrix I I ℝ => M (e.symm i) (e.symm j))
    fun_prop
  rw [← NormedSpace.map_exp ℝ _ hc]
  change (∑ j, (NormedSpace.exp ℝ A) (e.symm j) (e.symm j)) =
    ∑ i, (NormedSpace.exp ℝ A) i i
  exact Equiv.sum_comp e.symm (fun i => (NormedSpace.exp ℝ A) i i)

section Rectangular
variable [Fintype B]

/-- The column Hamiltonian contains all local terms and periodic transverse bonds. -/
def columnHamiltonian (nextT : Equiv.Perm T) (h : Matrix V V ℝ)
    (G : B → Matrix V V ℝ) (g : ℝ) : Matrix (T→V) (T→V) ℝ :=
  (∑ t, siteLift h t)-g • (∑ t, ∑ a,
    pairLift ((G a) ⊗ₖ (G a)) t (nextT.symm t))

/-- A crossing bond generator acts on one transverse rung of its column. -/
def columnGenerators (G : B → Matrix V V ℝ) : (T×B) → Matrix (T→V) (T→V) ℝ :=
  fun a => siteLift (G a.2) a.1

def rectangularOnSite (h : Matrix V V ℝ) : Matrix (S×T→V) (S×T→V) ℝ :=
  ∑ s, ∑ t, siteLift h (s,t)

def rectangularHorizontal (nextS : Equiv.Perm S) (G : B → Matrix V V ℝ) :
    Matrix (S×T→V) (S×T→V) ℝ :=
  ∑ s, ∑ t, ∑ a, pairLift ((G a) ⊗ₖ (G a)) (s,t) (nextS.symm s,t)

def rectangularVertical (nextT : Equiv.Perm T) (G : B → Matrix V V ℝ) :
    Matrix (S×T→V) (S×T→V) ℝ :=
  ∑ s, ∑ t, ∑ a, pairLift ((G a) ⊗ₖ (G a)) (s,t) (s,nextT.symm t)

/-- A single explicit real Hamiltonian on the full rectangular site space. -/
def rectangularHamiltonian (nextS : Equiv.Perm S) (nextT : Equiv.Perm T)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    Matrix (S×T→V) (S×T→V) ℝ :=
  rectangularOnSite h-g • (rectangularHorizontal nextS G+rectangularVertical nextT G)

/-- The column's on-site sum expands to precisely the on-rung and transverse
bonds of the full rectangular Hamiltonian. -/
theorem flatten_column_onSite (nextT : Equiv.Perm T) (h : Matrix V V ℝ)
    (G : B → Matrix V V ℝ) (g : ℝ) :
    flattenMatrix (onSiteGenerator (columnHamiltonian nextT h G g) :
      Matrix (S→T→V) (S→T→V) ℝ) = rectangularOnSite h-g • rectangularVertical nextT G := by
  rw [onSiteGenerator_eq_site_sum]
  simp only [columnHamiltonian, siteLift_sub, siteLift_sum, siteLift_smul,
    map_sum, map_sub, map_smul, flatten_nested_siteLift, flatten_nested_pairLift,
    Finset.sum_sub_distrib, ← Finset.smul_sum]
  rfl

/-- Crossing-bond insertions become precisely the horizontal physical bonds. -/
theorem flatten_column_interaction (nextS : Equiv.Perm S) (hnext : ∀ s, nextS s ≠ s)
    (G : B → Matrix V V ℝ) :
    flattenMatrix (oneEventGenerator nextS (columnGenerators (T:=T) G)) =
      rectangularHorizontal (T:=T) nextS G := by
  rw [oneEventGenerator_eq_pair_sum nextS hnext]
  simp only [map_sum, Fintype.sum_prod_type, columnGenerators]
  unfold rectangularHorizontal
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro a _
  apply flatten_horizontal_pair
  intro hs
  have he : nextS s = s := by simpa using congrArg nextS hs
  exact hnext s he

/-- The derived strip generator is exactly minus the same full rectangular
Hamiltonian after the explicit curry basis permutation. -/
theorem flatten_strip_generator (nextS : Equiv.Perm S) (nextT : Equiv.Perm T)
    (hnext : ∀ s, nextS s ≠ s) (h : Matrix V V ℝ)
    (G : B → Matrix V V ℝ) (g : ℝ) :
    flattenMatrix (-onSiteGenerator (columnHamiltonian nextT h G g)+
      g • oneEventGenerator nextS (columnGenerators (T:=T) G)) =
      -rectangularHamiltonian nextS nextT h G g := by
  rw [map_add, map_neg, map_smul, flatten_column_onSite,
    flatten_column_interaction nextS hnext]
  unfold rectangularHamiltonian
  simp only [smul_add]
  abel

theorem swap_rectangularOnSite (h : Matrix V V ℝ) :
    relabelSites (Equiv.prodComm T S) (rectangularOnSite (S:=T) (T:=S) h) =
      rectangularOnSite (S:=S) (T:=T) h := by
  simp only [rectangularOnSite, map_sum, relabel_siteLift, Equiv.prodComm_apply]
  exact Finset.sum_comm

theorem swap_rectangularHorizontal (nextT : Equiv.Perm T) (G : B → Matrix V V ℝ) :
    relabelSites (Equiv.prodComm T S) (rectangularHorizontal (T:=S) nextT G) =
      rectangularVertical (S:=S) nextT G := by
  simp only [rectangularHorizontal, rectangularVertical, map_sum,
    relabel_pairLift, Equiv.prodComm_apply]
  exact Finset.sum_comm

theorem swap_rectangularVertical (nextS : Equiv.Perm S) (G : B → Matrix V V ℝ) :
    relabelSites (Equiv.prodComm T S) (rectangularVertical (S:=T) nextS G) =
      rectangularHorizontal (T:=T) nextS G := by
  simp only [rectangularHorizontal, rectangularVertical, map_sum,
    relabel_pairLift, Equiv.prodComm_apply]
  exact Finset.sum_comm

/-- Exchanging the coordinates changes only the physical basis labeling, not
the full Hamiltonian or its trace. -/
theorem swap_rectangularHamiltonian (nextS : Equiv.Perm S) (nextT : Equiv.Perm T)
    (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    relabelSites (Equiv.prodComm T S) (rectangularHamiltonian nextT nextS h G g) =
      rectangularHamiltonian nextS nextT h G g := by
  simp only [rectangularHamiltonian, map_sub, map_smul, map_add,
    swap_rectangularOnSite, swap_rectangularHorizontal, swap_rectangularVertical, add_comm]

theorem rectangularHorizontal_eq_neighbor_sum (nextS : Equiv.Perm S)
    (hnext : ∀ s, nextS s ≠ s) (G : B → Matrix V V ℝ) :
    rectangularHorizontal (T:=T) nextS G =
      ∑ v : S×T, ∑ a, siteLift (G a) v *
        siteLift (G a) ((Equiv.prodCongr nextS (Equiv.refl T)) v) := by
  have hp : ∀ v : S×T, (Equiv.prodCongr nextS (Equiv.refl T)) v ≠ v := by
    intro v hv
    exact hnext v.1 (congrArg Prod.fst hv)
  rw [← oneEventGenerator_eq_neighbor_sum _ hp, oneEventGenerator_eq_pair_sum _ hp]
  simp only [rectangularHorizontal, Fintype.sum_prod_type]
  rfl

theorem rectangularVertical_eq_neighbor_sum (nextT : Equiv.Perm T)
    (hnext : ∀ t, nextT t ≠ t) (G : B → Matrix V V ℝ) :
    rectangularVertical (S:=S) nextT G =
      ∑ v : S×T, ∑ a, siteLift (G a) v *
        siteLift (G a) ((Equiv.prodCongr (Equiv.refl S) nextT) v) := by
  have hp : ∀ v : S×T, (Equiv.prodCongr (Equiv.refl S) nextT) v ≠ v := by
    intro v hv
    exact hnext v.2 (congrArg Prod.snd hv)
  rw [← oneEventGenerator_eq_neighbor_sum _ hp, oneEventGenerator_eq_pair_sum _ hp]
  simp only [rectangularVertical, Fintype.sum_prod_type]
  rfl

/-- A cyclic successor has no fixed points exactly where the two-site bond
interpretation is needed; valid bilayer sizes are all at least four. -/
theorem finRotate_no_fixed {n : ℕ} (hn : 2 ≤ n) : ∀ i : Fin n, finRotate n i ≠ i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro i hi
  rw [finRotate_succ_apply] at hi
  have hone : (1 : Fin (k+1)) = 0 := add_left_cancel (by simpa using hi : i+1=i+0)
  have he := Fin.one_eq_zero_iff.mp hone
  omega

/-- The matrix defined by column transfer regrouping is the actual-length
nearest-neighbor torus Hamiltonian used by the matching seed. -/
theorem rectangular_eq_fullHamiltonian (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (G : B → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) :
    rectangularHamiltonian (finRotate L) (finRotate M) h G g =
      Torus.fullHamiltonian L M h G g := by
  rw [rectangularHamiltonian, rectangularHorizontal_eq_neighbor_sum _ (finRotate_no_fixed hL),
    rectangularVertical_eq_neighbor_sum _ (finRotate_no_fixed hM)]
  simp only [Torus.fullHamiltonian, Torus.fullXNext, Torus.fullYNext,
    rectangularOnSite, Fintype.sum_prod_type]

/-- The actual thermal trace of the same physical Hamiltonian used for seeds. -/
def fullPartition (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : B → Matrix (Fin 4) (Fin 4) ℝ) (g β : ℝ) (L M : ℕ) : ℝ :=
  Matrix.trace (NormedSpace.exp ℝ ((-β) • Torus.fullHamiltonian L M h G g))

/-- Exact identification of the column transfer's limiting partition trace
with the actual two-dimensional Hamiltonian, for every admissible rectangle. -/
theorem column_stripPartition_eq_full (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (G : B → Matrix (Fin 4) (Fin 4) ℝ) (g β : ℝ) :
    stripPartition (columnHamiltonian (finRotate M) h G g)
      (columnGenerators (T:=Fin M) G) g β L = fullPartition h G g β L M := by
  have hm : flattenMatrix (β • stripGenerator L
      (columnHamiltonian (finRotate M) h G g) (columnGenerators (T:=Fin M) G) g) =
      (-β) • Torus.fullHamiltonian L M h G g := by
    rw [map_smul]
    change β • flattenMatrix (-onSiteGenerator (columnHamiltonian (finRotate M) h G g)+
      g • oneEventGenerator (finRotate L) (columnGenerators (T:=Fin M) G)) = _
    rw [flatten_strip_generator _ _ (finRotate_no_fixed hL),
      rectangular_eq_fullHamiltonian L M hL hM]
    simp
  unfold stripPartition fullPartition
  rw [← hm]
  exact (trace_exp_reindex flattenColumns _).symm

/-- Swapping axes preserves the actual rectangular thermal trace. -/
theorem fullPartition_swap (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (G : B → Matrix (Fin 4) (Fin 4) ℝ) (g β : ℝ) :
    fullPartition h G g β L M = fullPartition h G g β M L := by
  have hm : relabelSites (Equiv.prodComm (Fin M) (Fin L))
      (Torus.fullHamiltonian M L h G g) = Torus.fullHamiltonian L M h G g := by
    rw [← rectangular_eq_fullHamiltonian M L hM hL,
      swap_rectangularHamiltonian, rectangular_eq_fullHamiltonian L M hL hM]
  unfold fullPartition
  rw [← hm, ← map_smul]
  exact trace_exp_reindex _ _

/-- Changing only the stated partition function preserves an already
constructed transfer sequence, provided the actual traces agree. -/
def transferLimit_congr {Z W : ℕ → ℝ} (D : FiniteSymmetricTransferLimit Z)
    (h : ∀ n, ValidSize n → Z n = W n) : FiniteSymmetricTransferLimit W where
  dim := D.dim
  transfer := D.transfer
  symmetric := D.symmetric
  trace_limit := by
    intro n hn
    rw [← h n hn]
    exact D.trace_limit n hn

/-- Both spatial transfer hypotheses are proved for the same actual
nearest-neighbor torus Hamiltonian. Neither direction is a user-supplied
representation or convergence assumption. -/
def fullHamiltonian_spatial_limits [DecidableEq B]
    (h : Matrix (Fin 4) (Fin 4) ℝ) (G : B → Matrix (Fin 4) (Fin 4) ℝ)
    (g β : ℝ) (hg : 0 ≤ g) (hβ : 0 ≤ β) :
    FiniteSymmetricSpatialLimits (fullPartition h G g β) where
  x := fun M hM => transferLimit_congr
    (stripTransferLimit (columnHamiltonian (finRotate M) h G g)
      (columnGenerators (T:=Fin M) G) g β hg hβ)
    (fun L hL => column_stripPartition_eq_full L M (by have := hL.1; omega)
      (by have := hM.1; omega) h G g β)
  y := fun L hL => transferLimit_congr
    (stripTransferLimit (columnHamiltonian (finRotate L) h G g)
      (columnGenerators (T:=Fin L) G) g β hg hβ)
    (fun M hM => (column_stripPartition_eq_full M L (by have := hM.1; omega)
      (by have := hL.1; omega) h G g β).trans
      (fullPartition_swap M L (by have := hM.1; omega) (by have := hL.1; omega) h G g β))

/-- Public interface in the actual thermal-partition convention used by the
finite-volume Gibbs and seed modules. -/
def fullHamiltonianSpatialLimits [DecidableEq B]
    (h : Matrix (Fin 4) (Fin 4) ℝ) (G : B → Matrix (Fin 4) (Fin 4) ℝ)
    (g β : ℝ) (hg : 0 ≤ g) (hβ : 0 ≤ β) :
    FiniteSymmetricSpatialLimits (fun L M =>
      TraceConvexity.partition (Torus.fullHamiltonian L M h G g) β) :=
  fullHamiltonian_spatial_limits h G g β hg hβ

#print axioms fullHamiltonianSpatialLimits

#print axioms fullHamiltonian_spatial_limits

end Rectangular

#print axioms flatten_nested_siteLift
#print axioms flatten_nested_pairLift
#print axioms flatten_horizontal_pair
end BilayerGap.History
