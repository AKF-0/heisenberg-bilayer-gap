import Dressed.QuarticBondRegrouping
import Mathlib.Data.Set.Insert
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticCoefficientFibers
open GlobalResidual QuarticBondRegrouping LocalBond
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An injective finite parametrization has coefficient one at each image point. -/
theorem sum_injective_delta {T W : Type*} [Fintype T] [DecidableEq W]
    (f : T → W) (hf : Function.Injective f) (a : W → ℝ) (w : W) :
    (∑ t, if f t=w then a (f t) else 0) =
      if w ∈ Set.range f then a w else 0 := by
  classical
  by_cases hw : w ∈ Set.range f
  · obtain ⟨t,rfl⟩ := hw
    rw [if_pos (Set.mem_range_self t)]
    rw [Finset.sum_eq_single t]
    · simp
    · intro b _ hb
      simp [hf.ne hb]
    · simp
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro t _
    have ht : f t ≠ w := by
      intro he
      exact hw ⟨t,he⟩
    simp [ht]

/-- Exact coefficient of a specified ordered pair word in the literal source list. -/
def tupleCoefficient (K : V → V → ℝ) (u v : V) (s : Fin 4 → V) : ℝ :=
  ∑ t : BondTerm u v, if termSites u v t=s then termCoefficient K u v t else 0

/-- Equality of four-entry tuples is reduced to four concrete site equalities. -/
theorem tuple_eq_iff (a b c d a' b' c' d' : V) :
    (![a,b,c,d] : Fin 4 → V)=![a',b',c',d'] ↔
      a=a' ∧ b=b' ∧ c=c' ∧ d=d' := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,congrFun h 3⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

/-- Site range conditions for the explicit endpoint-excluded source families. -/
def outsideCondition (u v a : V) : Prop := a ≠ u ∧ a ≠ v

def tripleSites (u v a : V) (p : TripleOutside u v) : Fin 4 → V :=
  ![a,p.1,p.2.1,p.2.2]

def crossSites (u v : V) (p : PairOutside u v) : Fin 4 → V := ![u,p.1,v,p.2]
def pairedSites (u v : V) (p : PairOutside u v) : Fin 4 → V := ![u,v,p.1,p.2]

theorem tripleSites_injective (u v a : V) : Function.Injective (tripleSites u v a) := by
  intro p q h
  apply Prod.ext
  · exact Subtype.ext (congrFun h 1)
  · apply Prod.ext
    · exact Subtype.ext (congrFun h 2)
    · exact Subtype.ext (congrFun h 3)

theorem crossSites_injective (u v : V) : Function.Injective (crossSites u v) := by
  intro p q h
  exact Prod.ext (Subtype.ext (congrFun h 1)) (Subtype.ext (congrFun h 3))

theorem pairedSites_injective (u v : V) : Function.Injective (pairedSites u v) := by
  intro p q h
  exact Prod.ext (Subtype.ext (congrFun h 2)) (Subtype.ext (congrFun h 3))

theorem tripleSites_range (u v x a b c d : V) :
    (![a,b,c,d] : Fin 4 → V) ∈ Set.range (tripleSites u v x) ↔
      x=a ∧ outsideCondition u v b ∧ outsideCondition u v c ∧ outsideCondition u v d := by
  constructor
  · rintro ⟨p,h⟩
    have h0 : x=a := congrFun h 0
    have h1 : (p.1 : V)=b := congrFun h 1
    have h2 : (p.2.1 : V)=c := congrFun h 2
    have h3 : (p.2.2 : V)=d := congrFun h 3
    exact ⟨h0,h1 ▸ p.1.property,h2 ▸ p.2.1.property,h3 ▸ p.2.2.property⟩
  · rintro ⟨rfl,hb,hc,hd⟩
    exact ⟨(⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩),rfl⟩

theorem crossSites_range (u v a b c d : V) :
    (![a,b,c,d] : Fin 4 → V) ∈ Set.range (crossSites u v) ↔
      u=a ∧ v=c ∧ outsideCondition u v b ∧ outsideCondition u v d := by
  constructor
  · rintro ⟨p,h⟩
    have h0 : u=a := congrFun h 0
    have h1 : (p.1 : V)=b := congrFun h 1
    have h2 : v=c := congrFun h 2
    have h3 : (p.2 : V)=d := congrFun h 3
    exact ⟨h0,h2,h1 ▸ p.1.property,h3 ▸ p.2.property⟩
  · rintro ⟨rfl,rfl,hb,hd⟩
    exact ⟨(⟨b,hb⟩,⟨d,hd⟩),rfl⟩

theorem pairedSites_range (u v a b c d : V) :
    (![a,b,c,d] : Fin 4 → V) ∈ Set.range (pairedSites u v) ↔
      u=a ∧ v=b ∧ outsideCondition u v c ∧ outsideCondition u v d := by
  constructor
  · rintro ⟨p,h⟩
    have h0 : u=a := congrFun h 0
    have h1 : v=b := congrFun h 1
    have h2 : (p.1 : V)=c := congrFun h 2
    have h3 : (p.2 : V)=d := congrFun h 3
    exact ⟨h0,h1,h2 ▸ p.1.property,h3 ▸ p.2.property⟩
  · rintro ⟨rfl,rfl,hc,hd⟩
    exact ⟨(⟨c,hc⟩,⟨d,hd⟩),rfl⟩

/-- Explicit ordered tuple weight. Every condition comes from the literal
outside-field indices; this is not a separately assumed coefficient formula. -/
def orderedWeight (K : V → V → ℝ) (u v a b c d : V) : ℝ :=
  (if u=a ∧ outsideCondition u v b ∧ outsideCondition u v c ∧ outsideCondition u v d
    then -(K u b*K u c*K v d) else 0) +
  (if v=a ∧ outsideCondition u v b ∧ outsideCondition u v c ∧ outsideCondition u v d
    then -(K v b*K u c*K v d) else 0) +
  (if u=a ∧ v=c ∧ outsideCondition u v b ∧ outsideCondition u v d
    then K v b*K u d-K u b*K u d-K v b*K v d+3*K u v*K u b*K v d else 0) +
  (if u=a ∧ v=b ∧ outsideCondition u v c ∧ outsideCondition u v d
    then -((1+K u v)*K u c*K v d) else 0)

theorem tupleCoefficient_eq_orderedWeight (K : V → V → ℝ) (u v a b c d : V) :
    tupleCoefficient K u v ![a,b,c,d] = orderedWeight K u v a b c d := by
  have h1 := sum_injective_delta (tripleSites u v u) (tripleSites_injective u v u)
    (fun s => -(K u (s 1)*K u (s 2)*K v (s 3))) ![a,b,c,d]
  have h2 := sum_injective_delta (tripleSites u v v) (tripleSites_injective u v v)
    (fun s => -(K v (s 1)*K u (s 2)*K v (s 3))) ![a,b,c,d]
  have h3 := sum_injective_delta (crossSites u v) (crossSites_injective u v)
    (fun s => K v (s 1)*K u (s 3)-K u (s 1)*K u (s 3)-K v (s 1)*K v (s 3)+
      3*K u v*K u (s 1)*K v (s 3)) ![a,b,c,d]
  have h4 := sum_injective_delta (pairedSites u v) (pairedSites_injective u v)
    (fun s => -((1+K u v)*K u (s 2)*K v (s 3))) ![a,b,c,d]
  simp only [tripleSites_range] at h1 h2
  simp only [crossSites_range] at h3
  simp only [pairedSites_range] at h4
  simpa only [tupleCoefficient,Fintype.sum_sum_type,termSites,termCoefficient,
    tripleSites,crossSites,pairedSites,orderedWeight,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,add_assoc]
    using congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2) (congrArg₂ (· + ·) h3 h4)

/-- Unordered physical matching of the four site entries. -/
def pairing (s : Fin 4 → V) : Finset (Finset V) :=
  {{s 0,s 1},{s 2,s 3}}

/-- The union of the two unordered pairs is exactly the actual four-site image. -/
theorem union_pairing (s : Fin 4 → V) :
    (pairing s).biUnion id = Finset.univ.image s := by
  ext x
  simp [pairing,Fin.exists_fin_succ,or_assoc,eq_comm]
  tauto

/-- The eight ordered tuples representing the same two unordered pairs. -/
def orientations (s : Fin 4 → V) : Fin 8 → Fin 4 → V :=
  ![![s 0,s 1,s 2,s 3], ![s 1,s 0,s 2,s 3],
    ![s 0,s 1,s 3,s 2], ![s 1,s 0,s 3,s 2],
    ![s 2,s 3,s 0,s 1], ![s 3,s 2,s 0,s 1],
    ![s 2,s 3,s 1,s 0], ![s 3,s 2,s 1,s 0]]

theorem finset_pair_eq_iff {A : Type*} [DecidableEq A] (a b c d : A) :
    ({a,b} : Finset A)={c,d} ↔ a=c ∧ b=d ∨ a=d ∧ b=c := by
  rw [← Finset.coe_inj]
  simpa only [Finset.coe_insert,Finset.coe_singleton] using
    (Set.pair_eq_pair_iff : ({a,b} : Set A)={c,d} ↔ _)

/-- Finite classification of an unordered matching, without operator assumptions. -/
theorem pairing_eq_iff (s t : Fin 4 → V) :
    pairing s=pairing t ↔ ∃ i : Fin 8, s=orientations t i := by
  constructor
  · intro hp
    rcases (finset_pair_eq_iff {s 0,s 1} {s 2,s 3} {t 0,t 1} {t 2,t 3}).mp hp with h | h
    · rcases (finset_pair_eq_iff _ _ _ _).mp h.1 with h01 | h01
      · rcases (finset_pair_eq_iff _ _ _ _).mp h.2 with h23 | h23
        · refine ⟨0,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
        · refine ⟨2,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
      · rcases (finset_pair_eq_iff _ _ _ _).mp h.2 with h23 | h23
        · refine ⟨1,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
        · refine ⟨3,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
    · rcases (finset_pair_eq_iff _ _ _ _).mp h.1 with h01 | h01
      · rcases (finset_pair_eq_iff _ _ _ _).mp h.2 with h23 | h23
        · refine ⟨4,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
        · refine ⟨6,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
      · rcases (finset_pair_eq_iff _ _ _ _).mp h.2 with h23 | h23
        · refine ⟨5,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
        · refine ⟨7,?_⟩
          ext j
          fin_cases j <;> simp [orientations,h01.1,h01.2,h23.1,h23.2]
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [pairing,orientations,Finset.pair_comm,Finset.insert_comm]

theorem orientations_injective (s : Fin 4 → V) (hs : Function.Injective s) :
    Function.Injective (orientations s) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [orientations, tuple_eq_iff, hs.eq_iff]

theorem orientation_tuple_injective (s : Fin 4 → V) (hs : Function.Injective s)
    (i : Fin 8) : Function.Injective (orientations s i) := by
  intro a b hab
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp_all [orientations,hs.eq_iff]

theorem injective_of_pairing_eq (s t : Fin 4 → V) (ht : Function.Injective t)
    (hp : pairing s=pairing t) : Function.Injective s := by
  obtain ⟨i,hi⟩ := (pairing_eq_iff s t).mp hp
  rw [hi]
  exact orientation_tuple_injective t ht i

/-- Actual source coefficient of one unordered matching. -/
def matchingCoefficient (K : V → V → ℝ) (u v : V) (s : Fin 4 → V) : ℝ :=
  ∑ t : BondTerm u v,
    if pairing (termSites u v t)=pairing s then termCoefficient K u v t else 0

/-- Every unordered matching fiber consists of exactly its eight ordered
representatives, evaluated against the literal source family. -/
theorem matchingCoefficient_eq_orientation_sum (K : V → V → ℝ) (u v : V)
    (s : Fin 4 → V) (hs : Function.Injective s) :
    matchingCoefficient K u v s = ∑ i : Fin 8, tupleCoefficient K u v (orientations s i) := by
  unfold matchingCoefficient
  calc
    _ = ∑ t : BondTerm u v, ∑ i : Fin 8,
        if termSites u v t=orientations s i then termCoefficient K u v t else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      have hh := sum_injective_delta (orientations s) (orientations_injective s hs)
        (fun _ => termCoefficient K u v t) (termSites u v t)
      simp only [pairing_eq_iff (termSites u v t) s]
      simpa only [Set.mem_range,eq_comm] using hh.symm
    _ = ∑ i : Fin 8, ∑ t : BondTerm u v,
        if termSites u v t=orientations s i then termCoefficient K u v t else 0 :=
      Finset.sum_comm
    _ = _ := rfl
/-- Bonds disjoint from a four-site support contribute exactly zero. -/
theorem matchingCoefficient_disjoint (K : V → V → ℝ) (u v : V) (s : Fin 4 → V)
    (hs : Function.Injective s) (hu : ∀ i, u ≠ s i) (hv : ∀ i, v ≠ s i) :
    matchingCoefficient K u v s = 0 := by
  rw [matchingCoefficient_eq_orientation_sum K u v s hs]
  simp [orientations,Fin.sum_univ_succ,tupleCoefficient_eq_orderedWeight,
    orderedWeight,hu,hv]

/-- One occupied endpoint: exactly two ordered outside-field source terms. -/
theorem matchingCoefficient_left_only (K : V → V → ℝ) (u v b c d : V)
    (hs : Function.Injective (![u,b,c,d] : Fin 4 → V))
    (hv : ∀ i : Fin 4, v ≠ (![u,b,c,d] : Fin 4 → V) i) :
    matchingCoefficient K u v ![u,b,c,d] =
      -K u b*(K u c*K v d+K u d*K v c) := by
  have h01 : u ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : u ≠ c := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : u ≠ d := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : b ≠ c := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : b ≠ d := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : c ≠ d := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  have hv0 : v ≠ u := hv 0
  have hv1 : v ≠ b := hv 1
  have hv2 : v ≠ c := hv 2
  have hv3 : v ≠ d := hv 3
  rw [matchingCoefficient_eq_orientation_sum K u v _ hs]
  simp [orientations,Fin.sum_univ_succ,tupleCoefficient_eq_orderedWeight,
    orderedWeight,outsideCondition,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm,
    hv0,hv1,hv2,hv3,hv0.symm,hv1.symm,hv2.symm,hv3.symm]
  ring

/-- The other one-endpoint source family, with its actual asymmetric bond order. -/
theorem matchingCoefficient_right_only (K : V → V → ℝ) (u v b c d : V)
    (hs : Function.Injective (![v,b,c,d] : Fin 4 → V))
    (hu : ∀ i : Fin 4, u ≠ (![v,b,c,d] : Fin 4 → V) i) :
    matchingCoefficient K u v ![v,b,c,d] =
      -K v b*(K u c*K v d+K u d*K v c) := by
  have h01 : v ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : v ≠ c := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : v ≠ d := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : b ≠ c := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : b ≠ d := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : c ≠ d := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  have hu0 : u ≠ v := hu 0
  have hu1 : u ≠ b := hu 1
  have hu2 : u ≠ c := hu 2
  have hu3 : u ≠ d := hu 3
  rw [matchingCoefficient_eq_orientation_sum K u v _ hs]
  simp [orientations,Fin.sum_univ_succ,tupleCoefficient_eq_orderedWeight,
    orderedWeight,outsideCondition,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm,
    hu0,hu1,hu2,hu3,hu0.symm,hu1.symm,hu2.symm,hu3.symm]
  ring

/-- Both occupied endpoints paired together: two orientations of the other pair. -/
theorem matchingCoefficient_endpoints_paired (K : V → V → ℝ) (u v a b : V)
    (hs : Function.Injective (![u,v,a,b] : Fin 4 → V)) :
    matchingCoefficient K u v ![u,v,a,b] =
      -(1+K u v)*(K u a*K v b+K u b*K v a) := by
  have h01 : u ≠ v := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : u ≠ a := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : u ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : v ≠ a := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : v ≠ b := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : a ≠ b := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  rw [matchingCoefficient_eq_orientation_sum K u v _ hs]
  simp [orientations,Fin.sum_univ_succ,tupleCoefficient_eq_orderedWeight,
    orderedWeight,outsideCondition,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm]
  ring

/-- Crossed occupied endpoints: exactly the literal four-term crossed coefficient. -/
theorem matchingCoefficient_endpoints_crossed (K : V → V → ℝ) (u v a b : V)
    (hs : Function.Injective (![u,a,v,b] : Fin 4 → V)) :
    matchingCoefficient K u v ![u,a,v,b] =
      K v a*K u b-K u a*K u b-K v a*K v b+3*K u v*K u a*K v b := by
  have h01 : u ≠ a := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : u ≠ v := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : u ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : a ≠ v := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : a ≠ b := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : v ≠ b := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  rw [matchingCoefficient_eq_orientation_sum K u v _ hs]
  simp [orientations,Fin.sum_univ_succ,tupleCoefficient_eq_orderedWeight,
    orderedWeight,outsideCondition,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm]


end BilayerDressed.QuarticCoefficientFibers
