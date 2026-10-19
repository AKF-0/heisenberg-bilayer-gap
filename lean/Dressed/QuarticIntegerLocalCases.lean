import Dressed.QuarticIntegerDirect

/-!
# Exact fast local cases for signed quartic integer coefficients

These formulas are derived from the frozen eight-orientation source sum. They
preserve signed array coefficients and both ordered bond endpoints. No symmetry
of the kernel or external coefficient table is assumed.
-/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerLocalCases
open QuarticIntegerArrays QuarticIntegerDirect QuarticCoefficientFibers
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exactly the two surviving one-left-endpoint source terms. -/
def leftOnly (K : V → V → KernelCoefficients) (u v a b c : V) : Coefficients :=
  -(triple (K u a) (K u b) (K v c) + triple (K u a) (K u c) (K v b))

/-- The asymmetric one-right-endpoint source terms retain the original bond order. -/
def rightOnly (K : V → V → KernelCoefficients) (u v a b c : V) : Coefficients :=
  -(triple (K v a) (K u b) (K v c) + triple (K v a) (K u c) (K v b))

/-- Two endpoint-paired terms, with the extra factor64 on quadratic products. -/
def paired (K : V → V → KernelCoefficients) (u v a b : V) : Coefficients :=
  -(scale 64 (pair (K u a) (K v b)) + triple (K u v) (K u a) (K v b) +
    scale 64 (pair (K u b) (K v a)) + triple (K u v) (K u b) (K v a))

/-- The literal four-term crossed coefficient. -/
def crossed (K : V → V → KernelCoefficients) (u v a b : V) : Coefficients :=
  scale 64 (pair (K v a) (K u b)-pair (K u a) (K u b)-pair (K v a) (K v b)) +
    scale 3 (triple (K u v) (K u a) (K v b))

/-- Reorienting a matching permutes its eight literal source representatives. -/
theorem direct_orientation (K : V → V → KernelCoefficients) (u v : V)
    (s : Fin 4 → V) (i : Fin 8) :
    direct K u v (orientations s i)=direct K u v s := by
  fin_cases i <;> simp [direct,orientations,Fin.sum_univ_succ] <;> abel

/-- Disjoint bonds vanish without expanding any polynomial coefficients. -/
theorem direct_disjoint (K : V → V → KernelCoefficients) (u v : V) (s : Fin 4 → V)
    (hu : ∀ i,u≠s i) (hv : ∀ i,v≠s i) : direct K u v s=0 := by
  simp [direct,ordered,orientations,Fin.sum_univ_succ,hu,hv]

theorem direct_left_only (K : V → V → KernelCoefficients) (u v b c d : V)
    (hs : Function.Injective (![u,b,c,d] : Fin 4 → V))
    (hv : ∀ i : Fin 4,v≠(![u,b,c,d] : Fin 4 → V) i) :
    direct K u v ![u,b,c,d]=leftOnly K u v b c d := by
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
  simp [direct,ordered,orientations,Fin.sum_univ_succ,
    leftOnly,rightOnly,paired,crossed,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm,
    hv0,hv1,hv2,hv3,hv0.symm,hv1.symm,hv2.symm,hv3.symm]
  abel


theorem direct_right_only (K : V → V → KernelCoefficients) (u v b c d : V)
    (hs : Function.Injective (![v,b,c,d] : Fin 4 → V))
    (hu : ∀ i : Fin 4,u≠(![v,b,c,d] : Fin 4 → V) i) :
    direct K u v ![v,b,c,d]=rightOnly K u v b c d := by
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
  simp [direct,ordered,orientations,Fin.sum_univ_succ,
    leftOnly,rightOnly,paired,crossed,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm,
    hu0,hu1,hu2,hu3,hu0.symm,hu1.symm,hu2.symm,hu3.symm]
  abel


theorem direct_paired (K : V → V → KernelCoefficients) (u v a b : V)
    (hs : Function.Injective (![u,v,a,b] : Fin 4 → V)) :
    direct K u v ![u,v,a,b]=paired K u v a b := by
  have h01 : u ≠ v := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : u ≠ a := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : u ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : v ≠ a := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : v ≠ b := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : a ≠ b := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  simp [direct,ordered,orientations,Fin.sum_univ_succ,
    leftOnly,rightOnly,paired,crossed,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm]
  abel


theorem direct_crossed (K : V → V → KernelCoefficients) (u v a b : V)
    (hs : Function.Injective (![u,a,v,b] : Fin 4 → V)) :
    direct K u v ![u,a,v,b]=crossed K u v a b := by
  have h01 : u ≠ a := hs.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 : u ≠ v := hs.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 : u ≠ b := hs.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 : a ≠ v := hs.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 : a ≠ b := hs.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : v ≠ b := hs.ne (by decide : (2 : Fin 4) ≠ 3)
  simp [direct,ordered,orientations,Fin.sum_univ_succ,
    leftOnly,rightOnly,paired,crossed,h01,h02,h03,h12,h13,h23,
    h01.symm,h02.symm,h03.symm,h12.symm,h13.symm,h23.symm]

/-- Once the left endpoint is first, only three partner tests remain. -/
def atLeft (K : V → V → KernelCoefficients) (u v a b c : V) : Coefficients :=
  if v=a then paired K u v b c else
  if v=b then crossed K u v a c else
  if v=c then crossed K u v a b else leftOnly K u v a b c

theorem direct_atLeft (K : V → V → KernelCoefficients) (u v a b c : V)
    (hs : Function.Injective (![u,a,b,c] : Fin 4 → V)) (hne : u≠v) :
    direct K u v ![u,a,b,c]=atLeft K u v a b c := by
  by_cases ha : v=a
  · subst v
    simpa [atLeft] using direct_paired K u a b c hs
  by_cases hb : v=b
  · subst v
    simpa [atLeft,ha] using direct_crossed K u b a c hs
  by_cases hc : v=c
  · subst v
    have hi := orientation_tuple_injective (![u,a,b,c] : Fin 4 → V) hs 2
    have hd := direct_orientation K u c (![u,a,b,c] : Fin 4 → V) 2
    simp [orientations] at hi hd
    rw [←hd,direct_crossed K u c a b hi]
    simp [atLeft,ha,hb]
  · have hv : ∀ i : Fin 4,v≠(![u,a,b,c] : Fin 4 → V) i := by
      intro i; fin_cases i <;> simp [hne.symm,ha,hb,hc]
    simpa [atLeft,ha,hb,hc] using direct_left_only K u v a b c hs hv

/-- The exact fast local coefficient. A diagonal bond conservatively falls back
to the original definition; actual forward torus edges are never diagonal. -/
def fastDirect (K : V → V → KernelCoefficients) (u v : V) (s : Fin 4 → V) : Coefficients :=
  if u=v then direct K u v s else
  if u=s 0 then atLeft K u v (s 1) (s 2) (s 3) else
  if u=s 1 then atLeft K u v (s 0) (s 2) (s 3) else
  if u=s 2 then atLeft K u v (s 3) (s 0) (s 1) else
  if u=s 3 then atLeft K u v (s 2) (s 0) (s 1) else
  if v=s 0 then rightOnly K u v (s 1) (s 2) (s 3) else
  if v=s 1 then rightOnly K u v (s 0) (s 2) (s 3) else
  if v=s 2 then rightOnly K u v (s 3) (s 0) (s 1) else
  if v=s 3 then rightOnly K u v (s 2) (s 0) (s 1) else 0

private theorem tuple_eta (s : Fin 4 → V) : ![s 0,s 1,s 2,s 3]=s := by
  ext i; fin_cases i <;> rfl

theorem direct_left_oriented (K : V → V → KernelCoefficients) (v : V)
    (s : Fin 4 → V) (hs : Function.Injective s) (i : Fin 8)
    (hne : orientations s i 0≠v) :
    direct K (orientations s i 0) v s =
      atLeft K (orientations s i 0) v (orientations s i 1) (orientations s i 2) (orientations s i 3) := by
  have hi : Function.Injective
      (![orientations s i 0,orientations s i 1,orientations s i 2,orientations s i 3] : Fin 4 → V) := by
    rw [tuple_eta]
    exact orientation_tuple_injective s hs i
  rw [←direct_orientation K (orientations s i 0) v s i]
  have hh := direct_atLeft K (orientations s i 0) v (orientations s i 1)
    (orientations s i 2) (orientations s i 3) hi hne
  simpa only [tuple_eta] using hh

theorem direct_right_oriented (K : V → V → KernelCoefficients) (u : V)
    (s : Fin 4 → V) (hs : Function.Injective s) (i : Fin 8) (hu : ∀ j,u≠s j) :
    direct K u (orientations s i 0) s =
      rightOnly K u (orientations s i 0) (orientations s i 1) (orientations s i 2) (orientations s i 3) := by
  have hi : Function.Injective
      (![orientations s i 0,orientations s i 1,orientations s i 2,orientations s i 3] : Fin 4 → V) := by
    rw [tuple_eta]
    exact orientation_tuple_injective s hs i
  have ho : ∀ j,u≠orientations s i j := by
    fin_cases i <;> intro j <;> fin_cases j <;> simp [orientations,hu]
  have hu' : ∀ j : Fin 4,u≠(![orientations s i 0,orientations s i 1,
      orientations s i 2,orientations s i 3] : Fin 4 → V) j := by simpa only [tuple_eta] using ho
  rw [←direct_orientation K u (orientations s i 0) s i]
  have hh := direct_right_only K u (orientations s i 0) (orientations s i 1)
    (orientations s i 2) (orientations s i 3) hi hu'
  simpa only [tuple_eta] using hh

/-- The optimized signed-array formula is exactly the frozen actual eight-orientation sum. -/
theorem fastDirect_eq_direct (K : V → V → KernelCoefficients) (u v : V)
    (s : Fin 4 → V) (hs : Function.Injective s) : fastDirect K u v s=direct K u v s := by
  by_cases hne : u=v
  · simp [fastDirect,hne]
  by_cases h0 : u=s 0
  · subst u
    simpa [fastDirect,hne,orientations] using (direct_left_oriented K v s hs 0 hne).symm
  by_cases h1 : u=s 1
  · subst u
    simpa [fastDirect,hne,h0,orientations] using (direct_left_oriented K v s hs 1 hne).symm
  by_cases h2 : u=s 2
  · subst u
    simpa [fastDirect,hne,h0,h1,orientations] using (direct_left_oriented K v s hs 4 hne).symm
  by_cases h3 : u=s 3
  · subst u
    simpa [fastDirect,hne,h0,h1,h2,orientations] using (direct_left_oriented K v s hs 5 hne).symm
  have hu : ∀ i,u≠s i := by intro i; fin_cases i <;> assumption
  by_cases k0 : v=s 0
  · subst v
    simpa [fastDirect,hne,h0,h1,h2,h3,orientations] using (direct_right_oriented K u s hs 0 hu).symm
  by_cases k1 : v=s 1
  · subst v
    simpa [fastDirect,hne,h0,h1,h2,h3,k0,orientations] using (direct_right_oriented K u s hs 1 hu).symm
  by_cases k2 : v=s 2
  · subst v
    simpa [fastDirect,hne,h0,h1,h2,h3,k0,k1,orientations] using (direct_right_oriented K u s hs 4 hu).symm
  by_cases k3 : v=s 3
  · subst v
    simpa [fastDirect,hne,h0,h1,h2,h3,k0,k1,k2,orientations] using (direct_right_oriented K u s hs 5 hu).symm
  have hv : ∀ i,v≠s i := by intro i; fin_cases i <;> assumption
  simp [fastDirect,hne,h0,h1,h2,h3,k0,k1,k2,k3,direct_disjoint K u v s hu hv]

/-- The optimized full forward-edge array, retaining the exact incident-source set. -/
def fastForward (K : V → V → KernelCoefficients) (ex ey : V ≃ V) (s : Fin 4 → V) : Coefficients :=
  (∑ u∈QuarticDirectCoefficient.incidentSources ex s,fastDirect K u (ex u) s)+
    ∑ u∈QuarticDirectCoefficient.incidentSources ey s,fastDirect K u (ey u) s

theorem fastForward_eq_forward (K : V → V → KernelCoefficients) (ex ey : V ≃ V)
    (s : Fin 4 → V) (hs : Function.Injective s) : fastForward K ex ey s=forward K ex ey s := by
  simp only [fastForward,forward,fastDirect_eq_direct K _ _ s hs]

end BilayerDressed.QuarticIntegerLocalCases
