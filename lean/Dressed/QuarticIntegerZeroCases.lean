import Dressed.QuarticIntegerLocalCases

/-!
# Sound sparse-zero tests for the actual signed quartic coefficient arrays

The tests inspect only whether individual cubic-kernel arrays vanish. A true
result proves every monomial in the selected local expression vanishes. False
results make no assertion: cancellation and diagonal bonds remain on the ordinary
arithmetic path. In particular, this file does not omit any rooted support.
-/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerZeroCases
open QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerLocalCases
set_option maxHeartbeats 1000000

/-- Test all three signed coefficients, not a value at a sampled coupling. -/
def kernelCheck (a : KernelCoefficients) : Bool :=
  (a 0 == 0) && (a 1 == 0) && (a 2 == 0)

theorem kernel_zero_of_check (a : KernelCoefficients) (h : kernelCheck a = true) :
    a = 0 := by
  simp only [kernelCheck, Bool.and_eq_true, beq_iff_eq] at h
  ext i
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

@[simp] theorem pair_zero_left (a : KernelCoefficients) : pair 0 a = 0 := by
  ext i; fin_cases i <;> simp [pair]
@[simp] theorem pair_zero_right (a : KernelCoefficients) : pair a 0 = 0 := by
  ext i; fin_cases i <;> simp [pair]
@[simp] theorem triple_zero_left (a b : KernelCoefficients) : triple 0 a b = 0 := by
  ext i; fin_cases i <;> simp [triple]
@[simp] theorem triple_zero_middle (a b : KernelCoefficients) : triple a 0 b = 0 := by
  ext i; fin_cases i <;> simp [triple]
@[simp] theorem triple_zero_right (a b : KernelCoefficients) : triple a b 0 = 0 := by
  ext i; fin_cases i <;> simp [triple]
@[simp] theorem scale_zero (z : ℤ) : scale z 0 = 0 := by ext i; simp [scale]

def pairCheck (a b : KernelCoefficients) : Bool := kernelCheck a || kernelCheck b
def tripleCheck (a b c : KernelCoefficients) : Bool :=
  kernelCheck a || kernelCheck b || kernelCheck c

theorem pair_zero_of_check (a b : KernelCoefficients) (h : pairCheck a b = true) :
    pair a b = 0 := by
  simp only [pairCheck, Bool.or_eq_true] at h
  rcases h with h | h
  · simp [kernel_zero_of_check a h]
  · simp [kernel_zero_of_check b h]

theorem triple_zero_of_check (a b c : KernelCoefficients)
    (h : tripleCheck a b c = true) : triple a b c = 0 := by
  simp only [tripleCheck, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp [kernel_zero_of_check a h]
  · simp [kernel_zero_of_check b h]
  · simp [kernel_zero_of_check c h]

/-- A zero factor in the quadratic part also kills its extra-kernel cubic part. -/
theorem triple_zero_of_pair_check (a b c : KernelCoefficients)
    (h : pairCheck b c = true) : triple a b c = 0 := by
  simp only [pairCheck, Bool.or_eq_true] at h
  rcases h with h | h
  · simp [kernel_zero_of_check b h]
  · simp [kernel_zero_of_check c h]

variable {V : Type*}

def leftCheck (K : V → V → KernelCoefficients) (u v a b c : V) : Bool :=
  tripleCheck (K u a) (K u b) (K v c) && tripleCheck (K u a) (K u c) (K v b)
def rightCheck (K : V → V → KernelCoefficients) (u v a b c : V) : Bool :=
  tripleCheck (K v a) (K u b) (K v c) && tripleCheck (K v a) (K u c) (K v b)

/-- Checking each quadratic pair suffices for both corresponding cubic terms. -/
def pairedCheck (K : V → V → KernelCoefficients) (u v a b : V) : Bool :=
  pairCheck (K u a) (K v b) && pairCheck (K u b) (K v a)
def crossedCheck (K : V → V → KernelCoefficients) (u v a b : V) : Bool :=
  pairCheck (K v a) (K u b) && pairCheck (K u a) (K u b) &&
    pairCheck (K v a) (K v b) && tripleCheck (K u v) (K u a) (K v b)

theorem leftOnly_zero_of_check (K : V → V → KernelCoefficients) (u v a b c : V)
    (h : leftCheck K u v a b c = true) : leftOnly K u v a b c = 0 := by
  simp only [leftCheck, Bool.and_eq_true] at h
  simp [leftOnly, triple_zero_of_check _ _ _ h.1, triple_zero_of_check _ _ _ h.2]

theorem rightOnly_zero_of_check (K : V → V → KernelCoefficients) (u v a b c : V)
    (h : rightCheck K u v a b c = true) : rightOnly K u v a b c = 0 := by
  simp only [rightCheck, Bool.and_eq_true] at h
  simp [rightOnly, triple_zero_of_check _ _ _ h.1, triple_zero_of_check _ _ _ h.2]

theorem paired_zero_of_check (K : V → V → KernelCoefficients) (u v a b : V)
    (h : pairedCheck K u v a b = true) : paired K u v a b = 0 := by
  simp only [pairedCheck, Bool.and_eq_true] at h
  simp [paired, pair_zero_of_check _ _ h.1, pair_zero_of_check _ _ h.2,
    triple_zero_of_pair_check _ _ _ h.1, triple_zero_of_pair_check _ _ _ h.2]

theorem crossed_zero_of_check (K : V → V → KernelCoefficients) (u v a b : V)
    (h : crossedCheck K u v a b = true) : crossed K u v a b = 0 := by
  simp only [crossedCheck, Bool.and_eq_true] at h
  simp [crossed, pair_zero_of_check _ _ h.1.1.1, pair_zero_of_check _ _ h.1.1.2,
    pair_zero_of_check _ _ h.1.2, triple_zero_of_check _ _ _ h.2]

variable [DecidableEq V]

def atLeftCheck (K : V → V → KernelCoefficients) (u v a b c : V) : Bool :=
  if v=a then pairedCheck K u v b c else
  if v=b then crossedCheck K u v a c else
  if v=c then crossedCheck K u v a b else leftCheck K u v a b c

theorem atLeft_zero_of_check (K : V → V → KernelCoefficients) (u v a b c : V)
    (h : atLeftCheck K u v a b c = true) : atLeft K u v a b c = 0 := by
  unfold atLeftCheck atLeft at *
  split_ifs at h ⊢
  · exact paired_zero_of_check _ _ _ _ _ h
  · exact crossed_zero_of_check _ _ _ _ _ h
  · exact crossed_zero_of_check _ _ _ _ _ h
  · exact leftOnly_zero_of_check _ _ _ _ _ _ h

/-- Mirror the frozen endpoint dispatcher. Diagonal fallback is never asserted zero. -/
def directCheck (K : V → V → KernelCoefficients) (u v : V) (s : Fin 4 → V) : Bool :=
  if u=v then false else
  if u=s 0 then atLeftCheck K u v (s 1) (s 2) (s 3) else
  if u=s 1 then atLeftCheck K u v (s 0) (s 2) (s 3) else
  if u=s 2 then atLeftCheck K u v (s 3) (s 0) (s 1) else
  if u=s 3 then atLeftCheck K u v (s 2) (s 0) (s 1) else
  if v=s 0 then rightCheck K u v (s 1) (s 2) (s 3) else
  if v=s 1 then rightCheck K u v (s 0) (s 2) (s 3) else
  if v=s 2 then rightCheck K u v (s 3) (s 0) (s 1) else
  if v=s 3 then rightCheck K u v (s 2) (s 0) (s 1) else true

theorem fastDirect_zero_of_check (K : V → V → KernelCoefficients) (u v : V)
    (s : Fin 4 → V) (h : directCheck K u v s = true) : fastDirect K u v s = 0 := by
  unfold directCheck fastDirect at *
  split_ifs at h ⊢ <;> first
    | exact atLeft_zero_of_check _ _ _ _ _ _ h
    | exact rightOnly_zero_of_check _ _ _ _ _ _ h
    | contradiction
    | rfl

theorem direct_zero_of_check [Fintype V] (K : V → V → KernelCoefficients) (u v : V)
    (s : Fin 4 → V) (hs : Function.Injective s) (h : directCheck K u v s = true) :
    direct K u v s = 0 := by
  rw [←fastDirect_eq_direct K u v s hs]
  exact fastDirect_zero_of_check K u v s h

/-- Bounded decidable quantifiers inspect exactly the two incident-source sets,
not the full site type, and require only Boolean local checks. -/
def forwardCheck (K : V → V → KernelCoefficients) (ex ey : V ≃ V) (s : Fin 4 → V) : Bool :=
  decide (∀ u ∈ QuarticDirectCoefficient.incidentSources ex s, directCheck K u (ex u) s = true) &&
  decide (∀ u ∈ QuarticDirectCoefficient.incidentSources ey s, directCheck K u (ey u) s = true)

theorem fastForward_zero_of_check (K : V → V → KernelCoefficients) (ex ey : V ≃ V)
    (s : Fin 4 → V) (h : forwardCheck K ex ey s = true) : fastForward K ex ey s = 0 := by
  simp only [forwardCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hx : (∑ u∈QuarticDirectCoefficient.incidentSources ex s,fastDirect K u (ex u) s)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact fastDirect_zero_of_check K u (ex u) s (h.1 u hu)
  have hy : (∑ u∈QuarticDirectCoefficient.incidentSources ey s,fastDirect K u (ey u) s)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact fastDirect_zero_of_check K u (ey u) s (h.2 u hu)
  simp only [fastForward, hx, hy, add_zero]

theorem forward_zero_of_check [Fintype V] (K : V → V → KernelCoefficients) (ex ey : V ≃ V)
    (s : Fin 4 → V) (hs : Function.Injective s) (h : forwardCheck K ex ey s = true) :
    forward K ex ey s = 0 := by
  rw [←fastForward_eq_forward K ex ey s hs]
  exact fastForward_zero_of_check K ex ey s h

end BilayerDressed.QuarticIntegerZeroCases
