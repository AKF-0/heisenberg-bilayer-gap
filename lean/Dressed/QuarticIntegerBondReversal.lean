import Dressed.QuarticIntegerTransport

/-! Exact reversal of ordered quartic bonds. Symmetry of the kernel is used only
where the literal K_uv factor changes to K_vu. The result preserves the entire
signed coefficient array, and is not an assertion about absolute values. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerBondReversal
open QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerLocalCases
open QuarticIntegerTransport QuarticCoefficientFibers
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
variable {V : Type*}

theorem left_right_reversal (K : V → V → KernelCoefficients) (u v a b c : V) :
    leftOnly K u v a b c = rightOnly K v u a b c := by
  ext i
  fin_cases i <;> dsimp [leftOnly, rightOnly, triple] <;> ring

theorem paired_reversal (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v a b : V) :
    paired K u v a b = paired K v u a b := by
  unfold paired
  rw [hK v u]
  ext i
  fin_cases i <;> dsimp [scale, pair, triple] <;> ring

theorem crossed_reversal (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v a b : V) :
    crossed K u v a b = crossed K v u b a := by
  unfold crossed
  rw [hK v u]
  ext i
  fin_cases i <;> dsimp [scale, pair, triple] <;> ring

variable [Fintype V] [DecidableEq V]

theorem direct_reversal_left (K : V → V → KernelCoefficients) (u v a b c : V)
    (hs : Function.Injective (![u,a,b,c] : Fin 4 → V))
    (hv : ∀ i : Fin 4, v ≠ (![u,a,b,c] : Fin 4 → V) i) :
    direct K u v ![u,a,b,c] = direct K v u ![u,a,b,c] := by
  rw [direct_left_only K u v a b c hs hv, direct_right_only K v u a b c hs hv]
  exact left_right_reversal K u v a b c

theorem direct_reversal_paired (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v a b : V)
    (hs : Function.Injective (![u,v,a,b] : Fin 4 → V)) :
    direct K u v ![u,v,a,b] = direct K v u ![u,v,a,b] := by
  have hi := orientation_tuple_injective (![u,v,a,b] : Fin 4 → V) hs 1
  have hd := direct_orientation K v u (![u,v,a,b] : Fin 4 → V) 1
  simp [orientations] at hi hd
  rw [direct_paired K u v a b hs, ←hd, direct_paired K v u a b hi]
  exact paired_reversal K hK u v a b

theorem direct_reversal_crossed (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v a b : V)
    (hs : Function.Injective (![u,a,v,b] : Fin 4 → V)) :
    direct K u v ![u,a,v,b] = direct K v u ![u,a,v,b] := by
  have hi := orientation_tuple_injective (![u,a,v,b] : Fin 4 → V) hs 4
  have hd := direct_orientation K v u (![u,a,v,b] : Fin 4 → V) 4
  simp [orientations] at hi hd
  rw [direct_crossed K u v a b hs, ←hd, direct_crossed K v u b a hi]
  exact crossed_reversal K hK u v a b

theorem direct_reversal_at_first (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v a b c : V)
    (hs : Function.Injective (![u,a,b,c] : Fin 4 → V)) :
    direct K u v ![u,a,b,c] = direct K v u ![u,a,b,c] := by
  by_cases h0 : v=u
  · subst v; rfl
  by_cases h1 : v=a
  · subst v; exact direct_reversal_paired K hK u a b c hs
  by_cases h2 : v=b
  · subst v; exact direct_reversal_crossed K hK u b a c hs
  by_cases h3 : v=c
  · subst v
    have hi := orientation_tuple_injective (![u,a,b,c] : Fin 4 → V) hs 2
    have hd := direct_orientation K u c (![u,a,b,c] : Fin 4 → V) 2
    have he := direct_orientation K c u (![u,a,b,c] : Fin 4 → V) 2
    simp [orientations] at hi hd he
    rw [←hd, ←he]
    exact direct_reversal_crossed K hK u c a b hi
  · apply direct_reversal_left K u v a b c hs
    intro i; fin_cases i <;> simp [h0,h1,h2,h3]

private theorem tuple_eta (s : Fin 4 → V) : ![s 0,s 1,s 2,s 3] = s := by
  ext i; fin_cases i <;> rfl

theorem direct_reversal_oriented (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (s : Fin 4 → V) (hs : Function.Injective s)
    (i : Fin 8) (v : V) :
    direct K (orientations s i 0) v s = direct K v (orientations s i 0) s := by
  have hi : Function.Injective
      (![orientations s i 0,orientations s i 1,orientations s i 2,orientations s i 3] : Fin 4 → V) := by
    rw [tuple_eta]
    exact orientation_tuple_injective s hs i
  have hh := direct_reversal_at_first K hK (orientations s i 0) v
    (orientations s i 1) (orientations s i 2) (orientations s i 3) hi
  simpa only [tuple_eta, direct_orientation] using hh

theorem direct_reversal_at_site (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (s : Fin 4 → V) (hs : Function.Injective s)
    (j : Fin 4) (v : V) : direct K (s j) v s = direct K v (s j) s := by
  fin_cases j
  · simpa [orientations] using direct_reversal_oriented K hK s hs 0 v
  · simpa [orientations] using direct_reversal_oriented K hK s hs 1 v
  · simpa [orientations] using direct_reversal_oriented K hK s hs 4 v
  · simpa [orientations] using direct_reversal_oriented K hK s hs 5 v

/-- Actual signed coefficient reversal on any injective matching tuple. -/
theorem direct_reversal (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (u v : V) (s : Fin 4 → V) (hs : Function.Injective s) :
    direct K u v s = direct K v u s := by
  by_cases hu : ∃ i, u = s i
  · obtain ⟨i,rfl⟩ := hu
    exact direct_reversal_at_site K hK s hs i v
  by_cases hv : ∃ i, v = s i
  · obtain ⟨i,rfl⟩ := hv
    exact (direct_reversal_at_site K hK s hs i u).symm
  have hu' : ∀ i, u ≠ s i := fun i hi => hu ⟨i,hi⟩
  have hv' : ∀ i, v ≠ s i := fun i hi => hv ⟨i,hi⟩
  rw [direct_disjoint K u v s hu' hv', direct_disjoint K v u s hv' hu']

/-- Inverse-forward bonds become forward bonds only after exact signed reversal. -/
theorem inverse_direction_sum (K : V → V → KernelCoefficients)
    (hK : ∀ u v, K u v = K v u) (ex : V ≃ V) (s : Fin 4 → V) (hs : Function.Injective s) :
    (∑ u, direct K u (ex.symm u) s) = ∑ u, direct K u (ex u) s := by
  calc
    _ = ∑ u, direct K (ex u) (ex.symm (ex u)) s :=
      (ex.sum_comp (fun u => direct K u (ex.symm u) s)).symm
    _ = _ := by
      simp only [Equiv.symm_apply_apply]
      apply Finset.sum_congr rfl
      intro u _
      exact direct_reversal K hK (ex u) u s hs

end BilayerDressed.QuarticIntegerBondReversal
