import Dressed.QuarticIntegerLocalCases

/-!
# Exact signed integer-array transport for quartic matching coefficients

Transport follows a genuine site equivalence, the actual ordered forward bonds,
and one of the eight matching-preserving tuple orientations. The result is an
identity of all eleven signed integer coefficients. No sampled evaluation,
absolute value, orbit size, reflection, or representative-minimality assertion
is used. Explicit tuple witnesses can therefore justify reuse while retaining
every original table row.
-/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerTransport
open QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerLocalCases
open QuarticCoefficientFibers QuarticDirectCoefficient
set_option maxHeartbeats 1000000
variable {V W : Type*}

/-- Every literal matching orientation commutes with a site map. -/
theorem orientations_map (f : V → W) (s : Fin 4 → V) (i : Fin 8) (j : Fin 4) :
    orientations (fun k => f (s k)) i j = f (orientations s i j) := by
  fin_cases i <;> fin_cases j <;> rfl

variable [DecidableEq V]

/-- Site covariance preserves the four guarded, signed, integer-array sources. -/
theorem ordered_equiv (K : V → V → KernelCoefficients) (e : V ≃ V)
    (hK : ∀ u v, K (e u) (e v) = K u v) (u v a b c d : V) :
    ordered K (e u) (e v) (e a) (e b) (e c) (e d) = ordered K u v a b c d := by
  simp only [ordered, ne_eq, e.injective.eq_iff, hK]

theorem direct_equiv (K : V → V → KernelCoefficients) (e : V ≃ V)
    (hK : ∀ u v, K (e u) (e v) = K u v) (u v : V) (s : Fin 4 → V) :
    direct K (e u) (e v) (fun i => e (s i)) = direct K u v s := by
  unfold direct
  apply Finset.sum_congr rfl
  intro i _
  simp only [orientations_map, ordered_equiv K e hK]

/-- The exact incident-source reduction also holds before any polynomial evaluation. -/
theorem sum_direct_eq_incident [Fintype V] (K : V → V → KernelCoefficients)
    (ex : V ≃ V) (s : Fin 4 → V) :
    (∑ u, direct K u (ex u) s) = ∑ u ∈ incidentSources ex s, direct K u (ex u) s := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  apply direct_disjoint
  · intro i hi
    apply hu
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  · intro i hi
    apply hu
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa using congrArg ex.symm hi.symm

theorem forward_eq_sum [Fintype V] (K : V → V → KernelCoefficients)
    (ex ey : V ≃ V) (s : Fin 4 → V) :
    forward K ex ey s = (∑ u, direct K u (ex u) s) + ∑ u, direct K u (ey u) s := by
  simp only [forward, sum_direct_eq_incident]

theorem direction_sum_equiv [Fintype V] (K : V → V → KernelCoefficients) (ex e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hK : ∀ u v, K (e u) (e v) = K u v)
    (s : Fin 4 → V) :
    (∑ u, direct K u (ex u) (fun i => e (s i))) = ∑ u, direct K u (ex u) s := by
  calc
    _ = ∑ u, direct K (e u) (ex (e u)) (fun i => e (s i)) :=
      (e.sum_comp (fun u => direct K u (ex u) (fun i => e (s i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [hx u]
      exact direct_equiv K e hK u (ex u) s

/-- Both actual ordered forward families are transported without changing signs. -/
theorem forward_equiv [Fintype V] (K : V → V → KernelCoefficients) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ u v, K (e u) (e v) = K u v) (s : Fin 4 → V) :
    forward K ex ey (fun i => e (s i)) = forward K ex ey s := by
  rw [forward_eq_sum, forward_eq_sum, direction_sum_equiv K ex e hx hK,
    direction_sum_equiv K ey e hy hK]

/-- Reorientation changes no signed coefficient and needs no injectivity premise. -/
theorem forward_orientation [Fintype V] (K : V → V → KernelCoefficients)
    (ex ey : V ≃ V) (s : Fin 4 → V) (i : Fin 8) :
    forward K ex ey (orientations s i) = forward K ex ey s := by
  simp only [forward_eq_sum, direct_orientation]

/-- A concrete tuple equality is sufficient to authorize exact coefficient reuse. -/
theorem forward_eq_of_equiv_orientation [Fintype V]
    (K : V → V → KernelCoefficients) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ u v, K (e u) (e v) = K u v) (s s' : Fin 4 → V) (i : Fin 8)
    (heq : s' = orientations (fun j => e (s j)) i) :
    forward K ex ey s' = forward K ex ey s := by
  rw [heq, forward_orientation, forward_equiv K ex ey e hx hy hK]

/-- The same exact reuse identity is available directly for the optimized arrays. -/
theorem fastForward_eq_of_equiv_orientation [Fintype V]
    (K : V → V → KernelCoefficients) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ u v, K (e u) (e v) = K u v) (s s' : Fin 4 → V) (i : Fin 8)
    (hs : Function.Injective s) (heq : s' = orientations (fun j => e (s j)) i) :
    fastForward K ex ey s' = fastForward K ex ey s := by
  have hs' : Function.Injective s' := by
    rw [heq]
    exact orientation_tuple_injective _ (e.injective.comp hs) i
  rw [fastForward_eq_forward K ex ey s' hs', fastForward_eq_forward K ex ey s hs]
  exact forward_eq_of_equiv_orientation K ex ey e hx hy hK s s' i heq

section Torus
open BilayerGap CubicSeedChecks
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- Actual graph-walk integer coefficients, not equality at selected couplings. -/
theorem kernel_translation (u v t : Torus.Vertex n m) :
    kernel n m (u+t) (v+t) = kernel n m u v := by
  simp only [kernel, adjacency_translate n m u v t, offWalk2_translate n m u v t,
    walk3_translate n m u v t]

theorem coefficients_translation (s : Fin 4 → Torus.Vertex n m) (t : Torus.Vertex n m) :
    coefficients n m (fun j => s j+t) = coefficients n m s :=
  forward_equiv (kernel n m) (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight t)
    (fun u => xNext_add n m u t) (fun u => yNext_add n m u t)
    (fun u v => kernel_translation n m u v t) s

theorem coefficients_reroot (s : Fin 4 → Torus.Vertex n m) (t : Torus.Vertex n m) :
    coefficients n m (fun j => s j-t) = coefficients n m s := by
  simpa only [sub_eq_add_neg] using coefficients_translation n m s (-t)

omit [NeZero (2*n)] [NeZero (2*m)] in
theorem coefficients_orientation (s : Fin 4 → Torus.Vertex n m) (i : Fin 8) :
    coefficients n m (orientations s i) = coefficients n m s :=
  forward_orientation (kernel n m) (Torus.xNext n m) (Torus.yNext n m) s i

/-- Additive-shift witness form, matching the emitted representative data directly. -/
theorem coefficients_eq_of_translation_orientation
    (s : Fin 4 → Torus.Vertex n m) (shift : Torus.Vertex n m) (i : Fin 8)
    (s' : Fin 4 → Torus.Vertex n m)
    (heq : s' = orientations (fun j => s j+shift) i) :
    coefficients n m s' = coefficients n m s := by
  rw [heq, coefficients_orientation, coefficients_translation]

/-- Generic additive-shift transport also applies to a proved displacement cache. -/
theorem forward_eq_of_translation_orientation
    (K : Torus.Vertex n m → Torus.Vertex n m → KernelCoefficients)
    (s : Fin 4 → Torus.Vertex n m) (shift : Torus.Vertex n m) (i : Fin 8)
    (s' : Fin 4 → Torus.Vertex n m)
    (hK : ∀ u v, K (u+shift) (v+shift) = K u v)
    (heq : s' = orientations (fun j => s j+shift) i) :
    forward K (Torus.xNext n m) (Torus.yNext n m) s' =
      forward K (Torus.xNext n m) (Torus.yNext n m) s :=
  forward_eq_of_equiv_orientation K (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight shift)
    (fun u => xNext_add n m u shift) (fun u => yNext_add n m u shift) hK s s' i heq

/-- Optimized-array version uses the same concrete shift/orientation tuple witness. -/
theorem fastForward_eq_of_translation_orientation
    (K : Torus.Vertex n m → Torus.Vertex n m → KernelCoefficients)
    (s : Fin 4 → Torus.Vertex n m) (shift : Torus.Vertex n m) (i : Fin 8)
    (s' : Fin 4 → Torus.Vertex n m)
    (hK : ∀ u v, K (u+shift) (v+shift) = K u v)
    (hs : Function.Injective s) (heq : s' = orientations (fun j => s j+shift) i) :
    fastForward K (Torus.xNext n m) (Torus.yNext n m) s' =
      fastForward K (Torus.xNext n m) (Torus.yNext n m) s :=
  fastForward_eq_of_equiv_orientation K (Torus.xNext n m) (Torus.yNext n m) (Equiv.addRight shift)
    (fun u => xNext_add n m u shift) (fun u => yNext_add n m u shift) hK s s' i hs heq

/-- The emitted translation/orientation witness, not representative minimality,
proves equality of every signed integer coefficient in a reused rooted row. -/
theorem coefficients_eq_of_reroot_orientation
    (s : Fin 4 → Torus.Vertex n m) (t : Torus.Vertex n m) (i : Fin 8)
    (s' : Fin 4 → Torus.Vertex n m)
    (heq : s' = orientations (fun j => s j-t) i) :
    coefficients n m s' = coefficients n m s := by
  rw [heq, coefficients_orientation, coefficients_reroot]

/-- Rooting specifically at any one of the four displayed sites is a specialization. -/
theorem coefficients_eq_of_site_reroot_orientation
    (s : Fin 4 → Torus.Vertex n m) (k : Fin 4) (i : Fin 8)
    (s' : Fin 4 → Torus.Vertex n m)
    (heq : s' = orientations (fun j => s j-s k) i) :
    coefficients n m s' = coefficients n m s :=
  coefficients_eq_of_reroot_orientation n m s (s k) i s' heq

end Torus
end BilayerDressed.QuarticIntegerTransport
