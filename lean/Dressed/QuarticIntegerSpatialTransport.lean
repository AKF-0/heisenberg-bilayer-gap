import Dressed.QuarticIntegerBondReversal

/-! Signed-array spatial transport. Reflections reverse an actual forward
family and therefore use `inverse_direction_sum`, not forward commutation.
Axis interchange is a self-map only of `Torus.Vertex n n`. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerSpatialTransport
open QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerLocalCases
open QuarticIntegerTransport QuarticIntegerBondReversal QuarticCoefficientFibers
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V]

def PreservesForward (K : V → V → KernelCoefficients) (ex ey e : V ≃ V) : Prop :=
  ∀ s : Fin 4 → V, Function.Injective s → forward K ex ey (fun j => e (s j)) = forward K ex ey s

theorem preserves_refl (K : V → V → KernelCoefficients) (ex ey : V ≃ V) :
    PreservesForward K ex ey (Equiv.refl V) := by intro s hs; rfl

theorem preserves_trans (K : V → V → KernelCoefficients) (ex ey e f : V ≃ V)
    (he : PreservesForward K ex ey e) (hf : PreservesForward K ex ey f) :
    PreservesForward K ex ey (e.trans f) := by
  intro s hs
  exact (hf (fun j => e (s j)) (e.injective.comp hs)).trans (he s hs)

theorem direction_sum_equiv_to (K : V → V → KernelCoefficients) (ex target e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (target u)) (hK : ∀ u v, K (e u) (e v) = K u v)
    (s : Fin 4 → V) :
    (∑ u, direct K u (ex u) (fun j => e (s j))) = ∑ u, direct K u (target u) s := by
  calc
    _ = ∑ u, direct K (e u) (ex (e u)) (fun j => e (s j)) :=
      (e.sum_comp (fun u => direct K u (ex u) (fun j => e (s j)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [hx u]
      exact direct_equiv K e hK u (target u) s

theorem direction_sum_equiv_inverse (K : V → V → KernelCoefficients)
    (hsym : ∀ u v, K u v = K v u) (ex e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex.symm u)) (hK : ∀ u v, K (e u) (e v) = K u v)
    (s : Fin 4 → V) (hs : Function.Injective s) :
    (∑ u, direct K u (ex u) (fun j => e (s j))) = ∑ u, direct K u (ex u) s := by
  rw [direction_sum_equiv_to K ex ex.symm e hx hK, inverse_direction_sum K hsym ex s hs]

theorem preserves_reverse_first (K : V → V → KernelCoefficients)
    (hsym : ∀ u v, K u v = K v u) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex.symm u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ u v, K (e u) (e v) = K u v) : PreservesForward K ex ey e := by
  intro s hs
  rw [forward_eq_sum, forward_eq_sum, direction_sum_equiv_inverse K hsym ex e hx hK s hs,
    direction_sum_equiv K ey e hy hK]

theorem preserves_reverse_second (K : V → V → KernelCoefficients)
    (hsym : ∀ u v, K u v = K v u) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey.symm u))
    (hK : ∀ u v, K (e u) (e v) = K u v) : PreservesForward K ex ey e := by
  intro s hs
  rw [forward_eq_sum, forward_eq_sum, direction_sum_equiv K ex e hx hK,
    direction_sum_equiv_inverse K hsym ey e hy hK s hs]

theorem preserves_exchange (K : V → V → KernelCoefficients) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ey u)) (hy : ∀ u, ey (e u) = e (ex u))
    (hK : ∀ u v, K (e u) (e v) = K u v) : PreservesForward K ex ey e := by
  intro s hs
  rw [forward_eq_sum, forward_eq_sum, direction_sum_equiv_to K ex ey e hx hK,
    direction_sum_equiv_to K ey ex e hy hK, add_comm]

section Torus
open BilayerGap CubicSeedChecks
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def reflectX : Torus.Vertex n m ≃ Torus.Vertex n m where
  toFun u := (-u.1,u.2)
  invFun u := (-u.1,u.2)
  left_inv := by intro u; simp
  right_inv := by intro u; simp

def reflectY : Torus.Vertex n m ≃ Torus.Vertex n m where
  toFun u := (u.1,-u.2)
  invFun u := (u.1,-u.2)
  left_inv := by intro u; simp
  right_inv := by intro u; simp

/-- Swap is defined only on a square torus, so unequal coordinate periods cannot be conflated. -/
def swapAxes (n : ℕ) : Torus.Vertex n n ≃ Torus.Vertex n n := Equiv.prodComm _ _

private theorem rotate_apply {q : ℕ} [NeZero q] (u : Fin q) : finRotate q u = u+1 := by
  cases q with
  | zero => exact Fin.elim0 u
  | succ q => exact finRotate_succ_apply u

theorem reflectX_reverse (u : Torus.Vertex n m) :
    Torus.xNext n m (reflectX n m u) = reflectX n m ((Torus.xNext n m).symm u) := by
  have hh (v : Torus.Vertex n m) :
      Torus.xNext n m (reflectX n m (Torus.xNext n m v)) = reflectX n m v := by
    apply Prod.ext <;> simp [Torus.xNext, reflectX, rotate_apply] <;> abel
  simpa using hh ((Torus.xNext n m).symm u)

theorem reflectX_commute (u : Torus.Vertex n m) :
    Torus.yNext n m (reflectX n m u) = reflectX n m (Torus.yNext n m u) := rfl

theorem reflectY_commute (u : Torus.Vertex n m) :
    Torus.xNext n m (reflectY n m u) = reflectY n m (Torus.xNext n m u) := rfl

theorem reflectY_reverse (u : Torus.Vertex n m) :
    Torus.yNext n m (reflectY n m u) = reflectY n m ((Torus.yNext n m).symm u) := by
  have hh (v : Torus.Vertex n m) :
      Torus.yNext n m (reflectY n m (Torus.yNext n m v)) = reflectY n m v := by
    apply Prod.ext <;> simp [Torus.yNext, reflectY, rotate_apply] <;> abel
  simpa using hh ((Torus.yNext n m).symm u)

theorem swapAxes_x (u : Torus.Vertex n n) :
    Torus.xNext n n (swapAxes n u) = swapAxes n (Torus.yNext n n u) := rfl

theorem swapAxes_y (u : Torus.Vertex n n) :
    Torus.yNext n n (swapAxes n u) = swapAxes n (Torus.xNext n n u) := rfl

theorem reflectX_sub (u v : Torus.Vertex n m) :
    reflectX n m (v-u) = reflectX n m v-reflectX n m u := by
  apply Prod.ext <;> simp [reflectX] <;> abel

theorem reflectY_sub (u v : Torus.Vertex n m) :
    reflectY n m (v-u) = reflectY n m v-reflectY n m u := by
  apply Prod.ext <;> simp [reflectY] <;> abel

theorem swapAxes_sub (u v : Torus.Vertex n n) :
    swapAxes n (v-u) = swapAxes n v-swapAxes n u := rfl

def rectangularMap : Fin 4 → (Torus.Vertex n m ≃ Torus.Vertex n m) :=
  ![Equiv.refl _, reflectX n m, reflectY n m, (reflectX n m).trans (reflectY n m)]

def squareMap (n : ℕ) [NeZero (2*n)] : Fin 8 → (Torus.Vertex n n ≃ Torus.Vertex n n) :=
  ![Equiv.refl _, reflectX n n, reflectY n n, (reflectX n n).trans (reflectY n n),
    swapAxes n, (swapAxes n).trans (reflectX n n), (swapAxes n).trans (reflectY n n),
    ((swapAxes n).trans (reflectX n n)).trans (reflectY n n)]

theorem rectangularMap_preserves (K : Torus.Vertex n m → Torus.Vertex n m → KernelCoefficients)
    (hsym : ∀ u v, K u v = K v u)
    (hX : ∀ u v, K (reflectX n m u) (reflectX n m v) = K u v)
    (hY : ∀ u v, K (reflectY n m u) (reflectY n m v) = K u v) (code : Fin 4) :
    PreservesForward K (Torus.xNext n m) (Torus.yNext n m) (rectangularMap n m code) := by
  have hx := preserves_reverse_first K hsym (Torus.xNext n m) (Torus.yNext n m)
    (reflectX n m) (reflectX_reverse n m) (reflectX_commute n m) hX
  have hy := preserves_reverse_second K hsym (Torus.xNext n m) (Torus.yNext n m)
    (reflectY n m) (reflectY_commute n m) (reflectY_reverse n m) hY
  fin_cases code
  · exact preserves_refl K _ _
  · exact hx
  · exact hy
  · exact preserves_trans K _ _ _ _ hx hy

theorem squareMap_preserves (K : Torus.Vertex n n → Torus.Vertex n n → KernelCoefficients)
    (hsym : ∀ u v, K u v = K v u)
    (hX : ∀ u v, K (reflectX n n u) (reflectX n n v) = K u v)
    (hY : ∀ u v, K (reflectY n n u) (reflectY n n v) = K u v)
    (hS : ∀ u v, K (swapAxes n u) (swapAxes n v) = K u v) (code : Fin 8) :
    PreservesForward K (Torus.xNext n n) (Torus.yNext n n) (squareMap n code) := by
  have hx := rectangularMap_preserves n n K hsym hX hY 1
  have hy := rectangularMap_preserves n n K hsym hX hY 2
  have hxy := preserves_trans K _ _ _ _ hx hy
  have hs := preserves_exchange K (Torus.xNext n n) (Torus.yNext n n) (swapAxes n)
    (swapAxes_x n) (swapAxes_y n) hS
  fin_cases code
  · exact preserves_refl K _ _
  · exact hx
  · exact hy
  · exact hxy
  · exact hs
  · exact preserves_trans K _ _ _ _ hs hx
  · exact preserves_trans K _ _ _ _ hs hy
  · exact preserves_trans K _ _ _ _ (preserves_trans K _ _ _ _ hs hx) hy

/-- Exact spatial+shift+matching witness, retaining the complete ordered tuple. -/
theorem forward_eq_of_spatial_witness
    (K : Torus.Vertex n m → Torus.Vertex n m → KernelCoefficients)
    (e : Torus.Vertex n m ≃ Torus.Vertex n m)
    (he : PreservesForward K (Torus.xNext n m) (Torus.yNext n m) e)
    (s : Fin 4 → Torus.Vertex n m) (hs : Function.Injective s)
    (shift : Torus.Vertex n m) (i : Fin 8) (s' : Fin 4 → Torus.Vertex n m)
    (hShift : ∀ u v, K (u+shift) (v+shift) = K u v)
    (hw : s' = orientations (fun j => e (s j)+shift) i) :
    forward K (Torus.xNext n m) (Torus.yNext n m) s' =
      forward K (Torus.xNext n m) (Torus.yNext n m) s :=
  (forward_eq_of_translation_orientation n m K (fun j => e (s j)) shift i s' hShift hw).trans (he s hs)

theorem fastForward_eq_of_spatial_witness
    (K : Torus.Vertex n m → Torus.Vertex n m → KernelCoefficients)
    (e : Torus.Vertex n m ≃ Torus.Vertex n m)
    (he : PreservesForward K (Torus.xNext n m) (Torus.yNext n m) e)
    (s : Fin 4 → Torus.Vertex n m) (hs : Function.Injective s)
    (shift : Torus.Vertex n m) (i : Fin 8) (s' : Fin 4 → Torus.Vertex n m)
    (hShift : ∀ u v, K (u+shift) (v+shift) = K u v)
    (hw : s' = orientations (fun j => e (s j)+shift) i) :
    fastForward K (Torus.xNext n m) (Torus.yNext n m) s' =
      fastForward K (Torus.xNext n m) (Torus.yNext n m) s := by
  have hs' : Function.Injective s' := by
    rw [hw]
    exact orientation_tuple_injective _ ((Equiv.addRight shift).injective.comp (e.injective.comp hs)) i
  rw [fastForward_eq_forward _ _ _ _ hs', fastForward_eq_forward _ _ _ _ hs]
  exact forward_eq_of_spatial_witness n m K e he s hs shift i s' hShift hw

end Torus
end BilayerDressed.QuarticIntegerSpatialTransport
