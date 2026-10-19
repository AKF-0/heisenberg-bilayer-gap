import Gap.ClusterProducts

/-!
# Four concrete perfect matchings of an even rectangular torus

The site set is genuinely `Fin (2*n) × Fin (2*m)`. The two horizontal
matchings pair even/odd and odd/next-even x coordinates; the two vertical
matchings do the same in y. Every matching is an explicit bijection from
cluster index and endpoint to sites. No graph-cover assumption is used.
-/
noncomputable section
namespace BilayerGap
namespace Torus

abbrev Vertex (n m : ℕ) := Fin (2*n) × Fin (2*m)
abbrev Config (n m : ℕ) := Vertex n m → Fin 4
abbrev PairCount (n m : ℕ) := 2*n*m

/-- Even/odd decomposition of a periodic coordinate. -/
def pairCoordinate (n : ℕ) : Fin n × Fin 2 ≃ Fin (2*n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

@[simp] theorem pairCoordinate_val (n : ℕ) (i : Fin n) (s : Fin 2) :
    (pairCoordinate n (i,s)).val = s.val + 2*i.val := rfl

def horizontalIndex (n m : ℕ) : Fin (PairCount n m) ≃ Fin n × Fin (2*m) :=
  (finCongr (by dsimp [PairCount]; ring)).trans finProdFinEquiv.symm

def verticalIndex (n m : ℕ) : Fin (PairCount n m) ≃ Fin (2*n) × Fin m :=
  finProdFinEquiv.symm

/-- Unshifted horizontal matching, with exact coordinate formulas. -/
def horizontalEven (n m : ℕ) : (Fin (PairCount n m) × Fin 2) ≃ Vertex n m where
  toFun p := (pairCoordinate n ((horizontalIndex n m p.1).1,p.2),
    (horizontalIndex n m p.1).2)
  invFun v := ((horizontalIndex n m).symm ((pairCoordinate n).symm v.1 |>.1,v.2),
    ((pairCoordinate n).symm v.1).2)
  left_inv := by intro p; simp
  right_inv := by intro v; simp

/-- Unshifted vertical matching. -/
def verticalEven (n m : ℕ) : (Fin (PairCount n m) × Fin 2) ≃ Vertex n m where
  toFun p := ((verticalIndex n m p.1).1,
    pairCoordinate m ((verticalIndex n m p.1).2,p.2))
  invFun v := ((verticalIndex n m).symm (v.1,((pairCoordinate m).symm v.2).1),
    ((pairCoordinate m).symm v.2).2)
  left_inv := by intro p; simp
  right_inv := by intro v; simp

/-- Periodic positive-neighbor permutations, including the wraparound edge. -/
def xNext (n m : ℕ) : Equiv.Perm (Vertex n m) :=
  Equiv.prodCongr (finRotate (2*n)) (Equiv.refl _)

def yNext (n m : ℕ) : Equiv.Perm (Vertex n m) :=
  Equiv.prodCongr (Equiv.refl _) (finRotate (2*m))

def horizontalOdd (n m : ℕ) := (horizontalEven n m).trans (xNext n m)
def verticalOdd (n m : ℕ) := (verticalEven n m).trans (yNext n m)

/-- The four matchings: horizontal even, horizontal odd, vertical even, vertical odd. -/
def matching (n m : ℕ) : Fin 4 → (Fin (PairCount n m) × Fin 2) ≃ Vertex n m :=
  ![horizontalEven n m, horizontalOdd n m, verticalEven n m, verticalOdd n m]

private theorem rotate_apply {q : ℕ} [NeZero q] (i : Fin q) : finRotate q i = i+1 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q => exact finRotate_succ_apply i

theorem pairCoordinate_next (n : ℕ) (i : Fin n) :
    pairCoordinate n (i,1) = finRotate (2*n) (pairCoordinate n (i,0)) := by
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  letI : NeZero (2*n) := ⟨Nat.mul_ne_zero (by decide) hn⟩
  rw [rotate_apply]
  apply Fin.ext
  have hi := i.isLt
  simp only [pairCoordinate_val, Fin.val_add]
  norm_num [Nat.mod_eq_of_lt (show 1 < 2*n by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem horizontalEven_next (n m : ℕ) (i : Fin (PairCount n m)) :
    horizontalEven n m (i,1) = xNext n m (horizontalEven n m (i,0)) := by
  change (pairCoordinate n ((horizontalIndex n m i).1,1), _) =
    (finRotate (2*n) (pairCoordinate n ((horizontalIndex n m i).1,0)), _)
  rw [pairCoordinate_next]
  rfl

theorem verticalEven_next (n m : ℕ) (i : Fin (PairCount n m)) :
    verticalEven n m (i,1) = yNext n m (verticalEven n m (i,0)) := by
  change (_, pairCoordinate m ((verticalIndex n m i).2,1)) =
    (_, finRotate (2*m) (pairCoordinate m ((verticalIndex n m i).2,0)))
  rw [pairCoordinate_next]
  rfl

theorem horizontalOdd_next (n m : ℕ) (i : Fin (PairCount n m)) :
    horizontalOdd n m (i,1) = xNext n m (horizontalOdd n m (i,0)) := by
  change xNext n m (horizontalEven n m (i,1)) =
    xNext n m (xNext n m (horizontalEven n m (i,0)))
  rw [horizontalEven_next]

theorem verticalOdd_next (n m : ℕ) (i : Fin (PairCount n m)) :
    verticalOdd n m (i,1) = yNext n m (verticalOdd n m (i,0)) := by
  change yNext n m (verticalEven n m (i,1)) =
    yNext n m (yNext n m (verticalEven n m (i,0)))
  rw [verticalEven_next]

/-- Distinct endpoints and complete site coverage are consequences of the bijection. -/
theorem matching_endpoints_ne (n m : ℕ) (c : Fin 4) (i : Fin (PairCount n m)) :
    matching n m c (i,0) ≠ matching n m c (i,1) := by
  intro h
  have := (matching n m c).injective h
  have : (0 : Fin 2) = 1 := congrArg Prod.snd this
  exact zero_ne_one this

/-- Every matching covers every site exactly once, as an exact sum identity. -/
theorem matching_site_sum {A : Type*} [AddCommMonoid A]
    (n m : ℕ) (c : Fin 4) (f : Vertex n m → A) :
    (∑ i, (f (matching n m c (i,0)) + f (matching n m c (i,1)))) = ∑ v, f v := by
  have h := (matching n m c).sum_comp f
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_two] using h

/-- The two horizontal matchings cover exactly the positive horizontal torus edges. -/
theorem horizontal_edge_sum {A : Type*} [AddCommMonoid A]
    (n m : ℕ) (f : Vertex n m → Vertex n m → A) :
    (∑ i, f (horizontalEven n m (i,0)) (horizontalEven n m (i,1))) +
    (∑ i, f (horizontalOdd n m (i,0)) (horizontalOdd n m (i,1))) =
      ∑ v, f v (xNext n m v) := by
  rw [← matching_site_sum n m 0 (fun v => f v (xNext n m v))]
  simp only [matching, Matrix.cons_val_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [horizontalEven_next, horizontalOdd_next]
  rfl

/-- The two vertical matchings cover exactly the positive vertical torus edges. -/
theorem vertical_edge_sum {A : Type*} [AddCommMonoid A]
    (n m : ℕ) (f : Vertex n m → Vertex n m → A) :
    (∑ i, f (verticalEven n m (i,0)) (verticalEven n m (i,1))) +
    (∑ i, f (verticalOdd n m (i,0)) (verticalOdd n m (i,1))) =
      ∑ v, f v (yNext n m v) := by
  rw [← matching_site_sum n m 2 (fun v => f v (yNext n m v))]
  have hmatch : matching n m 2 = verticalEven n m := by simp [matching]
  rw [hmatch, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [verticalEven_next, verticalOdd_next]
  rfl

/-- Positive coordinate steps have no fixed sites on nontrivial even cycles. -/
theorem xNext_ne (n m : ℕ) (hn : 0 < n) (v : Vertex n m) : xNext n m v ≠ v := by
  letI : NeZero (2*n) := ⟨by omega⟩
  intro he
  have hx := congrArg Prod.fst he
  change finRotate (2*n) v.1 = v.1 at hx
  rw [rotate_apply] at hx
  simp at hx

theorem yNext_ne (n m : ℕ) (hm : 0 < m) (v : Vertex n m) : yNext n m v ≠ v := by
  letI : NeZero (2*m) := ⟨by omega⟩
  intro he
  have hy := congrArg Prod.snd he
  change finRotate (2*m) v.2 = v.2 at hy
  rw [rotate_apply] at hy
  simp at hy

#print axioms matching_site_sum
#print axioms horizontal_edge_sum
#print axioms vertical_edge_sum

end Torus
end BilayerGap
