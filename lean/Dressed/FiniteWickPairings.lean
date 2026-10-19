import Dressed.FinitePositiveMoments

/-! Finite perfect-matching bounds for the actual positive pair state.
The normalization factor is the true finite squared norm, not silently one.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteWickPairings
variable {ι : Type*}

/-- A finite recursive sum over all pairings of the listed occurrences. -/
def wick (L : ι→ι→ℝ) (l : List ι) : ℝ :=
  match l with
  | [] => 1
  | i::l => ∑ a : Fin l.length,L i l[a]*wick L (l.eraseIdx a.val)
termination_by l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)

theorem wick_nonneg (L : ι→ι→ℝ) (hL : ∀ i j,0≤L i j) (l : List ι) :
    0≤wick L l := by
  apply (measure List.length).wf.induction l
  intro l ih
  cases l with
  | nil => simp [wick]
  | cons i l =>
    rw [wick]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hL i l[a])
      (ih _ (Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)))

/-- Any deletion recurrence is dominated by its finite pairing polynomial. -/
theorem dominates (L : ι→ι→ℝ) (hL : ∀ i j,0≤L i j) (F : List ι→ℝ)
    (hstep : ∀ i l,F (i::l)≤∑ a : Fin l.length,L i l[a]*F (l.eraseIdx a.val))
    (l : List ι) : F l≤F []*wick L l := by
  apply (measure List.length).wf.induction l
  intro l ih
  cases l with
  | nil => simp [wick]
  | cons i l =>
    calc
      F (i::l)≤∑ a : Fin l.length,L i l[a]*F (l.eraseIdx a.val) := hstep i l
      _ ≤ ∑ a : Fin l.length,L i l[a]*(F []*wick L (l.eraseIdx a.val)) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hL i l[a])
        apply ih (l.eraseIdx a.val)
        exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)
      _ = F []*wick L (i::l) := by
        rw [wick,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

@[simp] theorem wick_nil (L : ι→ι→ℝ) : wick L []=1 := by rw [wick]
@[simp] theorem wick_pair (L : ι→ι→ℝ) (a b : ι) : wick L [a,b]=L a b := by
  simp [wick,Fin.sum_univ_succ]

 theorem wick_four (L : ι→ι→ℝ) (a b c d : ι) :
    wick L [a,b,c,d]=L a b*L c d+L a c*L b d+L a d*L b c := by
  simp [wick,Fin.sum_univ_succ]
  ring

 theorem wick_four_le (L : ι→ι→ℝ) (hL : ∀ i j,0≤L i j)
    (m : ℝ) (hm : 0 ≤ m) (hLm : ∀ i j,L i j ≤ m) (a b c d : ι) :
    wick L [a,b,c,d]≤3*m^2 := by
  rw [wick_four]
  have h₁ := mul_le_mul (hLm a b) (hLm c d) (hL c d) hm
  have h₂ := mul_le_mul (hLm a c) (hLm b d) (hL b d) hm
  have h₃ := mul_le_mul (hLm a d) (hLm b c) (hL b c) hm
  nlinarith

 theorem wick_six_le (L : ι→ι→ℝ) (hL : ∀ i j,0≤L i j)
    (m : ℝ) (hm : 0 ≤ m) (hLm : ∀ i j,L i j ≤ m) (a b c d e f : ι) :
    wick L [a,b,c,d,e,f]≤15*m^3 := by
  rw [wick]
  calc
    _ ≤ ∑ i : Fin 5,m*(3*m^2) := by
      apply Finset.sum_le_sum
      intro i _
      fin_cases i <;> simp only [List.getElem_cons_zero,List.getElem_cons_succ,
        List.eraseIdx_cons_zero,List.eraseIdx_cons_succ]
      all_goals
        exact mul_le_mul (hLm _ _) (wick_four_le L hL m hm hLm _ _ _ _)
          (wick_nonneg L hL _) hm
    _ = _ := by simp; ring

/-- Three color contractions retain exactly the factors 9, 3, 3. -/
theorem color_wick_four (L : ι→ι→ℝ) (a b c d : ι) :
    (∑ α : Fin 3,∑ β : Fin 3,
      wick (FiniteWick.colorLift L) [(a,α),(b,α),(c,β),(d,β)])=
      9*L a b*L c d+3*L a c*L b d+3*L a d*L b c := by
  simp only [wick_four,FiniteWick.colorLift]
  simp [Fin.sum_univ_succ]
  ring

/-- Three free color labels and fifteen pairings give the rigorous factor 405. -/
theorem color_wick_six_le (L : ι→ι→ℝ) (hL : ∀ i j,0≤L i j)
    (m : ℝ) (hm : 0 ≤ m) (hLm : ∀ i j,L i j ≤ m) (a b c d e f : ι) :
    (∑ α : Fin 3,∑ β : Fin 3,∑ γ : Fin 3,
      wick (FiniteWick.colorLift L) [(a,α),(b,α),(c,β),(d,β),(e,γ),(f,γ)])≤405*m^3 := by
  have hp (u v : ι×Fin 3) : 0≤FiniteWick.colorLift L u v := by
    unfold FiniteWick.colorLift
    split_ifs
    · exact hL _ _
    · norm_num
  have hb (u v : ι×Fin 3) : FiniteWick.colorLift L u v ≤ m := by
    unfold FiniteWick.colorLift
    split_ifs
    · exact hLm _ _
    · exact hm
  calc
    _ ≤ ∑ _α : Fin 3,∑ _β : Fin 3,∑ _γ : Fin 3,15*m^3 := by
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro β _
      apply Finset.sum_le_sum
      intro γ _
      exact wick_six_le _ hp m hm hb _ _ _ _ _ _
    _ = _ := by simp; ring

end BilayerDressed.FiniteWickPairings

namespace BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The genuine finite-state Wick upper theorem. There is no Gaussian state oracle. -/
theorem pairState_wick_bound {M N : ℕ} (hNM : N≤M)
    (B L : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j,0≤B i j)
    (hsym : ∀ i j,B i j=B j i) (hL0 : ∀ i j,0≤L i j)
    (q : ℝ) (hq : q<1) (hrow : ∀ i,∑ j,(B*B) i j≤q)
    (hL : ∀ i j,B i j+((B*B)*L) i j≤L i j)
    (n : ℕ) (l : List (Mode V)) :
    PositiveMatrix.expect (pairState (M := M) (N := N) B n) (PositiveMatrix.word create l)≤
      dotProduct (pairState (M := M) (N := N) B n) (pairState (M := M) (N := N) B n)*
        FiniteWickPairings.wick L l := by
  have h := FiniteWickPairings.dominates L hL0
    (fun l => PositiveMatrix.expect (pairState (M := M) (N := N) B n) (PositiveMatrix.word create l))
    (pairState_wick_step hNM B L hB hsym q hq hrow hL n) l
  simpa only [PositiveMatrix.word,PositiveMatrix.expect,Matrix.one_mulVec] using h

end BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments
