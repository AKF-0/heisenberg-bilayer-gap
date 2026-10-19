import Dressed.FinitePositiveComparison
import Dressed.FiniteDressedProjection
import Dressed.FinitePairStateNormBridge

/-! The actual signed hard-core dressed trial has a finite positive Wick
majorant. Projection deletes nonnegative contributions only after absolute
values have been taken. Signed and positive-state norms are never equated.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FinitePhysicalWick
open Matrix FiniteOccupation FiniteOccupation.TotalCutoff.PositiveMoments
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem word_eq_prod {σ ι : Type*} [Fintype σ] [DecidableEq σ]
    (C : ι→Matrix σ σ ℝ) (w : List ι) :
    PositiveMatrix.word C w=(w.map C).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [PositiveMatrix.word,List.map_cons,List.prod_cons,ih]

/-- A literal finite coefficient family defines the physical creation polynomial. -/
def physicalPolynomial {α : Type*} [Fintype α] (c : α→ℝ) (w : α→List (Mode V)) :
    ConfigurationMatrix V :=
  PositiveMatrix.creationPolynomial (fun i : Mode V => globalCreate i.1 i.2) c w

 theorem polynomial_intertwiner {M : ℕ} {α : Type*} [Fintype α]
    (hM : 2≤M) (c : α→ℝ) (w : α→List (Mode V)) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose*
      (PositiveMatrix.creationPolynomial TotalCutoff.create c w :
        TotalCutoff.Op V M (Fintype.card V)) =
    physicalPolynomial c w*(TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  have hw (a : α) := FiniteDressed.physical_transpose_word hM (w a)
  simp only [← word_eq_prod] at hw
  simp only [PositiveMatrix.creationPolynomial,physicalPolynomial,Matrix.mul_sum,Matrix.mul_smul,
    Matrix.sum_mul,Matrix.smul_mul,hw]

/-- Exact physical coordinates, with the signed kernel and actual sharp Taylor cutoff. -/
theorem dressedVector_apply {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) (s : Configuration V) :
    dressedVector K s=
      pairState (M := M) (N := Fintype.card V) (FiniteDressed.modeKernel K)
        (Fintype.card V/2) (encodeTotal hM s) := by
  rw [FiniteDressed.dressedVector_eq_projected_trial hM,FiniteDressed.physical_transpose_apply]
  exact (congrFun (TotalCutoff.PairStateBridge.pairState_eq_ofLp_finiteTrial
    (M := M) (N := Fintype.card V) (FiniteDressed.modeKernel K) (Fintype.card V/2)) _).symm

/-- The polynomial action is exactly a restricted signed finite occupation action. -/
theorem physicalPolynomial_apply {M : ℕ} {α : Type*} [Fintype α]
    (hM : 2≤M) (K : Matrix V V ℝ) (c : α→ℝ) (w : α→List (Mode V))
    (s : Configuration V) :
    ((physicalPolynomial c w).toEuclideanLin (dressedVector K)) s=
      ((PositiveMatrix.creationPolynomial TotalCutoff.create c w).mulVec
        (pairState (M := M) (N := Fintype.card V) (FiniteDressed.modeKernel K)
          (Fintype.card V/2))) (encodeTotal hM s) := by
  rw [FiniteDressed.physical_action_dressed_eq hM K _ _ (polynomial_intertwiner hM c w),
    FiniteDressed.physical_transpose_apply]
  change (_ *ᵥ WithLp.ofLp (TotalCutoff.PairNorm.finiteTrial (FiniteDressed.modeKernel K)
    (Fintype.card V/2) : TotalCutoff.PairNorm.Hilbert V M (Fintype.card V))) _ = _
  rw [← TotalCutoff.PairStateBridge.pairState_eq_ofLp_finiteTrial]

/-- A genuine signed physical expectation, not an auxiliary positive moment. -/
theorem physical_polynomial_mean_bound {M : ℕ} {α : Type*} [Fintype α]
    (hM : 2≤M) (hAM : Fintype.card V≤M)
    (K : Matrix V V ℝ) (hsym : ∀ i j,K i j=K j i)
    (L : Matrix (Mode V) (Mode V) ℝ) (hL0 : ∀ i j,0≤L i j)
    (q : ℝ) (hq : q<1)
    (hrow : ∀ i,∑ j,(PositiveMatrix.entryAbs (FiniteDressed.modeKernel K)*
      PositiveMatrix.entryAbs (FiniteDressed.modeKernel K)) i j≤q)
    (hL : ∀ i j,|FiniteDressed.modeKernel K i j|+
      ((PositiveMatrix.entryAbs (FiniteDressed.modeKernel K)*
        PositiveMatrix.entryAbs (FiniteDressed.modeKernel K))*L) i j≤L i j)
    (c : α→ℝ) (w : α→List (Mode V)) :
    |⟪dressedVector K,(physicalPolynomial c w).toEuclideanLin (dressedVector K)⟫|≤
      dotProduct
        (pairState (M := M) (N := Fintype.card V)
          (PositiveMatrix.entryAbs (FiniteDressed.modeKernel K)) (Fintype.card V/2))
        (pairState (M := M) (N := Fintype.card V)
          (PositiveMatrix.entryAbs (FiniteDressed.modeKernel K)) (Fintype.card V/2))*
        ∑ a,|c a| *FiniteWickPairings.wick L (w a) := by
  have hs (i j : Mode V) : FiniteDressed.modeKernel K i j=FiniteDressed.modeKernel K j i := by
    unfold FiniteDressed.modeKernel FiniteWick.colorLift
    by_cases he : i.2=j.2
    · simp [he,hsym]
    · simp [he,Ne.symm he]
  have hi := injected_pairState_polynomial_mean_bound hAM (FiniteDressed.modeKernel K) L
    hs hL0 q hq hrow hL (Fintype.card V/2) c w (encodeTotal hM)
    (TotalCutoff.physical_encode_injective hM)
  have he : ⟪dressedVector K,(physicalPolynomial c w).toEuclideanLin (dressedVector K)⟫=
      dotProduct
        (fun s => pairState (M := M) (N := Fintype.card V) (FiniteDressed.modeKernel K)
          (Fintype.card V/2) (encodeTotal hM s))
        (fun s => ((PositiveMatrix.creationPolynomial TotalCutoff.create c w).mulVec
          (pairState (M := M) (N := Fintype.card V) (FiniteDressed.modeKernel K)
            (Fintype.card V/2))) (encodeTotal hM s)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rw [dotProduct_comm]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro s _
    change dressedVector K s * ((physicalPolynomial c w).toEuclideanLin (dressedVector K)) s = _
    rw [dressedVector_apply hM,physicalPolynomial_apply hM]
  rw [he]
  exact hi

end BilayerDressed.FinitePhysicalWick
