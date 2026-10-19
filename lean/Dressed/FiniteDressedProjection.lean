import Dressed.FinitePairNormRecursion
import Dressed.FiniteWickSupersolution
import Dressed.DressedVacuum

/-! Exact physical projection of finite occupation creation polynomials. The
one-sided no-repair intertwiner, not multiplicativity of general compression,
is the basis of every identity below. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteDressed
open Matrix FiniteOccupation
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1800000

/-- The exact one-sided creation intertwiner on the site-count total cutoff. -/
 theorem physical_transpose_create {M : ℕ} (hM : 2≤M) (v : V) (α : Fin 3) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (TotalCutoff.create (v,α) : TotalCutoff.Op V M (Fintype.card V)) =
      globalCreate v α * (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  ext s μ
  have h := congrArg (fun A : Matrix (Configuration V) (Occupation V M) ℝ => A s μ.val)
    (inclusion_transpose_create hM v α)
  simp only [Matrix.mul_apply,Matrix.transpose_apply,inclusion,TotalCutoff.physicalInclusion,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] at h ⊢
  change FiniteOccupation.create (v,α) (encode hM s) μ.val = _
  rw [h]
  apply Finset.sum_congr rfl
  intro t _
  have he : μ=encodeTotal hM t ↔ μ.val=encode hM t := Subtype.ext_iff
  simp only [he]

/-- Two creators inherit the exact one-sided identity even at coinciding sites. -/
 theorem physical_transpose_create_pair {M : ℕ} (hM : 2≤M)
    (u v : V) (α β : Fin 3) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (TotalCutoff.create (u,α)*TotalCutoff.create (v,β) :
          TotalCutoff.Op V M (Fintype.card V)) =
      (globalCreate u α*globalCreate v β) *
        (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  rw [←Matrix.mul_assoc,physical_transpose_create,Matrix.mul_assoc,
    physical_transpose_create,←Matrix.mul_assoc]

/-- The signed rung kernel lifted with equal colors, with no extra color factor. -/
def modeKernel (K : Matrix V V ℝ) : Matrix (Mode V) (Mode V) ℝ :=
  FiniteWick.colorLift (χ := Fin 3) K

 theorem color_pair_sum (K : Matrix V V ℝ) :
    (1/2 : ℝ) • (∑ i : Mode V,∑ j : Mode V,
      modeKernel K i j • (globalCreate i.1 i.2 * globalCreate j.1 j.2)) = pairKernelS K := by
  simp only [modeKernel,FiniteWick.colorLift,Fintype.sum_prod_type,ite_smul,zero_smul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true,pairKernelS,pairKernelOperator,pairCreate,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  ring

/-- Exact pair-generator intertwiner for every real signed kernel. -/
 theorem physical_transpose_pair {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (TotalCutoff.Pair.pairCreate (modeKernel K) : TotalCutoff.Op V M (Fintype.card V)) =
      pairKernelS K * (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  have hp (i j : Mode V) :
      (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (TotalCutoff.create i*TotalCutoff.create j : TotalCutoff.Op V M (Fintype.card V)) =
      (globalCreate i.1 i.2*globalCreate j.1 j.2) *
        (TotalCutoff.physicalInclusion (V := V) hM).transpose :=
    physical_transpose_create_pair hM i.1 j.1 i.2 j.2
  simp only [TotalCutoff.Pair.pairCreate,Matrix.mul_smul,Matrix.mul_sum,hp]
  rw [←color_pair_sum K]
  simp only [Matrix.smul_mul,Matrix.sum_mul]

 theorem physical_transpose_pair_pow {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) (k : ℕ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        ((TotalCutoff.Pair.pairCreate (modeKernel K) : TotalCutoff.Op V M (Fintype.card V))^k) =
      (pairKernelS K)^k * (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,←Matrix.mul_assoc,ih,Matrix.mul_assoc,physical_transpose_pair,
      ←Matrix.mul_assoc,←pow_succ]


/-- A genuine finite creation word intertwines one-sidedly. -/
theorem physical_transpose_word {M : ℕ} (hM : 2≤M) (w : List (Mode V)) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
      (w.map (fun i => (TotalCutoff.create i : TotalCutoff.Op V M (Fintype.card V)))).prod =
    (w.map (fun i => globalCreate i.1 i.2)).prod *
      (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [←Matrix.mul_assoc,physical_transpose_create,Matrix.mul_assoc,ih,←Matrix.mul_assoc]

/-- Actual pair powers have exact degree shift, even at the cutoff. -/
theorem pair_pow_eq_zero_of_degree {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (k : ℕ) (ν μ : TotalCutoff.Basis V M N)
    (hdeg : totalDegree ν.val ≠ totalDegree μ.val + 2*k) :
    ((TotalCutoff.Pair.pairCreate B : TotalCutoff.Op V M N)^k) ν μ = 0 := by
  induction k generalizing ν μ with
  | zero =>
    have hne : ν ≠ μ := by intro h; subst μ; simp at hdeg
    simp [hne]
  | succ k ih =>
    rw [pow_succ',Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro ρ _
    by_cases hρ : totalDegree ρ.val = totalDegree μ.val+2*k
    · rw [TotalCutoff.Pair.pairCreate_eq_zero_of_degree B ν ρ (by omega),zero_mul]
    · rw [ih ρ μ hρ,mul_zero]

/-- No pair power survives past the finite total-degree cutoff. -/
theorem pair_pow_eq_zero {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (k : ℕ) (hk : N < 2*k) :
    (TotalCutoff.Pair.pairCreate B : TotalCutoff.Op V M N)^k = 0 := by
  ext ν μ
  exact pair_pow_eq_zero_of_degree B k ν μ (by have hν := ν.property; omega)

/-- The actual hard-core generator is the compression of every pair power. -/
theorem physical_pair_pow {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) (k : ℕ) :
    (pairKernelS K)^k =
      (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        ((TotalCutoff.Pair.pairCreate (modeKernel K) : TotalCutoff.Op V M (Fintype.card V))^k) *
          TotalCutoff.physicalInclusion (V := V) hM := by
  rw [physical_transpose_pair_pow,Matrix.mul_assoc,TotalCutoff.physicalInclusion_transpose_mul,
    Matrix.mul_one]

/-- Sharp physical nilpotence, at one more than half the site count. -/
theorem physical_pair_pow_half_eq_zero (K : Matrix V V ℝ) :
    (pairKernelS K)^(Fintype.card V/2+1) = 0 := by
  rw [physical_pair_pow (M := 2) (by omega) K]
  rw [pair_pow_eq_zero _ _ (by omega),Matrix.mul_zero,Matrix.zero_mul]

theorem pairGenerator_pow_half_eq_zero (K : Matrix V V ℝ) :
    (pairGenerator K)^(Fintype.card V/2+1) = 0 := by
  have hh := congrArg (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
    (physical_pair_pow_half_eq_zero K)
  simpa only [map_pow,map_zero,pairGenerator] using hh

local instance dressedProjectionRatModule : Module ℚ
    (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- The exact physical exponential is the finite half-area Taylor polynomial. -/
theorem dressedVector_eq_taylor_half (K : Matrix V V ℝ) :
    dressedVector K =
      taylorOperator (pairGenerator K) (Fintype.card V/2+1) vacuumVector := by
  rw [dressedVector,nilpotent_exp_eq_taylor _ _ (pairGenerator_pow_half_eq_zero K)]


omit [DecidableEq V] in
@[simp] theorem encodeTotal_vacuum {M : ℕ} (hM : 2≤M) :
    encodeTotal (V := V) hM vacuumConfiguration = TotalCutoff.vacuum := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp [encodeTotal,encode,rungBits,vacuumConfiguration,TotalCutoff.vacuum,Ne.symm (Fin.succ_ne_zero i.2)]

/-- The one-sided projection simply selects the actual encoded coordinates. -/
theorem physical_transpose_apply {M : ℕ} (hM : 2≤M)
    (y : TotalCutoff.PairNorm.Hilbert V M (Fintype.card V)) (s : Configuration V) :
    ((TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin y) s =
      y (encodeTotal hM s) := by
  simp [Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,
    TotalCutoff.physicalInclusion,Matrix.transpose_apply]

/-- The normalized finite vacuum projects to the actual physical vacuum. -/
theorem physical_transpose_vacuum {M : ℕ} (hM : 2≤M) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
      TotalCutoff.PairNorm.vacuumVector = (vacuumVector : ConfigurationHilbert V) := by
  ext s
  rw [physical_transpose_apply]
  have he : encodeTotal hM s = (TotalCutoff.vacuum : TotalCutoff.Basis V M (Fintype.card V)) ↔
      s=vacuumConfiguration := by
    rw [←encodeTotal_vacuum hM]
    exact (TotalCutoff.physical_encode_injective hM).eq_iff
  simp [TotalCutoff.PairNorm.vacuumVector,vacuumVector,EuclideanSpace.single_apply,he]

/-- Every normalized pair power projects exactly, for a signed real kernel. -/
theorem physical_transpose_pairVector {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) (k : ℕ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
      (TotalCutoff.PairNorm.pairVector (modeKernel K) k) =
    ((k.factorial : ℝ)⁻¹) • ((pairGenerator K)^k) vacuumVector := by
  rw [TotalCutoff.PairNorm.pairVector,map_smul]
  congr 1
  have hp := physical_transpose_pair_pow hM K k
  have hv := physical_transpose_vacuum (V := V) hM
  have hm : ((pairGenerator K)^k) =
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) ((pairKernelS K)^k) := by
    simp only [map_pow,pairGenerator]
  rw [hm,←hv]
  ext s
  change (((TotalCutoff.physicalInclusion hM).transpose *ᵥ
      (((TotalCutoff.Pair.pairCreate (modeKernel K) : TotalCutoff.Op V M (Fintype.card V))^k) *ᵥ
        WithLp.ofLp TotalCutoff.PairNorm.vacuumVector)) s) =
      (((pairKernelS K)^k) *ᵥ ((TotalCutoff.physicalInclusion hM).transpose *ᵥ
        WithLp.ofLp TotalCutoff.PairNorm.vacuumVector)) s
  rw [Matrix.mulVec_mulVec,hp,Matrix.mulVec_mulVec]

/-- Exact finite-Taylor projection, with L the inclusive highest pair power. -/
theorem physical_transpose_finiteTrial {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) (L : ℕ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
      (TotalCutoff.PairNorm.finiteTrial (modeKernel K) L) =
    taylorOperator (pairGenerator K) (L+1) vacuumVector := by
  simp only [TotalCutoff.PairNorm.finiteTrial,map_sum,taylorOperator,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    physical_transpose_pairVector]

/-- The hard-core dressed state is exactly the physical projection of a finite
occupation vector, with no infinite Fock state or normalization assumption. -/
theorem dressedVector_eq_projected_trial {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) :
    dressedVector K =
      (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
        (TotalCutoff.PairNorm.finiteTrial (modeKernel K) (Fintype.card V/2)) := by
  rw [physical_transpose_finiteTrial,dressedVector_eq_taylor_half]

/-- The transpose of the actual basis inclusion contracts the genuine Hilbert norm. -/
theorem physical_transpose_norm_le {M : ℕ} (hM : 2≤M)
    (y : TotalCutoff.PairNorm.Hilbert V M (Fintype.card V)) :
    ‖(TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin y‖ ≤ ‖y‖ := by
  have hs : ‖(TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin y‖^2 ≤ ‖y‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    simp only [physical_transpose_apply]
    classical
    calc
      _ = ∑ μ ∈ Finset.univ.image (encodeTotal hM), ‖y μ‖^2 := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => TotalCutoff.physical_encode_injective hM h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg y,norm_nonneg ((TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin y)]

/-- The exact physical dressed norm is bounded by the finite pair-vector norm. -/
theorem dressedVector_norm_le_finiteTrial {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ) :
    ‖dressedVector K‖ ≤
      ‖(TotalCutoff.PairNorm.finiteTrial (modeKernel K) (Fintype.card V/2) :
        TotalCutoff.PairNorm.Hilbert V M (Fintype.card V))‖ := by
  rw [dressedVector_eq_projected_trial hM]
  exact physical_transpose_norm_le hM _


/-- Any proved one-sided operator intertwiner transports actual Hilbert actions. -/
theorem physical_transpose_action {M : ℕ} (hM : 2≤M)
    (Rb : TotalCutoff.Op V M (Fintype.card V)) (Rh : ConfigurationMatrix V)
    (hR : (TotalCutoff.physicalInclusion (V := V) hM).transpose*Rb =
      Rh*(TotalCutoff.physicalInclusion (V := V) hM).transpose)
    (y : TotalCutoff.PairNorm.Hilbert V M (Fintype.card V)) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
      (Rb.toEuclideanLin y) =
    Rh.toEuclideanLin ((TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin y) := by
  ext s
  change ((TotalCutoff.physicalInclusion hM).transpose *ᵥ (Rb *ᵥ WithLp.ofLp y)) s =
    (Rh *ᵥ ((TotalCutoff.physicalInclusion hM).transpose *ᵥ WithLp.ofLp y)) s
  rw [Matrix.mulVec_mulVec,hR,Matrix.mulVec_mulVec]

/-- Exact signed residual-polynomial action through physical projection. The
intertwiner must be proved for the chosen faithful lift; it is not assumed
for arbitrary compressions. -/
theorem physical_action_dressed_eq {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ)
    (Rb : TotalCutoff.Op V M (Fintype.card V)) (Rh : ConfigurationMatrix V)
    (hR : (TotalCutoff.physicalInclusion (V := V) hM).transpose*Rb =
      Rh*(TotalCutoff.physicalInclusion (V := V) hM).transpose) :
    Rh.toEuclideanLin (dressedVector K) =
      (TotalCutoff.physicalInclusion (V := V) hM).transpose.toEuclideanLin
        (Rb.toEuclideanLin (TotalCutoff.PairNorm.finiteTrial (modeKernel K) (Fintype.card V/2))) := by
  rw [physical_transpose_action hM Rb Rh hR,←dressedVector_eq_projected_trial hM]

/-- A faithful finite lift yields a true physical residual norm upper bound. -/
theorem physical_action_dressed_norm_le {M : ℕ} (hM : 2≤M) (K : Matrix V V ℝ)
    (Rb : TotalCutoff.Op V M (Fintype.card V)) (Rh : ConfigurationMatrix V)
    (hR : (TotalCutoff.physicalInclusion (V := V) hM).transpose*Rb =
      Rh*(TotalCutoff.physicalInclusion (V := V) hM).transpose) :
    ‖Rh.toEuclideanLin (dressedVector K)‖ ≤
      ‖Rb.toEuclideanLin (TotalCutoff.PairNorm.finiteTrial (modeKernel K) (Fintype.card V/2))‖ := by
  rw [physical_action_dressed_eq hM K Rb Rh hR]
  exact physical_transpose_norm_le hM _

end BilayerDressed.FiniteDressed
