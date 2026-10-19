import Dressed.CubicResidualPolynomial
import Dressed.FiniteDressedProjection
import Dressed.FiniteWordHomogeneous

/-! The actual cubic pair residual is a homogeneous finite bosonic creator.
The vacuum norm equality is proved through the exact safe-grade commutator,
not inferred from the one-sided physical compression. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicPairHomogeneous
open Matrix FiniteOccupation TotalCutoff
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit normalized degree-two coefficients of the half-ordered pair sum. -/
def pairCoefficients (B : Matrix (Mode V) (Mode V) ℝ) : (Mode V → ℕ) → ℝ :=
  WordHomogeneous.polynomialCoefficient Finset.univ
    (fun p : Mode V × Mode V => B p.1 p.2 / 2) (fun p => [p.1,p.2])

/-- This is the actual finite pair matrix, with no representation premise. -/
theorem pairCreate_eq_homogeneous {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) :
    (Pair.pairCreate B : TotalCutoff.Op V M N) =
      Homogeneous.homogeneousOperator 2 (pairCoefficients B) := by
  have h := WordHomogeneous.wordPolynomial_eq_homogeneousOperator
    (M := M) (N := N) (d := 2) Finset.univ
    (fun p : Mode V × Mode V => B p.1 p.2 / 2) (fun p => [p.1,p.2]) (by simp)
  change _ = Homogeneous.homogeneousOperator 2 (pairCoefficients B) at h
  rw [←h]
  simp only [Pair.pairCreate,Fintype.sum_prod_type,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Matrix.mul_one,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  congr 1
  ring

/-- The genuine pair creator has vacuum norm Tr(B²)/2 when two grades fit. -/
theorem pair_vacuum_norm_sq {M N : ℕ} (hNM : N ≤ M) (hN : 2 ≤ N)
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j=B j i) :
    ‖(Pair.pairCreate B : TotalCutoff.Op V M N).toEuclideanLin
      PairNorm.vacuumVector‖^2=Matrix.trace (B*B)/2 := by
  let x : PairNorm.Hilbert V M N := PairNorm.vacuumVector
  have hx : PairNorm.HasGrade 0 x := PairNorm.grade_vacuumVector
  have hsafe (μ : TotalCutoff.Basis V M N) (hμ : (WithLp.ofLp x) μ ≠ 0) :
      totalDegree μ.val+2≤N := by
    have hd : totalDegree μ.val=0 := by
      by_contra hd
      exact hμ (hx μ hd)
    simpa [hd] using hN
  have hz : (Pair.secondQuantization (B*B) : TotalCutoff.Op V M N).mulVec
      (WithLp.ofLp x)=0 := by
    change (Pair.secondQuantization (B*B) : TotalCutoff.Op V M N).mulVec
      (Pi.single TotalCutoff.vacuum 1)=0
    simp only [Pair.secondQuantization,Matrix.sum_mulVec,Matrix.smul_mulVec,
      ←Matrix.mulVec_mulVec,annihilate_vacuum_vector,Matrix.mulVec_zero,
      smul_zero,Finset.sum_const_zero]
  have hc := congrArg (fun y => dotProduct (WithLp.ofLp x) y)
    (Pair.pairCommutator_mulVec_of_safe_support B hB hNM (WithLp.ofLp x) hsafe)
  dsimp only at hc
  rw [Pair.pairCommutator_form_eq_norm_sq,Matrix.add_mulVec,hz,
    Matrix.smul_mulVec,Matrix.one_mulVec,zero_add,dotProduct_smul] at hc
  have hadj : (Pair.pairCreate B : TotalCutoff.Op V M N).transpose.toEuclideanLin x=0 :=
    PairNorm.adjointAction_eq_zero_of_grade_zero B hx
  have hxx : dotProduct (WithLp.ofLp x) (WithLp.ofLp x)=1 := by
    simp [x,PairNorm.vacuumVector]
  simpa only [hadj,norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,hxx,smul_eq_mul,mul_one]
    using hc

/-- Three independent colors contribute exactly three copies to the trace. -/
theorem modeKernel_trace_square (K : Matrix V V ℝ) (hK : ∀ u v, K u v=K v u) :
    Matrix.trace (FiniteDressed.modeKernel K*FiniteDressed.modeKernel K)=
      3*∑ u,∑ v,(K u v)^2 := by
  simp only [FiniteDressed.modeKernel,FiniteWick.colorLift_mul]
  simp only [Matrix.trace,Matrix.diag,FiniteWick.colorLift,
    Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u _
  congr 1
  apply Finset.sum_congr rfl; intro v _
  rw [hK v u]
  ring

/-- Equality of actual bosonic and physical pair vacuum norms. The zero diagonal
is essential on the physical side, where a repeated site is killed. -/
theorem pair_vacuum_norm_eq_physical {M N : ℕ} (hNM : N ≤ M) (hN : 2 ≤ N)
    (K : Matrix V V ℝ) (hK : ∀ u v, K u v=K v u) (hdiag : ∀ u, K u u=0) :
    ‖(Pair.pairCreate (FiniteDressed.modeKernel K) : TotalCutoff.Op V M N).toEuclideanLin
      PairNorm.vacuumVector‖^2=
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairKernelS K)
      vacuumVector‖^2 := by
  have hB (i j : Mode V) : FiniteDressed.modeKernel K i j=FiniteDressed.modeKernel K j i := by
    simp only [FiniteDressed.modeKernel,FiniteWick.colorLift,hK i.1 j.1]
    simp [eq_comm]
  rw [pair_vacuum_norm_sq hNM hN _ hB,modeKernel_trace_square K hK,
    pairKernelS_vacuum_norm_sq K hK hdiag]
  ring

/-- Concrete cubic coefficient function, before any scalar norm majorant. -/
def residualCoefficients (G : FourRegularData V) (g : ℝ) : (Mode V → ℕ) → ℝ :=
  pairCoefficients (FiniteDressed.modeKernel (CubicResidualPair.residual G g))

/-- Exact one-sided physical intertwiner for the actual homogeneous cubic pair. -/
theorem physical_transpose_residual {M : ℕ} (hM : 2≤M)
    (n m : ℕ) (h : SeedGraphs.Conditions n m) (hi : SeedGraphs.IncidenceIdentity n m) (g : ℝ) :
    (TotalCutoff.physicalInclusion (V := BilayerGap.Torus.Vertex n m) hM).transpose *
      Homogeneous.homogeneousOperator 2 (residualCoefficients (SeedGraphs.graph n m h) g)=
    CubicResidualPair.physicalPairResidual n m h g *
      (TotalCutoff.physicalInclusion (V := BilayerGap.Torus.Vertex n m) hM).transpose := by
  rw [residualCoefficients,←pairCreate_eq_homogeneous,FiniteDressed.physical_transpose_pair,
    CubicResidualPair.physicalPairResidual_eq n m h hi]

/-- The actual homogeneous residual seed has exactly the previously proved
physical vacuum norm, with all cutoff conditions displayed. -/
theorem residual_vacuum_norm_eq_physical {M N : ℕ} (hNM : N≤M) (hN : 2≤N)
    (n m : ℕ) (h : SeedGraphs.Conditions n m) (hi : SeedGraphs.IncidenceIdentity n m) (g : ℝ) :
    ‖(Homogeneous.homogeneousOperator (M := M) (N := N) 2
      (residualCoefficients (SeedGraphs.graph n m h) g)).toEuclideanLin PairNorm.vacuumVector‖^2=
    ‖Matrix.toEuclideanCLM (n := Configuration (BilayerGap.Torus.Vertex n m)) (𝕜 := ℝ)
      (CubicResidualPair.physicalPairResidual n m h g) vacuumVector‖^2 := by
  rw [residualCoefficients,←pairCreate_eq_homogeneous,
    CubicResidualPair.physicalPairResidual_eq n m h hi]
  exact pair_vacuum_norm_eq_physical hNM hN _
    (CubicResidualPair.residual_symmetric _ _) (CubicResidualPair.residual_diagonal _ _)

/-- The same intertwiner targets the literal global residual2 operator. -/
theorem physical_transpose_literal_residual {M : ℕ} (hM : 2≤M)
    (n m : ℕ) (h : SeedGraphs.Conditions n m) (hi : SeedGraphs.IncidenceIdentity n m) (g : ℝ) :
    (TotalCutoff.physicalInclusion (V := BilayerGap.Torus.Vertex n m) hM).transpose *
      Homogeneous.homogeneousOperator 2 (residualCoefficients (SeedGraphs.graph n m h) g)=
    ((GlobalResidual.residual2
      (CubicWick.FourRegularData.cubicKernel (SeedGraphs.graph n m h) g)
      (BilayerGap.Torus.xNext n m) (BilayerGap.Torus.yNext n m) g :
        GlobalResidual.creationAlgebra (BilayerGap.Torus.Vertex n m)) :
          ConfigurationMatrix (BilayerGap.Torus.Vertex n m)) *
      (TotalCutoff.physicalInclusion (V := BilayerGap.Torus.Vertex n m) hM).transpose := by
  rw [CubicResidualPolynomial.coe_residual2_eq_physicalPairResidual n m h hi]
  exact physical_transpose_residual hM n m h hi g

end BilayerDressed.CubicPairHomogeneous
