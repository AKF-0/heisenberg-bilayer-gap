import Dressed.CubicResidualIntervals

/-! Concrete .1 whole-interval bounds for the actual physical degree-two
residual on the 4×4, 8×4, and 8×8 seed tori. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicResidualIntervalBounds
open BilayerGap BilayerDressed.SeedGraphs BilayerDressed.CubicSeedChecks
open BilayerDressed.CubicWick.FourRegularData BilayerDressed.CubicResidualPair
open BilayerDressed.CubicResidualPolynomial BilayerDressed.CubicResidualCoefficients
open BilayerDressed.CubicResidualSeedCoefficients BilayerDressed.CubicResidualIntervals
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem residualShift_root (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    GlobalResidual.residualShift (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g=
      (3*((2*n)*(2*m) : ℝ)/2)*g*
        (rootKernel n m g (Torus.xNext n m 0)+rootKernel n m g (Torus.yNext n m 0)) := by
  have hx (u : Torus.Vertex n m) :
      cubicKernel (graph n m h) g u (Torus.xNext n m u)=
        rootKernel n m g (Torus.xNext n m 0) := by
    have ht := kernel_translation n m h g 0 (Torus.xNext n m 0) u
    rw [zero_add,←xNext_add,zero_add,kernel_root n m h hi] at ht
    exact ht
  have hy (u : Torus.Vertex n m) :
      cubicKernel (graph n m h) g u (Torus.yNext n m u)=
        rootKernel n m g (Torus.yNext n m 0) := by
    have ht := kernel_translation n m h g 0 (Torus.yNext n m 0) u
    rw [zero_add,←yNext_add,zero_add,kernel_root n m h hi] at ht
    exact ht
  simp only [GlobalResidual.residualShift,hx,hy,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Torus.Vertex,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem physical_residual2_norm_sq_bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex 2 2)) (𝕜 := ℝ)
      ((GlobalResidual.residual2 (cubicKernel (graph 2 2 four_by_four_conditions) g)
        (Torus.xNext 2 2) (Torus.yNext 2 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 2 2)) : ConfigurationMatrix (Torus.Vertex 2 2))
      vacuumVector‖^2≤(ScalarTrial.F16_2 : ℝ) := by
  rw [coe_residual2 2 2 four_by_four_conditions four_by_four_incidence,
    residual_vacuum_norm_sq 2 2 four_by_four_conditions four_by_four_incidence,←normCoeff_evaluate]
  exact normSquare_bound16 g hg hmax

def endpoint16 (q : Torus.Vertex 2 2) : ℚ :=
  kernelTable16 q 0/10+kernelTable16 q 1/100+kernelTable16 q 2/1000

theorem rootKernel_endpoint16 (q : Torus.Vertex 2 2) :
    rootKernel 2 2 (1/10) q=(endpoint16 q : ℝ) := by
  rw [rootKernel_coeff,(kernel_table16 q).1,(kernel_table16 q).2.1,(kernel_table16 q).2.2]
  simp only [endpoint16,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat]
  ring

def correction16 : ℚ := 178671581/504222432000

theorem tau_eq16 : tau 11597344=(correction16 : ℝ) := by
  norm_num [tau,correction16]

def meanEnvelope16 : ℚ :=
  (16/2)*∑ q : Torus.Vertex 2 2,3*envelope16 q*(|endpoint16 q|+correction16)

def meanBound16 : ℚ := 362340055025101/6722965760000000000

theorem meanEnvelope16_eq : meanEnvelope16=meanBound16 := by
  decide +kernel

/-- The actual rooted pair-mean coefficient, not yet the later Wick expectation. -/
theorem pairMeanCoefficient_bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    pairMeanCoefficient 2 2 four_by_four_conditions g
      (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10)) (tau 11597344))≤
        (meanBound16 : ℝ) := by
  rw [tau_eq16]
  have hh := pairMeanCoefficient_le_envelope 2 2 four_by_four_conditions four_by_four_incidence g (1/10)
    (correction16 : ℝ) (by norm_num [correction16]) (fun q => (envelope16 q : ℝ))
    (rootResidual_bound16 g hg hmax)
  calc
    _ ≤ (((2*2)*(2*2) : ℝ)/2)*∑ q,3*(envelope16 q : ℝ)*
        (|rootKernel 2 2 (1/10) q|+(correction16 : ℝ)) := hh
    _ = (meanEnvelope16 : ℝ) := by
      simp only [meanEnvelope16,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum,
        Rat.cast_add,Rat.cast_abs,rootKernel_endpoint16]
      norm_num
    _ = (meanBound16 : ℝ) := by rw [meanEnvelope16_eq]

theorem physical_residual2_norm_sq_bound32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex 4 2)) (𝕜 := ℝ)
      ((GlobalResidual.residual2 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
        (Torus.xNext 4 2) (Torus.yNext 4 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 2)) : ConfigurationMatrix (Torus.Vertex 4 2))
      vacuumVector‖^2≤(ScalarTrial.F32_2 : ℝ) := by
  rw [coe_residual2 4 2 eight_by_four_conditions eight_by_four_incidence,
    residual_vacuum_norm_sq 4 2 eight_by_four_conditions eight_by_four_incidence,←normCoeff_evaluate]
  exact normSquare_bound32 g hg hmax

def endpoint32 (q : Torus.Vertex 4 2) : ℚ :=
  kernelTable32 q 0/10+kernelTable32 q 1/100+kernelTable32 q 2/1000

theorem rootKernel_endpoint32 (q : Torus.Vertex 4 2) :
    rootKernel 4 2 (1/10) q=(endpoint32 q : ℝ) := by
  rw [rootKernel_coeff,(kernel_table32 q).1,(kernel_table32 q).2.1,(kernel_table32 q).2.2]
  simp only [endpoint32,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat]
  ring

def correction32 : ℚ := 237228149/672296576000

theorem tau_eq32 : tau 11548632=(correction32 : ℝ) := by
  norm_num [tau,correction32]

def meanEnvelope32 : ℚ :=
  (32/2)*∑ q : Torus.Vertex 4 2,3*envelope32 q*(|endpoint32 q|+correction32)

def meanBound32 : ℚ := 9681283444697019/86053961728000000000

theorem meanEnvelope32_eq : meanEnvelope32=meanBound32 := by
  decide +kernel

/-- The actual rooted pair-mean coefficient, not yet the later Wick expectation. -/
theorem pairMeanCoefficient_bound32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    pairMeanCoefficient 4 2 eight_by_four_conditions g
      (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10)) (tau 11548632))≤
        (meanBound32 : ℝ) := by
  rw [tau_eq32]
  have hh := pairMeanCoefficient_le_envelope 4 2 eight_by_four_conditions eight_by_four_incidence g (1/10)
    (correction32 : ℝ) (by norm_num [correction32]) (fun q => (envelope32 q : ℝ))
    (rootResidual_bound32 g hg hmax)
  calc
    _ ≤ (((2*4)*(2*2) : ℝ)/2)*∑ q,3*(envelope32 q : ℝ)*
        (|rootKernel 4 2 (1/10) q|+(correction32 : ℝ)) := hh
    _ = (meanEnvelope32 : ℝ) := by
      simp only [meanEnvelope32,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum,
        Rat.cast_add,Rat.cast_abs,rootKernel_endpoint32]
      norm_num
    _ = (meanBound32 : ℝ) := by rw [meanEnvelope32_eq]


def endpoint64 (q : Torus.Vertex 4 4) : ℚ :=
  kernelTable64 q 0/10+kernelTable64 q 1/100+kernelTable64 q 2/1000

theorem rootKernel_endpoint64 (q : Torus.Vertex 4 4) :
    rootKernel 4 4 (1/10) q=(endpoint64 q : ℝ) := by
  rw [rootKernel_coeff,(kernel_table64 q).1,(kernel_table64 q).2.1,(kernel_table64 q).2.2]
  simp only [endpoint64,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat]
  ring

def correction64 : ℚ := 70868257/201688972800

theorem tau_eq64 : tau 11499920=(correction64 : ℝ) := by
  norm_num [tau,correction64]

def meanEnvelope64 : ℚ :=
  (64/2)*∑ q : Torus.Vertex 4 4,3*envelope64 q*(|endpoint64 q|+correction64)

def meanBound64 : ℚ := 1410465087620649/5378372608000000000

theorem meanEnvelope64_eq : meanEnvelope64=meanBound64 := by
  decide +kernel

/-- The actual rooted pair-mean coefficient, not yet the later Wick expectation. -/
theorem pairMeanCoefficient_bound64 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    pairMeanCoefficient 4 4 eight_by_eight_conditions g
      (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10)) (tau 11499920))≤
        (meanBound64 : ℝ) := by
  rw [tau_eq64]
  have hh := pairMeanCoefficient_le_envelope 4 4 eight_by_eight_conditions eight_by_eight_incidence g (1/10)
    (correction64 : ℝ) (by norm_num [correction64]) (fun q => (envelope64 q : ℝ))
    (rootResidual_bound64 g hg hmax)
  calc
    _ ≤ (((2*4)*(2*4) : ℝ)/2)*∑ q,3*(envelope64 q : ℝ)*
        (|rootKernel 4 4 (1/10) q|+(correction64 : ℝ)) := hh
    _ = (meanEnvelope64 : ℝ) := by
      simp only [meanEnvelope64,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum,
        Rat.cast_add,Rat.cast_abs,rootKernel_endpoint64]
      norm_num
    _ = (meanBound64 : ℝ) := by rw [meanEnvelope64_eq]

theorem physical_residualShift_eq16 (g : ℝ) :
    GlobalResidual.residualShift (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g=
      -12*g^2-6*g^3-(15/2)*g^4 := by
  rw [residualShift_root 2 2 four_by_four_conditions four_by_four_incidence]
  have hx : Torus.xNext 2 2 (0 : Torus.Vertex 2 2)=(1,0) := by decide +kernel
  have hy : Torus.yNext 2 2 (0 : Torus.Vertex 2 2)=(0,1) := by decide +kernel
  rw [hx,hy]
  simp only [rootKernel_coeff,
    (kernel_table16 (1,0)).1,(kernel_table16 (1,0)).2.1,(kernel_table16 (1,0)).2.2,
    (kernel_table16 (0,1)).1,(kernel_table16 (0,1)).2.1,(kernel_table16 (0,1)).2.2]
  norm_num [kernelTable16,Matrix.cons_val_two]
  ring

theorem physical_residualShift_eq32 (g : ℝ) :
    GlobalResidual.residualShift (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g=
      -24*g^2-12*g^3-(45/4)*g^4 := by
  rw [residualShift_root 4 2 eight_by_four_conditions eight_by_four_incidence]
  have hx : Torus.xNext 4 2 (0 : Torus.Vertex 4 2)=(1,0) := by decide +kernel
  have hy : Torus.yNext 4 2 (0 : Torus.Vertex 4 2)=(0,1) := by decide +kernel
  rw [hx,hy]
  simp only [rootKernel_coeff,
    (kernel_table32 (1,0)).1,(kernel_table32 (1,0)).2.1,(kernel_table32 (1,0)).2.2,
    (kernel_table32 (0,1)).1,(kernel_table32 (0,1)).2.1,(kernel_table32 (0,1)).2.2]
  norm_num [kernelTable32,Matrix.cons_val_two]
  ring

theorem physical_residualShift_eq64 (g : ℝ) :
    GlobalResidual.residualShift (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g=
      -48*g^2-24*g^3-(15)*g^4 := by
  rw [residualShift_root 4 4 eight_by_eight_conditions eight_by_eight_incidence]
  have hx : Torus.xNext 4 4 (0 : Torus.Vertex 4 4)=(1,0) := by decide +kernel
  have hy : Torus.yNext 4 4 (0 : Torus.Vertex 4 4)=(0,1) := by decide +kernel
  rw [hx,hy]
  simp only [rootKernel_coeff,
    (kernel_table64 (1,0)).1,(kernel_table64 (1,0)).2.1,(kernel_table64 (1,0)).2.2,
    (kernel_table64 (0,1)).1,(kernel_table64 (0,1)).2.1,(kernel_table64 (0,1)).2.2]
  norm_num [kernelTable64,Matrix.cons_val_two]
  ring

end BilayerDressed.CubicResidualIntervalBounds
