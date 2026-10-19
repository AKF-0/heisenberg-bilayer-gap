import Dressed.FinitePairNormRecursion
import Mathlib.Tactic.NormNum

/-! Fixed finite rational majorants for the three actual cubic-kernel seeds.
All sums use the proved pair recursion; this file assumes no numerical oracle.
Operator and coefficient identifications remain separate proof dependencies. -/
namespace BilayerDressed.ScalarTrial
open scoped BigOperators
open FiniteOccupation.TotalCutoff.PairNorm
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

def q : ℚ := (493/4000)^2
def moment (T : ℚ) (L d : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (L+1), ((2*m+d).choose d : ℚ)*rationalMajorant q T m

def T16 : ℚ := 1087251/8000000
def M16_0 : ℚ := 1070873423/1000000000
theorem moment16_0 : moment T16 8 0 < M16_0 := by
  norm_num [moment, T16, M16_0, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M16_2 : ℚ := 726404409/500000000
theorem moment16_2 : moment T16 8 2 < M16_2 := by
  norm_num [moment, T16, M16_2, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M16_4 : ℚ := 1118930283/500000000
theorem moment16_4 : moment T16 8 4 < M16_4 := by
  norm_num [moment, T16, M16_4, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M16_6 : ℚ := 1794975549/500000000
theorem moment16_6 : moment T16 8 6 < M16_6 := by
  norm_num [moment, T16, M16_6, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def F16_2 : ℚ := 2871661602999/819200000000000000
def F16_4 : ℚ := 10086255523899002668131/419430400000000000000000000
def ell16_6 : ℚ := 92232993647601/655360000000000000
def F16_6 : ℚ := 27*ell16_6^2
def e16_2 : ℚ := 2256710723/1000000000000
theorem root16_2 : 0<e16_2 ∧ F16_2*M16_2≤e16_2^2 := by
  norm_num [e16_2, F16_2, M16_2]
def e16_4 : ℚ := 7335868583/1000000000000
theorem root16_4 : 0<e16_4 ∧ F16_4*M16_4≤e16_4^2 := by
  norm_num [e16_4, F16_4, M16_4]
def e16_6 : ℚ := 692791463/500000000000
theorem root16_6 : 0<e16_6 ∧ F16_6*M16_6≤e16_6^2 := by
  norm_num [e16_6, F16_6, M16_6, ell16_6]
theorem epsilon16 : e16_2+e16_4+e16_6 < 5491/500000 := by
  norm_num [e16_2, e16_4, e16_6]
def meanCoefficient16 : ℚ := 189353926066535630290438652068558054213728219/1215465649108811054688763904000000000000000000000
theorem mean16 : M16_0*meanCoefficient16 < 167/1000000 := by
  norm_num [M16_0, meanCoefficient16]

def T32 : ℚ := 4330737/16000000
def M32_0 : ℚ := 286527607/250000000
theorem moment32_0 : moment T32 16 0 < M32_0 := by
  norm_num [moment, T32, M32_0, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M32_2 : ℚ := 1981768181/1000000000
theorem moment32_2 : moment T32 16 2 < M32_2 := by
  norm_num [moment, T32, M32_2, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M32_4 : ℚ := 387485587/100000000
theorem moment32_4 : moment T32 16 4 < M32_4 := by
  norm_num [moment, T32, M32_4, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M32_6 : ℚ := 7533402531/1000000000
theorem moment32_6 : moment T32 16 6 < M32_6 := by
  norm_num [moment, T32, M32_6, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def F32_2 : ℚ := 10257117031323/2621440000000000000
def F32_4 : ℚ := 61781177216998702643223/1342177280000000000000000000
def ell32_6 : ℚ := 2956223510791297/10485760000000000000
def F32_6 : ℚ := 27*ell32_6^2
def e32_2 : ℚ := 2784640403/1000000000000
theorem root32_2 : 0<e32_2 ∧ F32_2*M32_2≤e32_2^2 := by
  norm_num [e32_2, F32_2, M32_2]
def e32_4 : ℚ := 2671043251/200000000000
theorem root32_4 : 0<e32_4 ∧ F32_4*M32_4≤e32_4^2 := by
  norm_num [e32_4, F32_4, M32_4]
def e32_6 : ℚ := 2010410883/500000000000
theorem root32_6 : 0<e32_6 ∧ F32_6*M32_6≤e32_6^2 := by
  norm_num [e32_6, F32_6, M32_6, ell32_6]
theorem epsilon32 : e32_2+e32_4+e32_6 < 5043/250000 := by
  norm_num [e32_2, e32_4, e32_6]
def meanCoefficient32 : ℚ := 191647563709930314689695641370438602408638579856153/637254054239960330240662649700352000000000000000000000
theorem mean32 : M32_0*meanCoefficient32 < 173/500000 := by
  norm_num [M32_0, meanCoefficient32]

def T64 : ℚ := 431247/800000
def M64_0 : ℚ := 328014697/250000000
theorem moment64_0 : moment T64 32 0 < M64_0 := by
  norm_num [moment, T64, M64_0, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M64_2 : ℚ := 828790239/250000000
theorem moment64_2 : moment T64 32 2 < M64_2 := by
  norm_num [moment, T64, M64_2, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M64_4 : ℚ := 544139463/62500000
theorem moment64_4 : moment T64 32 4 < M64_4 := by
  norm_num [moment, T64, M64_4, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def M64_6 : ℚ := 169920309/8000000
theorem moment64_6 : moment T64 32 6 < M64_6 := by
  norm_num [moment, T64, M64_6, q, rationalMajorant, Finset.sum_range_succ, Nat.choose]

def F64_2 : ℚ := 2102224214157/409600000000000000
def F64_4 : ℚ := 1180448911477511430937329/13421772800000000000000000000
def ell64_6 : ℚ := 1480495612429681/2621440000000000000
def F64_6 : ℚ := 27*ell64_6^2
def e64_2 : ℚ := 4124885071/1000000000000
theorem root64_2 : 0<e64_2 ∧ F64_2*M64_2≤e64_2^2 := by
  norm_num [e64_2, F64_2, M64_2]
def e64_4 : ℚ := 2767156741/100000000000
theorem root64_4 : 0<e64_4 ∧ F64_4*M64_4≤e64_4^2 := by
  norm_num [e64_4, F64_4, M64_4]
def e64_6 : ℚ := 3381167957/250000000000
theorem root64_6 : 0<e64_6 ∧ F64_6*M64_6≤e64_6^2 := by
  norm_num [e64_6, F64_6, M64_6, ell64_6]
theorem epsilon64 : e64_2+e64_4+e64_6 < 22661/500000 := by
  norm_num [e64_2, e64_4, e64_6]
def meanCoefficient64 : ℚ := 189124403700384563131165281848080399637332351/311159206171855630000323559424000000000000000000
theorem mean64 : M64_0*meanCoefficient64 < 1/1250 := by
  norm_num [M64_0, meanCoefficient64]

end BilayerDressed.ScalarTrial
