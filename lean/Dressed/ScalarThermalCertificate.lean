import Dressed.ScalarWarmupCertificate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Fixed rational thermal and Temple scalar checks. Real exponential lower
bounds and actual-Hamiltonian spectral inputs are separate obligations. -/
namespace BilayerDressed.ScalarThermal
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def taylor50 (x : ℚ) : ℚ := ∑ k ∈ Finset.range 51, x^k/(k.factorial : ℚ)
def a : ℚ := 387/500
def den16 : ℚ := 588758821/787000000
def den32 : ℚ := 568075073/787000000
def den64 : ℚ := 5263369/7870000

theorem denominator_identities :
    den16=a-750*16/78700-(-507/4000)-167/1000000 ∧
    den32=a-750*32/78700-(-81/320)-346/1000000 ∧
    den64=a-750*64/78700-(-1011/2000)-800/1000000 := by
  norm_num [den16, den32, den64, a]
theorem denominators_pos : 0<den16 ∧ 0<den32 ∧ 0<den64 := by
  norm_num [den16, den32, den64]

theorem taylor_a : (238947:ℚ)<taylor50 (16*a) := by
  norm_num [taylor50, a, Finset.sum_range_succ, Nat.factorial]
theorem taylor_16 : (157894:ℚ)<taylor50 (16*den16) := by
  norm_num [taylor50, den16, Finset.sum_range_succ, Nat.factorial]
theorem taylor_32 : (103691:ℚ)<taylor50 (16*den32) := by
  norm_num [taylor50, den32, Finset.sum_range_succ, Nat.factorial]
theorem taylor_64 : (44383:ℚ)<taylor50 (16*den64) := by
  norm_num [taylor50, den64, Finset.sum_range_succ, Nat.factorial]

theorem tail16 : (48:ℚ)/157894/(1-1/238947)^49 < 305/1000000 := by norm_num
theorem tail32 : (96:ℚ)/103691/(1-1/238947)^97 < 927/1000000 := by norm_num
theorem tail64 : (192:ℚ)/44383/(1-1/238947)^193 < 4331/1000000 := by norm_num

theorem dx_identity : ScalarWarmup.dx = (3:ℚ)/8000+346/1000000+
    2*(167/1000000)+2*(10982/1000000)^2/den16 := by
  norm_num [ScalarWarmup.dx, den16]
theorem dy_identity : ScalarWarmup.dy = (3:ℚ)/4000+800/1000000+
    2*(346/1000000)+2*(20172/1000000)^2/den32 := by
  norm_num [ScalarWarmup.dy, den32]
end BilayerDressed.ScalarThermal
