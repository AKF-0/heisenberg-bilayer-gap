import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Cast.Order

/-! Kernel-checked fixed rational scalar certificate for the cubic g ≤ 1/10 seeds.
This file proves arithmetic only. Actual Hamiltonian seed bounds and recurrence
interpretation are separate obligations. No JSON data are hypotheses. -/
namespace BilayerDressed.ScalarWarmup
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def update (a b c : ℚ) : ℚ :=
  let u := 1-(1-a)^4*(1-b)^2*(1-c)
  u^2/(2*(1-u)^2)

def lowerExp3 (z : ℚ) : ℚ := 1-z+z^2/2-z^3/6

def a0 : ℚ := 11197089/500000000
def b0 : ℚ := 27119173/500000000
def c0 : ℚ := 8606051/1000000000
theorem bounds0 : 0<a0 ∧ a0<1 ∧ 0<b0 ∧ b0<1 ∧ 0<c0 ∧ c0<1 := by
  norm_num [a0, b0, c0]

def a1 : ℚ := 5504909/200000000
def b1 : ℚ := 11833497/250000000
def c1 : ℚ := 11099297/1000000000
theorem bounds1 : 0<a1 ∧ a1<1 ∧ 0<b1 ∧ b1<1 ∧ 0<c1 ∧ c1<1 := by
  norm_num [a1, b1, c1]

def a2 : ℚ := 30210971/1000000000
def b2 : ℚ := 19618453/500000000
def c2 : ℚ := 1545013/125000000
theorem bounds2 : 0<a2 ∧ a2<1 ∧ 0<b2 ∧ b2<1 ∧ 0<c2 ∧ c2<1 := by
  norm_num [a2, b2, c2]

def a3 : ℚ := 14413023/500000000
def b3 : ℚ := 28539483/1000000000
def c3 : ℚ := 10813383/1000000000
theorem bounds3 : 0<a3 ∧ a3<1 ∧ 0<b3 ∧ b3<1 ∧ 0<c3 ∧ c3<1 := by
  norm_num [a3, b3, c3]

def a4 : ℚ := 1302511/62500000
def b4 : ℚ := 14774239/1000000000
def c4 : ℚ := 1397021/250000000
theorem bounds4 : 0<a4 ∧ a4<1 ∧ 0<b4 ∧ b4<1 ∧ 0<c4 ∧ c4<1 := by
  norm_num [a4, b4, c4]

def a5 : ℚ := 8072381/1000000000
def b5 : ℚ := 3365491/1000000000
def c5 : ℚ := 919811/1000000000
theorem bounds5 : 0<a5 ∧ a5<1 ∧ 0<b5 ∧ b5<1 ∧ 0<c5 ∧ c5<1 := by
  norm_num [a5, b5, c5]

def a6 : ℚ := 167259/200000000
def b6 : ℚ := 132733/1000000000
def c6 : ℚ := 15137/1000000000
theorem bounds6 : 0<a6 ∧ a6<1 ∧ 0<b6 ∧ b6<1 ∧ 0<c6 ∧ c6<1 := by
  norm_num [a6, b6, c6]

theorem step1_a : update a0 b0 c0 < a1 := by
  norm_num [update, a0, b0, c0, a1, b1, c1]

theorem step1_b : update b0 c0 a1 < b1 := by
  norm_num [update, a0, b0, c0, a1, b1, c1]

theorem step1_c : update c0 a1 b1 < c1 := by
  norm_num [update, a0, b0, c0, a1, b1, c1]

theorem step2_a : update a1 b1 c1 < a2 := by
  norm_num [update, a1, b1, c1, a2, b2, c2]

theorem step2_b : update b1 c1 a2 < b2 := by
  norm_num [update, a1, b1, c1, a2, b2, c2]

theorem step2_c : update c1 a2 b2 < c2 := by
  norm_num [update, a1, b1, c1, a2, b2, c2]

theorem step3_a : update a2 b2 c2 < a3 := by
  norm_num [update, a2, b2, c2, a3, b3, c3]

theorem step3_b : update b2 c2 a3 < b3 := by
  norm_num [update, a2, b2, c2, a3, b3, c3]

theorem step3_c : update c2 a3 b3 < c3 := by
  norm_num [update, a2, b2, c2, a3, b3, c3]

theorem step4_a : update a3 b3 c3 < a4 := by
  norm_num [update, a3, b3, c3, a4, b4, c4]

theorem step4_b : update b3 c3 a4 < b4 := by
  norm_num [update, a3, b3, c3, a4, b4, c4]

theorem step4_c : update c3 a4 b4 < c4 := by
  norm_num [update, a3, b3, c3, a4, b4, c4]

theorem step5_a : update a4 b4 c4 < a5 := by
  norm_num [update, a4, b4, c4, a5, b5, c5]

theorem step5_b : update b4 c4 a5 < b5 := by
  norm_num [update, a4, b4, c4, a5, b5, c5]

theorem step5_c : update c4 a5 b5 < c5 := by
  norm_num [update, a4, b4, c4, a5, b5, c5]

theorem step6_a : update a5 b5 c5 < a6 := by
  norm_num [update, a5, b5, c5, a6, b6, c6]

theorem step6_b : update b5 c5 a6 < b6 := by
  norm_num [update, a5, b5, c5, a6, b6, c6]

theorem step6_c : update c5 a6 b6 < c6 := by
  norm_num [update, a5, b5, c5, a6, b6, c6]

theorem final_bounds : a6 < 1/400 ∧ b6 < 1/400 ∧ c6 < 1/400 := by
  norm_num [a6, b6, c6]

def dx : ℚ := 810971762131/588758821000000
def dy : ℚ := 957049999441/284037536500000
def Q0 : ℚ := 200061/200000
def Q1 : ℚ := 1000927/1000000
def Q2 : ℚ := 1004331/1000000
theorem seed_scalar_signs :
    0<dx ∧ 0<dy ∧ 1<Q0 ∧ 1<Q1 ∧ 1<Q2 ∧
    0<lowerExp3 (16*dx) ∧ 0<lowerExp3 (16*dy) := by
  norm_num [dx, dy, Q0, Q1, Q2, lowerExp3]

theorem initial_a : 1-lowerExp3 (16*dx)/Q0^2 < a0 := by
  norm_num [lowerExp3, dx, Q0, a0]
theorem initial_b : 1-lowerExp3 (16*dy)/Q1^2 < b0 := by
  norm_num [lowerExp3, dy, Q1, b0]
theorem initial_c : 1-1/Q2^2 < c0 := by
  norm_num [Q2, c0]

def commonCoefficient (u : ℚ) : ℚ :=
  (((1-u)^1)⁻¹+((1-u)^2)⁻¹+((1-u)^3)⁻¹+((1-u)^4)⁻¹+
   ((1-u)^5)⁻¹+((1-u)^6)⁻¹+((1-u)^7)⁻¹)^2/2

theorem common_coefficient : commonCoefficient (1/400) < 26 := by
  norm_num [commonCoefficient]
theorem common_parameters :
    (26:ℚ)*(1/400)=13/200 ∧ (13:ℚ)/200<1 ∧
    (7:ℚ)<26*(1-7*(1/400)) ∧ (1:ℚ)/400<1/14 := by norm_num

theorem final_coordinates : (4:ℕ)*2^6=256 ∧ (16:ℕ)*2^6=1024 := by norm_num
end BilayerDressed.ScalarWarmup
