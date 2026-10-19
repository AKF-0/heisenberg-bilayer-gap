import Dressed.PhysicalReferencePointOne

/-! Finite-product thermal comparison reduced to a single exponential.
The estimate is on the already proved finite occupation reference, not an
infinite Fock partition function. Exactly one ground contribution was removed
before this scalar estimate is applied. -/
noncomputable section
namespace BilayerDressed
open BilayerGap

/-- Elementary finite Bernoulli bound, including zero power. -/
theorem one_sub_one_sub_pow_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (p : ℕ) :
    1-(1-q)^p ≤ (p:ℝ)*q := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : (1-q)^p ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp hq0
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A conservative rational envelope matching the fixed scalar certificates. -/
theorem inverse_geometric_power_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) :
    ((1-q)⁻¹)^p-1 ≤ (p:ℝ)*q/(1-q)^(p+1) := by
  have ht : 0 < 1-q := by linarith
  have hb := one_sub_one_sub_pow_le q hq0 hq1.le p
  have he : ((1-q)⁻¹)^p-1 = (1-(1-q)^p)/(1-q)^p := by
    rw [inv_pow]
    field_simp [ne_of_gt ht]
  rw [he]
  have hn : 0 ≤ (p:ℝ)*q := mul_nonneg (Nat.cast_nonneg _) hq0
  calc
    _ ≤ (p:ℝ)*q/(1-q)^p := div_le_div_of_nonneg_right hb (pow_nonneg ht.le _)
    _ ≤ _ := div_le_div_of_nonneg_left hn (pow_pos ht _)
      (by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg ht.le _) (by linarith))

/-- Ground shift and frequency combine into the actual nonlowest denominator. -/
theorem exponential_geometric_tail_le (p : ℕ) (β a c U : ℝ)
    (hβ : 0 < β) (ha : 0 < a) :
    Real.exp (β*(U-c))*(((1-Real.exp (-β*a))⁻¹)^p-1) ≤
      (p:ℝ)*Real.exp (-β*(a+c-U))/(1-Real.exp (-β*a))^(p+1) := by
  have hq : Real.exp (-β*a) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hh := mul_le_mul_of_nonneg_left
    (inverse_geometric_power_tail (Real.exp (-β*a)) (Real.exp_nonneg _) hq p)
    (Real.exp_nonneg (β*(U-c)))
  apply hh.trans_eq
  have he : Real.exp (β*(U-c))*Real.exp (-β*a) = Real.exp (-β*(a+c-U)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = (p:ℝ)*(Real.exp (β*(U-c))*Real.exp (-β*a))/
        (1-Real.exp (-β*a))^(p+1) := by ring
    _ = _ := by rw [he]

/-- Actual finite-volume thermal tail with no remaining operator or spectral
reference premise; only the genuine ground-energy upper bound is supplied. -/
theorem physical_thermal_denominator_bound
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U β : ℝ) (hβ : 0 < β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β-1 ≤
      (3*((2*n)*(2*m)):ℝ)*Real.exp (-β*(387/500-750*((2*n)*(2*m):ℝ)*g^2/787-U))/
        (1-Real.exp (-β*(387/500)))^(3*((2*n)*(2*m))+1) := by
  have hh := PhysicalReferencePointOne.fullHamiltonian_thermal_fixed_geometric
    n m hn hm g hg hgmax U β hβ hU
  have he := exponential_geometric_tail_le (3*((2*n)*(2*m))) β (387/500)
    (-750*((2*n)*(2*m):ℝ)*g^2/787) U hβ (by norm_num)
  apply hh.trans
  convert he using 1 <;> push_cast <;> ring_nf

/-- A scalar lower denominator can be substituted on the whole coupling interval. -/
theorem physical_thermal_fixed_denominator_bound
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (g : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (U β d : ℝ) (hβ : 0 < β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U)
    (hd : d ≤ 387/500-750*((2*n)*(2*m):ℝ)*g^2/787-U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β-1 ≤
      (3*((2*n)*(2*m)):ℝ)*Real.exp (-β*d)/
        (1-Real.exp (-β*(387/500)))^(3*((2*n)*(2*m))+1) := by
  have hh := physical_thermal_denominator_bound n m hn hm g hg hgmax U β hβ hU
  have hq : Real.exp (-β*(387/500)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  have he : Real.exp (-β*(387/500-750*((2*n)*(2*m):ℝ)*g^2/787-U)) ≤
      Real.exp (-β*d) := Real.exp_le_exp.mpr (by nlinarith)
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by positivity))
    (pow_nonneg (by linarith) _))

end BilayerDressed
