import Dressed.QuarticIntegerArrays

/-! Exact signed Gram-polynomial arithmetic for integer coefficient tables.
The computational convolution has only eleven summands per output coefficient. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerNorm
open QuarticIntegerArrays
set_option maxHeartbeats 1000000

abbrev NormCoefficients := Fin 21 → ℤ

def evaluate (a : NormCoefficients) (g : ℝ) : ℝ := ∑ i,(a i : ℝ)*g^(i:ℕ)

def convolution (a b : Coefficients) (k : Fin 21) : ℤ :=
  ∑ i : Fin 11, if h : (i:ℕ)≤k.val ∧ k.val-i.val<11
    then a i*b ⟨k.val-i.val,h.2⟩ else 0

theorem convolution_eq_double (a b : Coefficients) (k : Fin 21) :
    convolution a b k = ∑ i : Fin 11,∑ j : Fin 11,
      if i.val+j.val=k.val then a i*b j else 0 := by
  unfold convolution
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · let j : Fin 11 := ⟨k.val-i.val,h.2⟩
    have he (x : Fin 11) : i.val+x.val=k.val ↔ x=j := by
      apply Iff.intro
      · intro hx
        apply Fin.ext
        dsimp [j]
        omega
      · rintro rfl
        dsimp [j]
        omega
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl
  · symm
    apply Finset.sum_eq_zero
    intro j _
    have hn : ¬i.val+j.val=k.val := by
      intro he
      apply h
      constructor <;> omega
    simp [hn]

theorem convolution_evaluate (a b : Coefficients) (g : ℝ) :
    evaluate (convolution a b) g=QuarticIntegerArrays.evaluate a g*
      QuarticIntegerArrays.evaluate b g := by
  unfold evaluate
  simp_rw [convolution_eq_double]
  simp only [Int.cast_sum,apply_ite,Int.cast_mul,Int.cast_zero,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 21)))
    (t := (Finset.univ : Finset (Fin 11)))]
  have ht (i j : Fin 11) :
      (∑ k : Fin 21,(if i.val+j.val=k.val then (a i : ℝ)*(b j : ℝ) else 0)*g^k.val)=
        ((a i : ℝ)*g^i.val)*((b j : ℝ)*g^j.val) := by
    let ij : Fin 21 := ⟨i.val+j.val,by omega⟩
    have he (k : Fin 21) : i.val+j.val=k.val ↔ k=ij := by
      change ij.val=k.val ↔ k=ij
      simp only [Fin.val_inj,eq_comm]
    simp only [he,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    dsimp only [ij]
    rw [pow_add]
    ring
  simp_rw [ht]
  rw [←Finset.sum_mul_sum]
  rfl

def gram (a : Fin 3 → Coefficients) : NormCoefficients :=
  6 • (∑ m,convolution (a m) (a m)) +
    3 • convolution (∑ m,a m) (∑ m,a m)

theorem evaluate_add (a b : NormCoefficients) (g : ℝ) :
    evaluate (a+b) g=evaluate a g+evaluate b g := by
  simp [evaluate,Int.cast_add,add_mul,Finset.sum_add_distrib]

theorem evaluate_nsmul (z : ℕ) (a : NormCoefficients) (g : ℝ) :
    evaluate (z • a) g=(z:ℝ)*evaluate a g := by
  simp [evaluate,mul_assoc,Finset.mul_sum]

theorem evaluate_sum {I : Type*} (s : Finset I) (a : I → NormCoefficients) (g : ℝ) :
    evaluate (∑ j∈s,a j) g=∑ j∈s,evaluate (a j) g := by
  simp only [evaluate,Finset.sum_apply,Int.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_evaluate (a : Fin 3 → Coefficients) (g : ℝ) :
    evaluate (gram a) g=6*(∑ m,(QuarticIntegerArrays.evaluate (a m) g)^2)+
      3*(∑ m,QuarticIntegerArrays.evaluate (a m) g)^2 := by
  rw [gram,evaluate_add,evaluate_nsmul,evaluate_nsmul,evaluate_sum]
  simp_rw [convolution_evaluate,QuarticIntegerArrays.evaluate_sum]
  simp only [Nat.cast_ofNat,pow_two]

/-- Denominator normalization retains both terms of the exact 9/3 Gram matrix. -/
theorem gram_evaluate_div (a : Fin 3 → Coefficients) (g d : ℝ) :
    evaluate (gram a) g/d^2=
      6*(∑ m,(QuarticIntegerArrays.evaluate (a m) g/d)^2)+
      3*(∑ m,QuarticIntegerArrays.evaluate (a m) g/d)^2 := by
  rw [gram_evaluate]
  simp_rw [div_pow]
  rw [←Finset.sum_div,←Finset.sum_div,div_pow]
  ring

end BilayerDressed.QuarticIntegerNorm
