import Dressed.CubicResidualPolynomial

/-! Computable rational coefficient arrays for the exact rooted cubic residual. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualCoefficients
open BilayerGap BilayerDressed.SeedGraphs BilayerDressed.CubicSeedChecks
open BilayerDressed.CubicResidualPair
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

 def k1 (q : Torus.Vertex n m) : ℚ := -(adjacencyNat n m 0 q : ℚ)/4
 def k2 (q : Torus.Vertex n m) : ℚ :=
   ((offWalk2 n m 0 q : ℚ)-(adjacencyNat n m 0 q : ℚ))/8
 def k3 (q : Torus.Vertex n m) : ℚ :=
   -(5*(walk3 n m 0 q : ℚ)-4*(offWalk2 n m 0 q : ℚ)-40*(adjacencyNat n m 0 q : ℚ))/64

 def neighborSum (f : Torus.Vertex n m → ℚ) (q : Torus.Vertex n m) : ℚ :=
   ∑ r,f r*(adjacencyNat n m r q : ℚ)
 def b1 := neighborSum n m (k1 n m)
 def b2 := neighborSum n m (k2 n m)
 def b3 := neighborSum n m (k3 n m)

 def conv (f h : Torus.Vertex n m → ℚ) (q : Torus.Vertex n m) : ℚ := ∑ r,f r*h (q-r)
 def c2 := conv n m (k1 n m) (b1 n m)
 def c3 (q : Torus.Vertex n m) : ℚ :=
   conv n m (k1 n m) (b2 n m) q+conv n m (k2 n m) (b1 n m) q
 def c4 (q : Torus.Vertex n m) : ℚ :=
   conv n m (k1 n m) (b3 n m) q+conv n m (k2 n m) (b2 n m) q+
     conv n m (k3 n m) (b1 n m) q
 def c5 (q : Torus.Vertex n m) : ℚ :=
   conv n m (k2 n m) (b3 n m) q+conv n m (k3 n m) (b2 n m) q
 def c6 := conv n m (k3 n m) (b3 n m)

 theorem rootKernel_coeff (g : ℝ) (q : Torus.Vertex n m) :
    rootKernel n m g q=(k1 n m q : ℝ)*g+(k2 n m q : ℝ)*g^2+(k3 n m q : ℝ)*g^3 := by
  simp only [rootKernel,k1,k2,k3,Rat.cast_div,Rat.cast_neg,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_natCast,Rat.cast_ofNat]
  ring

 theorem sum_kernel_coeff (g : ℝ) (q : Torus.Vertex n m) :
    rootDK n m g q=(b1 n m q : ℝ)*g+(b2 n m q : ℝ)*g^2+(b3 n m q : ℝ)*g^3 := by
  simp only [rootDK,rootKernel_coeff,b1,b2,b3,neighborSum,Rat.cast_sum,Rat.cast_mul,
    Rat.cast_natCast,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

 theorem convolution_coeff (g : ℝ) (q : Torus.Vertex n m) :
    rootKDK n m g q=(c2 n m q : ℝ)*g^2+(c3 n m q : ℝ)*g^3+
      (c4 n m q : ℝ)*g^4+(c5 n m q : ℝ)*g^5+(c6 n m q : ℝ)*g^6 := by
  simp only [rootKDK,rootKernel_coeff,sum_kernel_coeff,c2,c3,c4,c5,c6,conv,
    Rat.cast_add,Rat.cast_sum,Rat.cast_mul,add_mul,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- All coefficients are rational arithmetic over the actual finite rung graph. -/
def coeff (q : Torus.Vertex n m) : Fin 8 → ℚ :=
  if q=0 then 0 else
  let a := k1 n m q; let b := k2 n m q; let c := k3 n m q
  let d := (adjacencyNat n m 0 q : ℚ)
  let x := b1 n m 0; let y := b2 n m 0; let z := b3 n m 0
  ![0,2*a+d/2,2*b+b1 n m q-d*a,
    2*c+b2 n m q-d*b+c2 n m q/2-4*x*a+2*d*a^2,
    b3 n m q-d*c+c3 n m q/2-4*(x*b+y*a)+4*d*a*b,
    c4 n m q/2-4*(x*c+y*b+z*a)+2*d*(2*a*c+b^2),
    c5 n m q/2-4*(y*c+z*b)+4*d*b*c,
    c6 n m q/2-4*z*c+2*d*c^2]

/-- Horner-free finite evaluation, convenient for exact coefficient certificates. -/
def evalCoeff {d : ℕ} (a : Fin d → ℚ) (g : ℝ) : ℝ :=
  ∑ i,(a i : ℝ)*g^(i : ℕ)

 theorem rootResidual_coeff (g : ℝ) (q : Torus.Vertex n m) :
    rootResidual n m g q=evalCoeff (coeff n m q) g := by
  by_cases hq : q=0
  · simp [rootResidual,coeff,hq,evalCoeff]
  · simp only [rootResidual,if_neg hq,rootKernel_coeff,sum_kernel_coeff,convolution_coeff,
      coeff,evalCoeff,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Rat.cast_add,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_zero]
    norm_num only [Fin.sum_univ_zero] 
    ring

/-- Exact convolution of finite coefficient arrays, with no truncated tail. -/
def squareCoeff (a : Fin 8 → ℚ) (k : Fin 15) : ℚ :=
  ∑ i : Fin 8,∑ j : Fin 8,if (i : ℕ)+(j : ℕ)=(k : ℕ) then a i*a j else 0

 theorem squareCoeff_evaluate (a : Fin 8 → ℚ) (g : ℝ) :
    evalCoeff (squareCoeff a) g=(evalCoeff a g)^2 := by
  unfold evalCoeff squareCoeff
  simp only [Rat.cast_sum,apply_ite,Rat.cast_mul,Rat.cast_zero,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 15)))
    (t := (Finset.univ : Finset (Fin 8)))]
  have ht (i j : Fin 8) :
      (∑ k : Fin 15,(if (i : ℕ)+(j : ℕ)=(k : ℕ) then (a i : ℝ)*(a j : ℝ) else 0)*g^(k : ℕ))=
        ((a i : ℝ)*g^(i : ℕ))*((a j : ℝ)*g^(j : ℕ)) := by
    let ij : Fin 15 := ⟨(i : ℕ)+(j : ℕ),by omega⟩
    have he (k : Fin 15) : ((i : ℕ)+(j : ℕ)=(k : ℕ)) ↔ k=ij := by
      change ij.val=k.val ↔ k=ij
      simp only [Fin.val_inj,eq_comm]
    simp only [he,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    dsimp only [ij]
    rw [pow_add]
    ring
  simp_rw [ht]
  rw [←Finset.sum_mul_sum]
  ring

 def normCoeff (k : Fin 15) : ℚ :=
  (3*((2*n)*(2*m) : ℚ)/2)*∑ q,squareCoeff (coeff n m q) k

 theorem normCoeff_evaluate (g : ℝ) :
    evalCoeff (normCoeff n m) g=
      (3*((2*n)*(2*m) : ℝ)/2)*∑ q,(rootResidual n m g q)^2 := by
  simp only [evalCoeff,normCoeff,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,
    Rat.cast_sum,mul_assoc,←Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  change evalCoeff (squareCoeff (coeff n m q)) g=(rootResidual n m g q)^2
  rw [squareCoeff_evaluate,rootResidual_coeff]

end BilayerDressed.CubicResidualCoefficients
