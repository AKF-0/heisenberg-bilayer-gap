import Dressed.QuadraticResidualKernel
import Dressed.GlobalResidualDegrees
import Dressed.GlobalResidualSplit

/-! Exact finite algebraic regrouping from literal bond terms to the compact
quadratic coefficient. All polynomial identities occur inside a commutative
real algebra, later instantiated to the actual creation-only subalgebra. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuadraticRegrouping
variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R] [Algebra ℝ R]

/-- Bilinear coefficient sum, without a hidden half. -/
def bilinear (M : Matrix V V ℝ) (x y : V → R) : R :=
  ∑ i, ∑ j, M i j • (x i*y j)

def field (K : Matrix V V ℝ) (x : V → R) (i : V) : R :=
  ∑ j, K i j • x j

 theorem bilinear_add (M N : Matrix V V ℝ) (x y : V → R) :
    bilinear (M+N) x y=bilinear M x y+bilinear N x y := by
  simp [bilinear, add_smul, Finset.sum_add_distrib]

 theorem bilinear_sub (M N : Matrix V V ℝ) (x y : V → R) :
    bilinear (M-N) x y=bilinear M x y-bilinear N x y := by
  simp [bilinear, sub_smul, Finset.sum_sub_distrib]

 theorem bilinear_smul (a : ℝ) (M : Matrix V V ℝ) (x y : V → R) :
    bilinear (a • M) x y=a • bilinear M x y := by
  simp [bilinear, mul_smul, Finset.smul_sum]

 theorem bilinear_transpose (M : Matrix V V ℝ) (x y : V → R) :
    bilinear M.transpose x y=bilinear M y x := by
  simp only [bilinear, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

 theorem bilinear_field_right (M K : Matrix V V ℝ) (x y : V → R) :
    bilinear M x (field K y)=bilinear (M*K) x y := by
  simp only [bilinear, field, Matrix.mul_apply, Finset.mul_sum,
    Finset.smul_sum, mul_smul_comm, smul_smul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

 theorem bilinear_field_left (M K : Matrix V V ℝ) (x y : V → R) :
    bilinear M (field K x) y=bilinear (K.transpose*M) x y := by
  calc
    _ = bilinear M.transpose y (field K x) := (bilinear_transpose M y (field K x)).symm
    _ = bilinear (M.transpose*K) y x := bilinear_field_right _ _ _ _
    _ = bilinear (M.transpose*K).transpose x y := (bilinear_transpose _ x y).symm
    _ = _ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]

 theorem bilinear_fields (M K L : Matrix V V ℝ) (x y : V → R) :
    bilinear M (field K x) (field L y)=bilinear (K.transpose*M*L) x y := by
  rw [bilinear_field_left, bilinear_field_right]

 theorem bilinear_offDiagonal (M : Matrix V V ℝ) (x : V → R)
    (hx : ∀ i, x i*x i=0) : bilinear (offDiagonal M) x x=bilinear M x x := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [offDiagonal,hx]
  · simp [offDiagonal,hij]

/-- An exact one-color expansion; the only simplification is hard-core x²=y²=0. -/
 theorem local_full_field (x y A B k : R) (hx : x*x=0) (hy : y*y=0) :
    A*B+x*(B-3*k*A)+y*(A-3*k*B)+(1-2*k-3*k^2)*(x*y) =
      (A+k*y)*(B+k*x)+x*(B+k*x)+y*(A+k*y)-
        4*k*(x*(A+k*y)+y*(B+k*x))+(1-2*k+4*k^2)*(x*y) := by
  have hx2 : x^2=0 := by simpa only [pow_two] using hx
  have hy2 : y^2=0 := by simpa only [pow_two] using hy
  ring_nf
  simp [hx2,hy2]

/-- A diagonal row weight is exactly the corresponding diagonal matrix product. -/
 theorem weighted_field (z : V → ℝ) (K : Matrix V V ℝ) (x : V → R) :
    (∑ i, z i • (x i*field K x i)) = bilinear (Matrix.diagonal z*K) x x := by
  simp [bilinear, field, Matrix.diagonal_mul, Finset.mul_sum, Finset.smul_sum,
    mul_smul_comm, smul_smul]

 theorem weighted_row (D K : Matrix V V ℝ) (f : V → R) :
    (∑ i,∑ j,D i j • (K i j • f i)) =
      ∑ i,(∑ j,D i j*K i j) • f i := by
  simp only [smul_smul, Finset.sum_smul]

 theorem weighted_other_row (D K : Matrix V V ℝ)
    (hD : D.transpose=D) (hK : K.transpose=K) (f : V → R) :
    (∑ i,∑ j,D i j • (K i j • f j)) =
      ∑ i,(∑ j,D i j*K i j) • f i := by
  rw [Finset.sum_comm]
  have hd (i j : V) : D j i=D i j := congrFun (congrFun hD i) j
  have hk (i j : V) : K j i=K i j := congrFun (congrFun hK i) j
  simp only [hd,hk,smul_smul,Finset.sum_smul]

/-- Every contraction used here is the actual diagonal of D K. -/
 theorem row_contraction_eq (D K : Matrix V V ℝ) (hK : K.transpose=K) (i : V) :
    (∑ j,D i j*K i j)=(D*K) i i := by
  apply Finset.sum_congr rfl
  intro j _
  change D i j*K i j=D i j*K j i
  rw [show K j i=K i j from congrFun (congrFun hK i) j]

/-- Expanded full-row bond expression for one color. -/
def fullBond (K : Matrix V V ℝ) (x : V → R) (i j : V) : R :=
  field K x i*field K x j+x i*field K x j+x j*field K x i-
    (4*K i j) • (x i*field K x i+x j*field K x j)+
    (1-2*K i j+4*(K i j)^2) • (x i*x j)

/-- Exact regrouping of all ordered bond incidences for one color. -/
 theorem fullBond_sum (D K : Matrix V V ℝ) (hD : D.transpose=D) (hK : K.transpose=K)
    (x : V → R) :
    (∑ i,∑ j,D i j • fullBond K x i j) =
      bilinear (K*D*K) x x + bilinear (D*K) x x + bilinear (K*D) x x -
        (4 : ℝ) • (bilinear (Matrix.diagonal (fun i => (D*K) i i)*K) x x +
          bilinear (K*Matrix.diagonal (fun i => (D*K) i i)) x x) +
        bilinear (fun i j => D i j*(1-2*K i j+4*(K i j)^2)) x x := by
  have hs (i j : V) : D i j • fullBond K x i j =
      D i j • (field K x i*field K x j)+D i j • (x i*field K x j)+
      D i j • (x j*field K x i)-
      (4 : ℝ) • (D i j • (K i j • (x i*field K x i))+
        D i j • (K i j • (x j*field K x j)))+
      (D i j*(1-2*K i j+4*(K i j)^2)) • (x i*x j) := by
    simp only [fullBond,smul_add,smul_sub,smul_smul]
    module
  simp_rw [hs]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.smul_sum]
  have hswap : (∑ i,∑ j,D i j • (x j*field K x i))=bilinear D (field K x) x := by
    simp only [bilinear,mul_comm]
  change bilinear D (field K x) (field K x)+bilinear D x (field K x)+
    (∑ i,∑ j,D i j • (x j*field K x i))-
    (4 : ℝ) • ((∑ i,∑ j,D i j • (K i j • (x i*field K x i)))+
      (∑ i,∑ j,D i j • (K i j • (x j*field K x j))))+_=_
  rw [hswap,bilinear_fields,bilinear_field_right,bilinear_field_left,hK,
    weighted_row,weighted_other_row D K hD hK]
  simp_rw [row_contraction_eq D K hK]
  rw [weighted_field]
  have hz : bilinear (K*Matrix.diagonal (fun i => (D*K) i i)) x x =
      bilinear (Matrix.diagonal (fun i => (D*K) i i)*K) x x := by
    rw [← bilinear_transpose,Matrix.transpose_mul,Matrix.diagonal_transpose,hK]
  rw [hz]
  rfl

/-- Generic compact coefficient with all diagonal-irrelevant terms removed. -/
def compactCoefficient (D K : Matrix V V ℝ) (g : ℝ) : Matrix V V ℝ :=
  (2 : ℝ) • K+(g/2) • D+(g/2) • offDiagonal (D*K+K*D)-
    g • (show Matrix V V ℝ from fun i j => D i j*K i j)+
    quadraticNonlinear D K (Matrix.diagonal (fun i => (D*K) i i)) g

 theorem one_color_compact (D K : Matrix V V ℝ) (hD : D.transpose=D) (hK : K.transpose=K)
    (x : V → R) (hx : ∀ i,x i*x i=0) (g : ℝ) :
    bilinear K x x+(g/4) • (∑ i,∑ j,D i j • fullBond K x i j) =
      (1/2 : ℝ) • bilinear (compactCoefficient D K g) x x := by
  rw [fullBond_sum D K hD hK]
  have hp : (show Matrix V V ℝ from fun i j => D i j*(1-2*K i j+4*(K i j)^2)) =
      D-(2 : ℝ) • (show Matrix V V ℝ from fun i j => D i j*K i j)+
        (4 : ℝ) • (show Matrix V V ℝ from fun i j => D i j*K i j*K i j) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [hp]
  simp only [compactCoefficient,quadraticNonlinear,bilinear_add,bilinear_sub,
    bilinear_smul,bilinear_offDiagonal _ x hx]
  module

 theorem compactCoefficient_eq (G : FourRegularData V) (g : ℝ) :
    compactCoefficient G.adjacency (G.kernel g) g=G.quadraticResidual g := rfl

 theorem field_eq_outside_left (c : V → Fin 3 → R) (K : Matrix V V ℝ)
    (hdiag : ∀ i,K i i=0) (u v : V) (huv : u≠v) (α : Fin 3) :
    field K (fun w => c w α) u =
      GlobalResidual.outsideField c K u v u α+(algebraMap ℝ R (K u v))*c v α := by
  rw [field,GlobalResidual.sum_two_sites u v huv,hdiag,zero_smul,zero_add]
  rw [Algebra.smul_def]
  exact add_comm _ _

 theorem field_eq_outside_right (c : V → Fin 3 → R) (K : Matrix V V ℝ)
    (hK : K.transpose=K) (hdiag : ∀ i,K i i=0) (u v : V) (huv : u≠v) (α : Fin 3) :
    field K (fun w => c w α) v =
      GlobalResidual.outsideField c K u v v α+(algebraMap ℝ R (K u v))*c u α := by
  rw [field,GlobalResidual.sum_two_sites u v huv,hdiag,zero_smul,add_zero]
  have hk : K v u=K u v := congrFun (congrFun hK u) v
  rw [hk,Algebra.smul_def]
  exact add_comm _ _

/-- The literal outside-row bond polynomial is exactly the full-row expression. -/
 theorem bondR2_eq_fullBond (c : V → Fin 3 → R) (hc : ∀ u α,c u α*c u α=0)
    (K : Matrix V V ℝ) (hK : K.transpose=K) (hdiag : ∀ i,K i i=0)
    (u v : V) (huv : u≠v) :
    GlobalResidual.bondR2 (c u) (c v)
      (GlobalResidual.outsideField c K u v u) (GlobalResidual.outsideField c K u v v)
      (algebraMap ℝ R (K u v)) = ∑ α, fullBond K (fun w => c w α) u v := by
  simp only [GlobalResidual.bondR2,LocalBond.dot,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [fullBond,field_eq_outside_left c K hdiag u v huv α,
    field_eq_outside_right c K hK hdiag u v huv α]
  simp only [Algebra.smul_def,map_sub,map_add,map_mul,map_pow,map_ofNat,map_one]
  exact local_full_field _ _ _ _ _ (hc u α) (hc v α)

end BilayerDressed.QuadraticRegrouping
