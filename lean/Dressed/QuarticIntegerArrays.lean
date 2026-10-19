import Dressed.CubicResidualCoefficients

/-! Fixed integer coefficient arrays for actual cubic-kernel quartic arithmetic.
The arrays retain signed coefficients. The pair terms carry the extra factor64
needed to put all ordered terms over64^3; the outer g/2 is represented by the
shifted pair/triple arrays and the eventual denominator524288. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerArrays
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
set_option maxHeartbeats 800000

abbrev KernelCoefficients := Fin 3 → ℤ
abbrev Coefficients := Fin 11 → ℤ

def evaluateKernel (a : KernelCoefficients) (g : ℝ) : ℝ :=
  (a 0 : ℝ)*g+(a 1 : ℝ)*g^2+(a 2 : ℝ)*g^3

def evaluate (a : Coefficients) (g : ℝ) : ℝ := ∑ i,(a i : ℝ)*g^(i : ℕ)

def scale (z : ℤ) (a : Coefficients) : Coefficients := fun i => z*a i

@[simp] theorem evaluate_zero (g : ℝ) : evaluate 0 g=0 := by simp [evaluate]

theorem evaluate_add (a b : Coefficients) (g : ℝ) :
    evaluate (a+b) g=evaluate a g+evaluate b g := by
  simp [evaluate,Int.cast_add,add_mul,Finset.sum_add_distrib]

theorem evaluate_neg (a : Coefficients) (g : ℝ) :
    evaluate (-a) g= -evaluate a g := by simp [evaluate]

theorem evaluate_sub (a b : Coefficients) (g : ℝ) :
    evaluate (a-b) g=evaluate a g-evaluate b g := by
  simp [evaluate,sub_mul,Finset.sum_sub_distrib]

theorem evaluate_scale (z : ℤ) (a : Coefficients) (g : ℝ) :
    evaluate (scale z a) g=(z : ℝ)*evaluate a g := by
  simp [evaluate,scale,Int.cast_mul,mul_assoc,Finset.mul_sum]

theorem evaluate_sum {I : Type*} (s : Finset I) (a : I → Coefficients) (g : ℝ) :
    evaluate (∑ j∈s,a j) g=∑ j∈s,evaluate (a j) g := by
  simp only [evaluate,Finset.sum_apply,Int.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem evaluate_ite (p : Prop) [Decidable p] (a b : Coefficients) (g : ℝ) :
    evaluate (if p then a else b) g=if p then evaluate a g else evaluate b g := by
  split_ifs <;> rfl

/-- Coefficients of g times the product of two cubic kernels. -/
def pair (a b : KernelCoefficients) : Coefficients :=
  ![0,0,0,a 0*b 0,a 0*b 1+a 1*b 0,
    a 0*b 2+a 1*b 1+a 2*b 0,a 1*b 2+a 2*b 1,a 2*b 2,0,0,0]

/-- Coefficients of g times the product of three cubic kernels. -/
def triple (a b c : KernelCoefficients) : Coefficients :=
  ![0,0,0,0,a 0*b 0*c 0,
    (a 0*b 1+a 1*b 0)*c 0+a 0*b 0*c 1,
    (a 0*b 2+a 1*b 1+a 2*b 0)*c 0+(a 0*b 1+a 1*b 0)*c 1+a 0*b 0*c 2,
    (a 1*b 2+a 2*b 1)*c 0+(a 0*b 2+a 1*b 1+a 2*b 0)*c 1+(a 0*b 1+a 1*b 0)*c 2,
    a 2*b 2*c 0+(a 1*b 2+a 2*b 1)*c 1+(a 0*b 2+a 1*b 1+a 2*b 0)*c 2,
    a 2*b 2*c 1+(a 1*b 2+a 2*b 1)*c 2,a 2*b 2*c 2]

theorem pair_evaluate (a b : KernelCoefficients) (g : ℝ) :
    evaluate (pair a b) g=g*evaluateKernel a g*evaluateKernel b g := by
  simp [evaluate,pair,evaluateKernel,Fin.sum_univ_succ]
  ring

theorem triple_evaluate (a b c : KernelCoefficients) (g : ℝ) :
    evaluate (triple a b c) g=g*evaluateKernel a g*evaluateKernel b g*evaluateKernel c g := by
  simp [evaluate,triple,evaluateKernel,Fin.sum_univ_succ]
  ring

section Ordered
variable {V : Type*} [DecidableEq V]

/-- Denominator-normalized ordered source formula. Degree-two terms have one
explicit additional factor q; cubic terms do not. -/
def scaledOrderedWeight {R : Type*} [CommRing R] (q : R) (K : V→V→R)
    (u v a b c d : V) : R :=
  (if u=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(K u b*K u c*K v d) else 0) +
  (if v=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(K v b*K u c*K v d) else 0) +
  (if u=a ∧ v=c ∧ (b≠u ∧ b≠v) ∧ (d≠u ∧ d≠v)
    then q*(K v b*K u d-K u b*K u d-K v b*K v d)+3*K u v*K u b*K v d else 0) +
  (if u=a ∧ v=b ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(q*K u c*K v d+K u v*K u c*K v d) else 0)

/-- Exact finite integer arithmetic, before any matching-orientation sum. -/
def ordered (K : V→V→KernelCoefficients) (u v a b c d : V) : Coefficients :=
  (if u=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(triple (K u b) (K u c) (K v d)) else 0) +
  (if v=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(triple (K v b) (K u c) (K v d)) else 0) +
  (if u=a ∧ v=c ∧ (b≠u ∧ b≠v) ∧ (d≠u ∧ d≠v)
    then scale 64 (pair (K v b) (K u d)-pair (K u b) (K u d)-pair (K v b) (K v d))+
      scale 3 (triple (K u v) (K u b) (K v d)) else 0) +
  (if u=a ∧ v=b ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(scale 64 (pair (K u c) (K v d))+triple (K u v) (K u c) (K v d)) else 0)

theorem ordered_evaluate (K : V→V→KernelCoefficients) (u v a b c d : V) (g : ℝ) :
    evaluate (ordered K u v a b c d) g =
      g*scaledOrderedWeight (64 : ℝ) (fun x y=>evaluateKernel (K x y) g) u v a b c d := by
  simp only [ordered,scaledOrderedWeight,evaluate_add,evaluate_sub,evaluate_neg,
    evaluate_ite,evaluate_zero,evaluate_scale,pair_evaluate,triple_evaluate]
  split_ifs <;> push_cast <;> ring
end Ordered

/-- Three integer coefficients for exactly64 times the actual cubic rung kernel.
Off-diagonal removal is inherited from the proved offWalk2 graph convention. -/
def kernel (n m : ℕ) (u v : Torus.Vertex n m) : KernelCoefficients :=
  ![-16*(adjacencyNat n m u v : ℤ),
    8*((offWalk2 n m u v : ℤ)-(adjacencyNat n m u v : ℤ)),
    -(5*(walk3 n m u v : ℤ)-4*(offWalk2 n m u v : ℤ)-40*(adjacencyNat n m u v : ℤ))]

theorem kernel_evaluate (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (u v : Torus.Vertex n m) (g : ℝ) :
    evaluateKernel (kernel n m u v) g=64*cubicKernel (graph n m h) g u v := by
  simp only [cubicKernel,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [graph_cube_cast n m h hi,graph_off_square_cast n m h hi]
  change ((-16*(adjacencyNat n m u v : ℤ) : ℤ) : ℝ)*g+
    ((8*((offWalk2 n m u v : ℤ)-(adjacencyNat n m u v : ℤ)) : ℤ) : ℝ)*g^2+
    ((-(5*(walk3 n m u v : ℤ)-4*(offWalk2 n m u v : ℤ)-40*(adjacencyNat n m u v : ℤ)) : ℤ) : ℝ)*g^3 =
    64*(-(g/4)*(adjacencyNat n m u v : ℝ)+(g^2/8)*
    ((offWalk2 n m u v : ℝ)-(adjacencyNat n m u v : ℝ))-
    (g^3/64)*(5*(walk3 n m u v : ℝ)-4*(offWalk2 n m u v : ℝ)-40*(adjacencyNat n m u v : ℝ)))
  push_cast
  ring

end BilayerDressed.QuarticIntegerArrays
