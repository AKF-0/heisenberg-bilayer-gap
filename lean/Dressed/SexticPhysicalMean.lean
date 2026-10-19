import Dressed.SexticFaithfulLift
import Dressed.CubicPhysicalMeanEndpoints

/-! Actual physical sextic expectation bounds. The six-creator word dictionary
and the literal global residual expansion are preserved before applying Wick405.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.SexticPhysicalMean
open Matrix FiniteOccupation FinitePhysicalWick SexticFaithfulLift
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Raw finite expectation equals the actual real Euclidean inner product. -/
theorem expect_eq_inner (ψ : ConfigurationHilbert V) (A : ConfigurationMatrix V) :
    PositiveMatrix.expect (WithLp.ofLp ψ) A=⟪ψ,A.toEuclideanLin ψ⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,Matrix.ofLp_toEuclideanLin_apply]
  exact dotProduct_comm _ _

/-- Exact physical word dictionary, without any Gaussian interpretation. -/
theorem sixPolynomial_eq_physicalPolynomial (sites : Fin 6→V) :
    ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V)=physicalPolynomial (fun _ : Fin 3→Fin 3 => (1:ℝ))
        (sixWord sites) := by
  rw [coe_sixPolynomial]
  simp only [physicalPolynomial,PositiveMatrix.creationPolynomial,one_smul,
    word_eq_prod]

/-- A six-word bound includes all 27 color choices and all 15 matchings. -/
theorem six_wick_sum_le (L : Mode V→Mode V→ℝ) (hL : ∀ i j,0 ≤ L i j)
    (m : ℝ) (hm : 0 ≤ m) (hLm : ∀ i j,L i j ≤ m) (sites : Fin 6→V) :
    (∑ colors : Fin 3→Fin 3,FiniteWickPairings.wick L (sixWord sites colors)) ≤405*m^3 := by
  have hs (colors : Fin 3→Fin 3) :
      FiniteWickPairings.wick L (sixWord sites colors) ≤15*m^3 := by
    have hh := FiniteWickPairings.wick_six_le L hL m hm hLm
      (sites 0,colors 0) (sites 1,colors 0) (sites 2,colors 1)
      (sites 3,colors 1) (sites 4,colors 2) (sites 5,colors 2)
    simpa only [sixWord,List.ofFn_succ,List.ofFn_zero,pairSlot] using hh
  calc
    _ ≤∑ _colors : Fin 3→Fin 3,15*m^3 := Finset.sum_le_sum fun colors _ => hs colors
    _ = _ := by simp; ring

/-- Exact local edge expansion followed by the triangle inequality. -/
theorem bond6_expect_le (ψ : Configuration V→ℝ) (K : V→V→ℝ) (C : ℝ)
    (hsix : ∀ sites : Fin 6→V,
      |PositiveMatrix.expect ψ ((sixPolynomial GlobalResidual.C sites :
        GlobalResidual.creationAlgebra V) : ConfigurationMatrix V)| ≤ C)
    (r s : V) :
    |PositiveMatrix.expect ψ ((GlobalResidual.bondResidual6 K r s :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V)| ≤
      C*outsideRow K r s r^2*outsideRow K r s s^2 := by
  rw [bondResidual6_expansion]
  simp only [AddSubmonoidClass.coe_finset_sum,Subalgebra.coe_smul,
    PositiveMatrix.expect_sum,PositiveMatrix.expect_smul,smul_eq_mul]
  calc
    _ ≤ ∑ i : PhysicalGram.Outside r s,∑ j : PhysicalGram.Outside r s,
        ∑ k : PhysicalGram.Outside r s,∑ l : PhysicalGram.Outside r s,
          |edgeCoefficient K r s i j k l| * C := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hsix _) (abs_nonneg _)
    _ = _ := by
      simp only [edgeCoefficient,abs_mul,outsideRow,←Finset.mul_sum,←Finset.sum_mul]
      ring

/-- The true degree-six residual mean is controlled by its already-certified scalar mass. -/
theorem residual6_expect_le (ψ : Configuration V→ℝ) (K : V→V→ℝ)
    (ex ey : Equiv.Perm V) (g C : ℝ) (hg : 0 ≤ g)
    (hsix : ∀ sites : Fin 6→V,
      |PositiveMatrix.expect ψ ((sixPolynomial GlobalResidual.C sites :
        GlobalResidual.creationAlgebra V) : ConfigurationMatrix V)| ≤ C) :
    |PositiveMatrix.expect ψ ((GlobalResidual.residual6 K ex ey g :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V)| ≤C*ell6 K ex ey g := by
  simp only [GlobalResidual.residual6,Subalgebra.coe_smul,Subalgebra.coe_add,
    AddSubmonoidClass.coe_finset_sum,PositiveMatrix.expect_smul,
    PositiveMatrix.expect_add,PositiveMatrix.expect_sum,smul_eq_mul,abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ g/2)]
  have hx := (Finset.abs_sum_le_sum_abs (fun r => PositiveMatrix.expect ψ
    ((GlobalResidual.bondResidual6 K r (ex r) : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V)) Finset.univ).trans
        (Finset.sum_le_sum fun r _ => bond6_expect_le ψ K C hsix r (ex r))
  have hy := (Finset.abs_sum_le_sum_abs (fun r => PositiveMatrix.expect ψ
    ((GlobalResidual.bondResidual6 K r (ey r) : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V)) Finset.univ).trans
        (Finset.sum_le_sum fun r _ => bond6_expect_le ψ K C hsix r (ey r))
  calc
    _ ≤ (g/2)*((∑ r,C*outsideRow K r (ex r) r^2*outsideRow K r (ex r) (ex r)^2)+
        ∑ r,C*outsideRow K r (ey r) r^2*outsideRow K r (ey r) (ey r)^2) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hx hy)) (by positivity)
    _ = _ := by
      simp only [ell6,←Finset.mul_sum,mul_assoc]
      ring

end BilayerDressed.SexticPhysicalMean
