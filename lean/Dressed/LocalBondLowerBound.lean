import Dressed.LocalBondAction

/-!
# Finite local Gram-square lower bound

These are quadratic-form inequalities for the actual 16-dimensional local
matrix, with arbitrary real input coefficients. No eigenvalue or gap premise
is assumed. The same inequality can be summed over tensor-product edges.
-/
noncomputable section
namespace BilayerDressed.LocalBond
open scoped BigOperators

abbrev RealPair := PairIndex → ℝ

def stNorm (v : RealPair) : ℝ :=
  v (1,0)^2+v (2,0)^2+v (3,0)^2+v (0,1)^2+v (0,2)^2+v (0,3)^2

def offNorm (v : RealPair) : ℝ :=
  v (1,2)^2+v (2,1)^2+v (1,3)^2+v (3,1)^2+v (2,3)^2+v (3,2)^2

def ttNorm (v : RealPair) : ℝ :=
  v (1,1)^2+v (2,2)^2+v (3,3)^2+offNorm v

def numberForm (v : RealPair) : ℝ := stNorm v+2*ttNorm v

def normForm (v : RealPair) : ℝ := v (0,0)^2+stNorm v+ttNorm v

def normalSOS (v : RealPair) : ℝ := (1/2 : ℝ)*(
  (v (1,0)+v (0,1))^2+(v (2,0)+v (0,2))^2+(v (3,0)+v (0,3))^2+
  (v (1,1)-v (2,2))^2+(v (1,1)-v (3,3))^2+(v (2,2)-v (3,3))^2+
  (v (1,2)+v (2,1))^2+(v (1,3)+v (3,1))^2+(v (2,3)+v (3,2))^2+
  offNorm v)

def pairSOS (g : ℝ) (v : RealPair) : ℝ :=
  (1/10 : ℝ)*((5*g*v (0,0)+v (1,1))^2+
    (5*g*v (0,0)+v (2,2))^2+(5*g*v (0,0)+v (3,3))^2) +
  stNorm v/20+offNorm v/10+(15/2 : ℝ)*g^2*(stNorm v+ttNorm v)

/-- Exact polynomial sum-of-squares identity for the local Heisenberg bond. -/
theorem local_gram_identity (g : ℝ) (v : RealPair) :
    (g/2)*dotProduct v (Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex ℝ) v)+
      (g/2+1/20)*numberForm v+(15/2 : ℝ)*g^2*normForm v =
        g*normalSOS v+pairSOS g v := by
  rw [twiceBond_mulVec]
  simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, action,
    numberForm, normForm, normalSOS, pairSOS, stNorm, ttNorm, offNorm]
  ring

/-- A true local operator-form bound, valid for every real vector. -/
theorem local_bond_lower_bound (g : ℝ) (hg : 0 ≤ g) (v : RealPair) :
    -(g/2+1/20)*numberForm v-(15/2 : ℝ)*g^2*normForm v ≤
      (g/2)*dotProduct v (Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex ℝ) v) := by
  have hnormal : 0 ≤ normalSOS v := by unfold normalSOS offNorm; positivity
  have hpair : 0 ≤ pairSOS g v := by unfold pairSOS stNorm ttNorm offNorm; positivity
  have h := local_gram_identity g v
  have hn := mul_nonneg hg hnormal
  linarith

/-- The scalar norm form is exactly the usual finite Euclidean norm square. -/
theorem normForm_eq_sum_sq (v : RealPair) : normForm v = ∑ p, v p^2 := by
  simp [normForm, stNorm, ttNorm, offNorm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- The number form weights one-triplet states by one and two-triplet states by two. -/
theorem numberForm_eq_sum (v : RealPair) :
    numberForm v = ∑ p : PairIndex,
      ((if p.1=0 then 0 else 1 : ℝ)+(if p.2=0 then 0 else 1 : ℝ))*v p^2 := by
  simp [numberForm, stNorm, ttNorm, offNorm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

end BilayerDressed.LocalBond
