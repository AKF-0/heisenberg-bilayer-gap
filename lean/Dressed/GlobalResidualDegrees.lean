import Dressed.GlobalResidualAlgebra

/-!
# All homogeneous creation degrees of the transformed bond

The letters x and y are local creations, while A and B have one creation on
outside sites. k is a real kernel coefficient and has creation degree zero.
No term is discarded on account of its order in the coupling.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.GlobalResidual
open LocalBond
variable {R : Type*} [CommRing R]

/-- Evaluation of a two-rung coefficient vector as a creation polynomial. -/
def evaluate (x y : Fin 3 → R) (v : PairIndex → R) : R :=
  v (0,0) + (∑ α : Fin 3, x α * v (α.succ,0)) +
  (∑ β : Fin 3, y β * v (0,β.succ)) +
  ∑ α : Fin 3, ∑ β : Fin 3, x α * y β * v (α.succ,β.succ)

/-- The complete creation-degree-two part of twice the transformed bond. -/
def bondR2 (x y A B : Fin 3 → R) (k : R) : R :=
  dot A B + (∑ α : Fin 3, x α * (B α - 3*k*A α)) +
  (∑ β : Fin 3, y β * (A β - 3*k*B β)) +
  (1-2*k-3*k^2) * ∑ α : Fin 3, x α * y α

/-- Every creation-degree-four term, including the terms proportional to k. -/
def bondR4 (x y A B : Fin 3 → R) (k : R) : R :=
  -(∑ α : Fin 3, x α * A α * dot A B) -
  (∑ β : Fin 3, y β * B β * dot A B) +
  ∑ α : Fin 3, ∑ β : Fin 3, x α * y β *
    (B α*A β - (if α=β then dot A B else 0) - A α*A β - B α*B β +
      3*k*A α*B β - (if α=β then k*dot A B else 0))

/-- The nonvanishing degree-six term is retained explicitly. -/
def bondR6 (x y A B : Fin 3 → R) : R :=
  ∑ α : Fin 3, ∑ β : Fin 3, x α * y β * A α * B β * dot A B

/-- Exact degree-0/2/4/6 decomposition, as a polynomial identity over any
commutative coefficient ring. -/
theorem transformed_degree_decomposition (x y A B : Fin 3 → R) (k : R) :
    evaluate x y (transformedCoefficients A B k) =
      3*k + bondR2 x y A B k + bondR4 x y A B k + bondR6 x y A B := by
  simp [evaluate, transformedCoefficients, bondR2, bondR4, bondR6,
    Fin.sum_univ_succ]
  ring

end BilayerDressed.GlobalResidual
