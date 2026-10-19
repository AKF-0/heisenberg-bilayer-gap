import Mathlib

/-!
# Creation-stable projection algebra

The condition says that a discarded state cannot return to the kept sector
under the operator. Concrete hard-core occupation projections still have to
be shown to satisfy it for bosonic creation. The algebraic closure below does
not assume any spectral gap or norm bound.
-/

namespace BilayerDressed

variable {R : Type*} [Ring R]

def ProjectionStable (p a : R) : Prop := p*a*p = p*a

theorem projectionStable_mul {p a b : R}
    (ha : ProjectionStable p a) (hb : ProjectionStable p b) :
    ProjectionStable p (a*b) := by
  unfold ProjectionStable at *
  calc
    p*(a*b)*p = p*a*b*p := by simp only [mul_assoc]
    _ = p*a*p*b*p := by rw [ha]
    _ = p*a*(p*b*p) := by simp only [mul_assoc]
    _ = p*a*(p*b) := by rw [hb]
    _ = p*a*p*b := by simp only [mul_assoc]
    _ = p*a*b := by rw [ha]
    _ = p*(a*b) := by simp only [mul_assoc]

theorem projectionStable_add {p a b : R}
    (ha : ProjectionStable p a) (hb : ProjectionStable p b) :
    ProjectionStable p (a+b) := by
  unfold ProjectionStable at *
  simpa only [mul_add, add_mul, ha, hb]

theorem projectionStable_one {p : R} (hp : p*p=p) : ProjectionStable p 1 := by
  simpa only [ProjectionStable, mul_one] using hp

theorem projectionStable_pow {p a : R} (hp : p*p=p)
    (ha : ProjectionStable p a) (n : ℕ) : ProjectionStable p (a^n) := by
  induction n with
  | zero => simpa using projectionStable_one hp
  | succ n ih => simpa only [pow_succ] using projectionStable_mul ih ha

/-- The insertion of a hard-core projection between two creation polynomials
does not alter their final projected product. -/
theorem projected_product_no_intermediate_loss {p a b : R}
    (ha : ProjectionStable p a) : p*a*p*b = p*(a*b) := by
  unfold ProjectionStable at ha
  rw [ha, mul_assoc]

theorem projectionStable_iff_discarded_zero (p a : R) :
    ProjectionStable p a ↔ p*a*(1-p)=0 := by
  unfold ProjectionStable
  rw [mul_sub, mul_one, sub_eq_zero]
  exact eq_comm

end BilayerDressed
