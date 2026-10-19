import Dressed.QuarticCoefficientFibers
open scoped BigOperators
namespace BilayerDressed.QuarticDirectCoefficient
open QuarticCoefficientFibers
variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Computable ordered source weight over an arbitrary coefficient ring. -/
def orderedWeight (K : V → V → R) (u v a b c d : V) : R :=
  (if u=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(K u b*K u c*K v d) else 0) +
  (if v=a ∧ (b≠u ∧ b≠v) ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -(K v b*K u c*K v d) else 0) +
  (if u=a ∧ v=c ∧ (b≠u ∧ b≠v) ∧ (d≠u ∧ d≠v)
    then K v b*K u d-K u b*K u d-K v b*K v d+3*K u v*K u b*K v d else 0) +
  (if u=a ∧ v=b ∧ (c≠u ∧ c≠v) ∧ (d≠u ∧ d≠v)
    then -((1+K u v)*K u c*K v d) else 0)

/-- Computable finite direct matching coefficient. No canonical-equivalence
inverse, physical matrix, or occupation-space enumeration is evaluated. -/
def directCoefficient (K : V → V → R) (u v : V) (s : Fin 4 → V) : R :=
  ∑ i : Fin 8, orderedWeight K u v
    (orientations s i 0) (orientations s i 1) (orientations s i 2) (orientations s i 3)

section Real
variable [Fintype V]

omit [Fintype V] in
theorem orderedWeight_real (K : V → V → ℝ) (u v a b c d : V) :
    orderedWeight K u v a b c d = QuarticCoefficientFibers.orderedWeight K u v a b c d := by
  simp only [orderedWeight,QuarticCoefficientFibers.orderedWeight,outsideCondition]
  split_ifs <;> rfl

/-- The ring-computable expression is exactly the actual real matching fiber. -/
theorem matchingCoefficient_eq_directCoefficient (K : V → V → ℝ) (u v : V)
    (s : Fin 4 → V) (hs : Function.Injective s) :
    matchingCoefficient K u v s = directCoefficient K u v s := by
  rw [matchingCoefficient_eq_orientation_sum K u v s hs]
  unfold directCoefficient
  apply Finset.sum_congr rfl
  intro i _
  let t := orientations s i
  have he : (![t 0,t 1,t 2,t 3] : Fin 4 → V)=t := by
    ext j; fin_cases j <;> rfl
  have hh := tupleCoefficient_eq_orderedWeight K u v (t 0) (t 1) (t 2) (t 3)
  rw [he] at hh
  exact hh.trans (orderedWeight_real K u v (t 0) (t 1) (t 2) (t 3)).symm
end Real
end BilayerDressed.QuarticDirectCoefficient

open scoped BigOperators
namespace BilayerDressed.QuarticDirectCoefficient
variable {V R S : Type*} [DecidableEq V] [CommRing R] [CommRing S]

/-- Polynomial evaluation and every other coefficient-ring homomorphism commute
with the explicit finite source formula. -/
theorem map_orderedWeight (φ : R →+* S) (K : V → V → R) (u v a b c d : V) :
    φ (orderedWeight K u v a b c d) =
      orderedWeight (fun x y => φ (K x y)) u v a b c d := by
  unfold orderedWeight
  split_ifs <;> simp [map_ofNat]

theorem map_directCoefficient (φ : R →+* S) (K : V → V → R) (u v : V) (s : Fin 4 → V) :
    φ (directCoefficient K u v s) =
      directCoefficient (fun x y => φ (K x y)) u v s := by
  simp only [directCoefficient,map_sum,map_orderedWeight]

end BilayerDressed.QuarticDirectCoefficient

open scoped BigOperators
namespace BilayerDressed.QuarticDirectCoefficient
open QuarticCoefficientFibers
variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- The computable direct expression vanishes on every disjoint bond, over any
coefficient ring. -/
theorem directCoefficient_disjoint (K : V → V → R) (u v : V) (s : Fin 4 → V)
    (hu : ∀ i, u ≠ s i) (hv : ∀ i, v ≠ s i) : directCoefficient K u v s = 0 := by
  simp [directCoefficient,orderedWeight,orientations,Fin.sum_univ_succ,hu,hv]

/-- At most eight sources per forward direction can meet a four-site support. -/
def incidentSources (ex : V ≃ V) (s : Fin 4 → V) : Finset V :=
  Finset.univ.image s ∪ (Finset.univ.image s).image ex.symm

/-- Exact small finite support reduction for arithmetic evaluation. -/
theorem sum_directCoefficient_eq_incident [Fintype V]
    (K : V → V → R) (ex : V ≃ V) (s : Fin 4 → V) :
    (∑ u, directCoefficient K u (ex u) s) =
      ∑ u ∈ incidentSources ex s, directCoefficient K u (ex u) s := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  apply directCoefficient_disjoint
  · intro i hi
    apply hu
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  · intro i hi
    apply hu
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨s i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
    simpa using congrArg ex.symm hi.symm

end BilayerDressed.QuarticDirectCoefficient

namespace BilayerDressed.QuarticDirectCoefficient
variable {V : Type*} [DecidableEq V]

/-- The exact incident-source reduction uses at most eight vertices per forward direction. -/
theorem incidentSources_card_le (ex : V ≃ V) (s : Fin 4 → V) :
    (incidentSources ex s).card ≤ 8 := by
  have hs : (Finset.univ.image s).card ≤ 4 := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := s))
  have he : ((Finset.univ.image s).image ex.symm).card ≤ 4 :=
    (Finset.card_image_le).trans hs
  exact (Finset.card_union_le _ _).trans (by omega)
end BilayerDressed.QuarticDirectCoefficient
