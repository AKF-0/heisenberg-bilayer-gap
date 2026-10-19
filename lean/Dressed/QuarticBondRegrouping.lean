import Dressed.GlobalDressedResidual

/-!
# Exact quartic bond regrouping in the actual creation algebra

All terms are retained, including the k-dependent quartic terms. Pair products
are actual finite hard-core creation matrices inside their commutative subalgebra.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticBondRegrouping
open GlobalResidual LocalBond PhysicalGram
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Same-color pair contraction in a commutative creation algebra. -/
def pairForm {R : Type*} [CommRing R] (c : V → Fin 3 → R) (u v : V) : R :=
  dot (c u) (c v)

/-- Literal bondR4 rearranged into pair contractions; no field term is omitted. -/
theorem bondR4_dot {R : Type*} [CommRing R]
    (x y A B : Fin 3 → R) (k : R) :
    bondR4 x y A B k =
      -(dot x A * dot A B) - dot y B * dot A B +
      dot x B * dot y A - (1+k) * dot x y * dot A B -
      dot x A * dot y A - dot x B * dot y B + 3*k*dot x A*dot y B := by
  simp [bondR4, dot, Fin.sum_univ_succ]
  ring

lemma dot_local_outside {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) (u v r s : V) :
    dot (c r) (outsideField c K u v s) =
      ∑ i : Outside u v, K s i • pairForm c r i := by
  simp only [dot, outsideField, pairForm, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  rw [Finset.sum_comm]

lemma dot_outside_outside {R : Type*} [CommRing R] [Algebra ℝ R]
    (c : V → Fin 3 → R) (K : V → V → ℝ) (u v r s : V) :
    dot (outsideField c K u v r) (outsideField c K u v s) =
      ∑ i : Outside u v, ∑ j : Outside u v, (K r i * K s j) • pairForm c i j := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [dot, outsideField, pairForm, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The same-color pair in the actual hard-core creation subalgebra. -/
def Q (u v : V) : creationAlgebra V := pairForm C u v

@[simp] theorem coe_Q (u v : V) :
    ((Q u v : creationAlgebra V) : ConfigurationMatrix V) = pairCreate u v := rfl

/-- Exact compact pair form of the literal physical quartic bond. -/
theorem bondResidual4_pair_form (K : V → V → ℝ) (u v : V) :
    bondResidual4 K u v =
      -((∑ i : Outside u v, K u i • Q u i) *
        (∑ j : Outside u v, ∑ k : Outside u v, (K u j*K v k) • Q (V := V) j k)) -
      (∑ i : Outside u v, K v i • Q v i) *
        (∑ j : Outside u v, ∑ k : Outside u v, (K u j*K v k) • Q (V := V) j k) +
      (∑ i : Outside u v, K v i • Q u i) * (∑ j : Outside u v, K u j • Q v j) -
      (1 + algebraMap ℝ (creationAlgebra V) (K u v)) * Q u v *
        (∑ i : Outside u v, ∑ j : Outside u v, (K u i*K v j) • Q (V := V) i j) -
      (∑ i : Outside u v, K u i • Q u i) * (∑ j : Outside u v, K u j • Q v j) -
      (∑ i : Outside u v, K v i • Q u i) * (∑ j : Outside u v, K v j • Q v j) +
      (3 * algebraMap ℝ (creationAlgebra V) (K u v)) *
        (∑ i : Outside u v, K u i • Q u i) * (∑ j : Outside u v, K v j • Q v j) := by
  simp only [bondResidual4, bondR4_dot, dot_local_outside, dot_outside_outside, Q, pairForm]

end BilayerDressed.QuarticBondRegrouping

noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticBondRegrouping
open GlobalResidual LocalBond PhysicalGram
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bondResidual4_pair_expansion (K : V → V → ℝ) (u v : V) :
    bondResidual4 K u v =
      -(∑ i : Outside u v, ∑ j : Outside u v, ∑ k : Outside u v,
        (K u i*K u j*K v k) • (Q u i*Q (V := V) j k)) -
      (∑ i : Outside u v, ∑ j : Outside u v, ∑ k : Outside u v,
        (K v i*K u j*K v k) • (Q v i*Q (V := V) j k)) +
      (∑ i : Outside u v, ∑ j : Outside u v,
        (K v i*K u j-K u i*K u j-K v i*K v j+3*K u v*K u i*K v j) • (Q u i*Q v j)) -
      (∑ i : Outside u v, ∑ j : Outside u v,
        ((1+K u v)*K u i*K v j) • (Q u v*Q (V := V) i j)) := by
  rw [bondResidual4_pair_form]
  have h1 : (1 + algebraMap ℝ (creationAlgebra V) (K u v)) =
      algebraMap ℝ (creationAlgebra V) (1+K u v) := by simp only [map_add, map_one]
  have h3 : (3 * algebraMap ℝ (creationAlgebra V) (K u v)) =
      algebraMap ℝ (creationAlgebra V) (3*K u v) := by simp only [map_mul, map_ofNat]
  rw [h1,h3]
  simp only [mul_assoc]
  simp_rw [Fintype.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, Finset.smul_sum, ← Algebra.smul_def, mul_assoc, sub_smul, add_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [smul_add, one_smul, smul_smul, add_mul, mul_add, one_mul, mul_one,
    add_smul, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  abel


theorem Q_symm (u v : V) : Q u v = Q v u := by
  simp only [Q, pairForm, dot, mul_comm]

@[simp] theorem Q_diag (u : V) : Q u u = 0 := by
  simp [Q, pairForm, dot]

/-- Repeated-site deletion occurs in the physical creation algebra, before any
bosonic lift is formed. -/
theorem Q_mul_Q_shared (u v w : V) : Q u v * Q u w = 0 := by
  simp only [Q, pairForm, dot, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero; intro α _
  apply Finset.sum_eq_zero; intro β _
  rw [show C u β * C v β * (C u α * C w α) =
    (C u β * C u α) * (C v β * C w α) by ring, C_mul_same, zero_mul]

theorem Q_mul_Q_injective_of_ne_zero (a b c d : V) (hz : Q a b * Q c d ≠ 0) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  have hab : a ≠ b := by rintro rfl; simp at hz
  have hcd : c ≠ d := by rintro rfl; simp at hz
  have hac : a ≠ c := by rintro rfl; exact hz (Q_mul_Q_shared _ _ _)
  have had : a ≠ d := by
    rintro rfl
    exact hz (by rw [Q_symm c a, Q_mul_Q_shared])
  have hbc : b ≠ c := by
    rintro rfl
    exact hz (by rw [Q_symm a b, Q_mul_Q_shared])
  have hbd : b ≠ d := by
    rintro rfl
    exact hz (by rw [Q_symm a b, Q_symm c b, Q_mul_Q_shared])
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> tauto

/-- The faithful four-site filter changes no physical quartic pair monomial. -/
theorem Q_mul_Q_eq_distinct_filter (a b c d : V) :
    Q a b * Q c d =
      if Function.Injective (![a,b,c,d] : Fin 4 → V) then Q a b * Q c d else 0 := by
  split_ifs with hi
  · rfl
  · by_contra hn
    exact hi (Q_mul_Q_injective_of_ne_zero a b c d hn)

end BilayerDressed.QuarticBondRegrouping

noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticBondRegrouping
open GlobalResidual LocalBond PhysicalGram
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual four-creator pair word in the physical creation algebra. -/
def physicalWord (s : Fin 4 → V) : creationAlgebra V := Q (s 0) (s 1) * Q (s 2) (s 3)

/-- Repeated physical sites are explicitly deleted before any bosonic lift. -/
def faithfulWord (s : Fin 4 → V) : creationAlgebra V :=
  if Function.Injective s then physicalWord s else 0

theorem faithfulWord_eq (s : Fin 4 → V) : faithfulWord s = physicalWord s := by
  have he : (![s 0,s 1,s 2,s 3] : Fin 4 → V) = s := by
    ext i; fin_cases i <;> rfl
  have hh := Q_mul_Q_eq_distinct_filter (s 0) (s 1) (s 2) (s 3)
  rw [he] at hh
  exact hh.symm

abbrev TripleOutside (u v : V) := Outside u v × Outside u v × Outside u v
abbrev PairOutside (u v : V) := Outside u v × Outside u v
/-- Four exact source families: the two one-endpoint terms and two two-endpoint terms. -/
abbrev BondTerm (u v : V) :=
  (TripleOutside u v ⊕ TripleOutside u v) ⊕ (PairOutside u v ⊕ PairOutside u v)

/-- Ordered pair-site tuple, before the explicit repeated-site deletion. -/
def termSites (u v : V) : BondTerm u v → Fin 4 → V
  | .inl (.inl p) => ![u,p.1,p.2.1,p.2.2]
  | .inl (.inr p) => ![v,p.1,p.2.1,p.2.2]
  | .inr (.inl p) => ![u,p.1,v,p.2]
  | .inr (.inr p) => ![u,v,p.1,p.2]

/-- Literal scalar coefficients; the physical bond factor g/2 is applied globally. -/
def termCoefficient (K : V → V → ℝ) (u v : V) : BondTerm u v → ℝ
  | .inl (.inl p) => -(K u p.1*K u p.2.1*K v p.2.2)
  | .inl (.inr p) => -(K v p.1*K u p.2.1*K v p.2.2)
  | .inr (.inl p) => K v p.1*K u p.2-K u p.1*K u p.2-K v p.1*K v p.2+
      3*K u v*K u p.1*K v p.2
  | .inr (.inr p) => -((1+K u v)*K u p.1*K v p.2)

/-- Exact finite source-term expansion with repeated-site deletion already imposed. -/
theorem bondResidual4_eq_terms (K : V → V → ℝ) (u v : V) :
    bondResidual4 K u v = ∑ t : BondTerm u v,
      termCoefficient K u v t • faithfulWord (termSites u v t) := by
  rw [bondResidual4_pair_expansion]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, faithfulWord_eq,
    termSites, termCoefficient, physicalWord, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, neg_smul, Finset.sum_neg_distrib]
  abel

/-- Global actual quartic sum, with the physical g/2 factor retained exactly. -/
theorem sum_bondResidual4_eq_terms {E : Type*} [Fintype E]
    (K : V → V → ℝ) (u v : E → V) (g : ℝ) :
    (∑ e, (g/2) • bondResidual4 K (u e) (v e)) =
      ∑ e, ∑ t : BondTerm (u e) (v e),
        ((g/2)*termCoefficient K (u e) (v e) t) • faithfulWord (termSites (u e) (v e) t) := by
  simp only [bondResidual4_eq_terms, Finset.smul_sum, smul_smul]


/-- The two oriented forward-bond directions of the literal global residual. -/
def forwardNeighbor (ex ey : V ≃ V) (d : Fin 2) (u : V) : V :=
  if d=0 then ex u else ey u

/-- One finite index type for every literal quartic source term. -/
abbrev GlobalTerm (ex ey : V ≃ V) :=
  Σ e : Fin 2 × V, BondTerm e.2 (forwardNeighbor ex ey e.1 e.2)

def globalTermSites (ex ey : V ≃ V) (t : GlobalTerm ex ey) : Fin 4 → V :=
  termSites t.1.2 (forwardNeighbor ex ey t.1.1 t.1.2) t.2

def globalTermCoefficient (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (t : GlobalTerm ex ey) : ℝ :=
  (g/2) * termCoefficient K t.1.2 (forwardNeighbor ex ey t.1.1 t.1.2) t.2

/-- Actual global residual4, exactly flattened into a finite family of faithful
four-site words. Its coefficients retain the physical bond normalization. -/
theorem residual4_eq_global_terms (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    residual4 K ex ey g = ∑ t : GlobalTerm ex ey,
      globalTermCoefficient K ex ey g t • faithfulWord (globalTermSites ex ey t) := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, globalTermCoefficient,
    globalTermSites, ← smul_smul, ← Finset.smul_sum, ← bondResidual4_eq_terms]
  simp [forwardNeighbor, Fin.sum_univ_succ, residual4, smul_add]

@[simp] theorem coe_physicalWord (s : Fin 4 → V) :
    ((physicalWord s : creationAlgebra V) : ConfigurationMatrix V) =
      pairCreate (s 0) (s 1) * pairCreate (s 2) (s 3) := rfl

theorem coe_faithfulWord (s : Fin 4 → V) :
    ((faithfulWord s : creationAlgebra V) : ConfigurationMatrix V) =
      if Function.Injective s then pairCreate (s 0) (s 1) * pairCreate (s 2) (s 3) else 0 := by
  unfold faithfulWord
  split_ifs <;> rfl

/-- Matrix-level interface for canonical matching regrouping and faithful lifts. -/
theorem coe_residual4_eq_global_terms (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) =
      ∑ t : GlobalTerm ex ey, globalTermCoefficient K ex ey g t •
        (if Function.Injective (globalTermSites ex ey t) then
          pairCreate (globalTermSites ex ey t 0) (globalTermSites ex ey t 1) *
          pairCreate (globalTermSites ex ey t 2) (globalTermSites ex ey t 3) else 0) := by
  have hh := congrArg (creationAlgebra V).val (residual4_eq_global_terms K ex ey g)
  simpa only [map_sum, map_smul, Subalgebra.val_apply, coe_faithfulWord] using hh

/-- The faithful source index retains only four genuinely distinct physical sites. -/
abbrev DistinctGlobalTerm (ex ey : V ≃ V) :=
  {t : GlobalTerm ex ey // Function.Injective (globalTermSites ex ey t)}

/-- The explicit deletion is equivalently a sum over an actual finite subtype,
ready for the canonical matching theorem requiring injective tuples. -/
theorem residual4_eq_distinct_terms (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    residual4 K ex ey g = ∑ t : DistinctGlobalTerm ex ey,
      globalTermCoefficient K ex ey g t.val • physicalWord (globalTermSites ex ey t.val) := by
  rw [residual4_eq_global_terms]
  simp only [faithfulWord, smul_ite, smul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro t; simp) _

/-- Matrix version of the filtered actual source family. -/
theorem coe_residual4_eq_distinct_terms (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) =
      ∑ t : DistinctGlobalTerm ex ey, globalTermCoefficient K ex ey g t.val •
        (pairCreate (globalTermSites ex ey t.val 0) (globalTermSites ex ey t.val 1) *
          pairCreate (globalTermSites ex ey t.val 2) (globalTermSites ex ey t.val 3)) := by
  have hh := congrArg (creationAlgebra V).val (residual4_eq_distinct_terms K ex ey g)
  simpa only [map_sum, map_smul, Subalgebra.val_apply, coe_physicalWord] using hh

/-- Site bijections transport the two-endpoint-excluded index set exactly. -/
def outsideEquiv (e : V ≃ V) (u v : V) : Outside u v ≃ Outside (e u) (e v) where
  toFun w := ⟨e w, by simpa only [ne_eq, e.injective.eq_iff] using w.property⟩
  invFun w := ⟨e.symm w, by
    constructor
    · intro h
      apply w.property.1
      have hh := congrArg e h
      simpa using hh
    · intro h
      apply w.property.2
      have hh := congrArg e h
      simpa using hh⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

/-- Actual finite reindexing of all four source families under a site bijection. -/
def termEquiv (e : V ≃ V) (u v : V) : BondTerm u v ≃ BondTerm (e u) (e v) :=
  let o := outsideEquiv e u v
  let p := Equiv.prodCongr o o
  let t := Equiv.prodCongr o p
  Equiv.sumCongr (Equiv.sumCongr t t) (Equiv.sumCongr p p)

theorem termSites_equiv (e : V ≃ V) (u v : V) (t : BondTerm u v) (i : Fin 4) :
    termSites (e u) (e v) (termEquiv e u v t) i = e (termSites u v t i) := by
  rcases t with (p|p)|(p|p) <;> fin_cases i <;> rfl

/-- Translation invariance is proved from actual kernel covariance, without a
norm or orbit-size assumption. -/
theorem termCoefficient_equiv (K : V → V → ℝ) (e : V ≃ V)
    (hK : ∀ a b, K (e a) (e b) = K a b) (u v : V) (t : BondTerm u v) :
    termCoefficient K (e u) (e v) (termEquiv e u v t) = termCoefficient K u v t := by
  rcases t with (p|p)|(p|p) <;>
    simp [termEquiv, termCoefficient, outsideEquiv, hK]

end BilayerDressed.QuarticBondRegrouping

noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticBondRegrouping
open GlobalResidual PhysicalGram
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Proof-only endpoint transport for the dependent term index type. -/
def bondTermCast {u v u' v' : V} (hu : u=u') (hv : v=v') : BondTerm u v ≃ BondTerm u' v' :=
  Equiv.cast (by rw [hu,hv])

theorem termSites_cast {u v u' v' : V} (hu : u=u') (hv : v=v')
    (t : BondTerm u v) (i : Fin 4) :
    termSites u' v' (bondTermCast hu hv t) i = termSites u v t i := by
  subst u'; subst v'; rfl

theorem termCoefficient_cast (K : V → V → ℝ) {u v u' v' : V} (hu : u=u') (hv : v=v')
    (t : BondTerm u v) :
    termCoefficient K u' v' (bondTermCast hu hv t) = termCoefficient K u v t := by
  subst u'; subst v'; rfl

theorem forwardNeighbor_equiv (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (d : Fin 2) (u : V) :
    forwardNeighbor ex ey d (e u) = e (forwardNeighbor ex ey d u) := by
  unfold forwardNeighbor
  split_ifs <;> simp only [hx,hy]

/-- Genuine permutation of the complete literal global source-term index. -/
def globalTermEquiv (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u)) :
    GlobalTerm ex ey ≃ GlobalTerm ex ey :=
  Equiv.sigmaCongr (Equiv.prodCongr (Equiv.refl (Fin 2)) e) fun b =>
    (termEquiv e b.2 (forwardNeighbor ex ey b.1 b.2)).trans
      (bondTermCast rfl (forwardNeighbor_equiv ex ey e hx hy b.1 b.2).symm)

theorem globalTermSites_equiv (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (t : GlobalTerm ex ey) (i : Fin 4) :
    globalTermSites ex ey (globalTermEquiv ex ey e hx hy t) i = e (globalTermSites ex ey t i) := by
  rcases t with ⟨⟨d,u⟩,t⟩
  change termSites (e u) (forwardNeighbor ex ey d (e u))
    (bondTermCast rfl (forwardNeighbor_equiv ex ey e hx hy d u).symm
      (termEquiv e u (forwardNeighbor ex ey d u) t)) i = _
  rw [termSites_cast, termSites_equiv]
  rfl

theorem globalTermCoefficient_equiv (K : V → V → ℝ) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ a b, K (e a) (e b) = K a b) (g : ℝ) (t : GlobalTerm ex ey) :
    globalTermCoefficient K ex ey g (globalTermEquiv ex ey e hx hy t) =
      globalTermCoefficient K ex ey g t := by
  rcases t with ⟨⟨d,u⟩,t⟩
  change (g/2) * termCoefficient K (e u) (forwardNeighbor ex ey d (e u))
    (bondTermCast rfl (forwardNeighbor_equiv ex ey e hx hy d u).symm
      (termEquiv e u (forwardNeighbor ex ey d u) t)) = _
  rw [termCoefficient_cast, termCoefficient_equiv K e hK]
  rfl


theorem globalTerm_injective_iff (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (t : GlobalTerm ex ey) :
    Function.Injective (globalTermSites ex ey (globalTermEquiv ex ey e hx hy t)) ↔
      Function.Injective (globalTermSites ex ey t) := by
  constructor
  · intro ht i j hij
    apply ht
    rw [globalTermSites_equiv, globalTermSites_equiv, hij]
  · intro ht i j hij
    apply ht
    apply e.injective
    simpa only [globalTermSites_equiv] using hij

/-- Translation also permutes the faithful finite subtype, so deletion commutes
with actual site translation. -/
def distinctGlobalTermEquiv (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u)) :
    DistinctGlobalTerm ex ey ≃ DistinctGlobalTerm ex ey :=
  (globalTermEquiv ex ey e hx hy).subtypeEquiv
    (fun t => (globalTerm_injective_iff ex ey e hx hy t).symm)

theorem distinctGlobalTermSites_equiv (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (t : DistinctGlobalTerm ex ey) (i : Fin 4) :
    globalTermSites ex ey (distinctGlobalTermEquiv ex ey e hx hy t).val i =
      e (globalTermSites ex ey t.val i) :=
  globalTermSites_equiv ex ey e hx hy t.val i

theorem distinctGlobalTermCoefficient_equiv (K : V → V → ℝ) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u) = e (ex u)) (hy : ∀ u, ey (e u) = e (ey u))
    (hK : ∀ a b, K (e a) (e b) = K a b) (g : ℝ) (t : DistinctGlobalTerm ex ey) :
    globalTermCoefficient K ex ey g (distinctGlobalTermEquiv ex ey e hx hy t).val =
      globalTermCoefficient K ex ey g t.val :=
  globalTermCoefficient_equiv K ex ey e hx hy hK g t.val

end BilayerDressed.QuarticBondRegrouping
