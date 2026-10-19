import Dressed.QuarticCoefficientFibers
import Dressed.QuarticCanonicalTransport
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticActualCoefficients
open GlobalResidual QuarticBondRegrouping QuarticCoefficientFibers
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered representative of each of the three canonical unordered matchings. -/
def matchingTuple (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (S : QuarticCanonical.Support V) (m : Fin 3) : Fin 4 → V :=
  let v := QuarticCanonical.tuple enum S
  (![![v 0,v 1,v 2,v 3],![v 0,v 2,v 1,v 3],![v 0,v 3,v 1,v 2]]) m

theorem matchingTuple_injective
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (S : QuarticCanonical.Support V) (m : Fin 3) :
    Function.Injective (matchingTuple enum S m) := by
  have hv := QuarticCanonical.tuple_injective enum S
  intro i j hij
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    simp_all [matchingTuple,hv.eq_iff]

theorem matchingTuple_support
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (S : QuarticCanonical.Support V) (m : Fin 3) :
    QuarticCanonical.tupleSupport (matchingTuple enum S m) (matchingTuple_injective enum S m)=S := by
  apply Subtype.ext
  change Finset.univ.image (matchingTuple enum S m)=S.val
  have hv : Finset.univ.image (QuarticCanonical.tuple enum S)=S.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (enum S i).property
    · intro hx
      obtain ⟨i,hi⟩ := (enum S).surjective ⟨x,hx⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩
  rw [← hv]
  fin_cases m <;> ext x <;>
    simp [matchingTuple,Fin.exists_fin_succ,or_assoc,or_comm,or_left_comm] <;> tauto

theorem matchingTuple_pairing
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (S : QuarticCanonical.Support V) (m : Fin 3) :
    pairing (matchingTuple enum S m)=QuarticCanonical.canonicalSupportPairing enum S m := by
  fin_cases m <;>
    simp [matchingTuple,pairing,QuarticCanonical.canonicalSupportPairing,
      QuarticCanonical.mapPairing,QuarticCanonical.canonicalPairing]

/-- Equal unordered matchings have the same support, including all four sites. -/
theorem tupleSupport_eq_of_pairing_eq (v w : Fin 4 → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hp : pairing v=pairing w) :
    QuarticCanonical.tupleSupport v hv = QuarticCanonical.tupleSupport w hw := by
  apply Subtype.ext
  have hh := congrArg (fun p : Finset (Finset V) => p.biUnion id) hp
  simpa only [union_pairing,QuarticCanonical.tupleSupport] using hh

/-- Once the target matching is fixed, canonical fibers are concrete unordered
pairing fibers. No reduction through a chosen inverse equivalence is required. -/
theorem key_eq_iff_pairing (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (v w : Fin 4 → V) (hv : Function.Injective v) (hw : Function.Injective w)
    (S : QuarticCanonical.Support V) (m : Fin 3)
    (hS : QuarticCanonical.tupleSupport w hw=S)
    (hp : pairing w=QuarticCanonical.canonicalSupportPairing enum S m) :
    QuarticCanonical.key enum v hv=(S,m) ↔ pairing v=pairing w := by
  rw [QuarticCanonical.key_eq_iff]
  change (_ ∧ pairing v=_) ↔ _
  rw [← hp]
  constructor
  · exact And.right
  · intro he
    exact ⟨(tupleSupport_eq_of_pairing_eq v w hv hw he).trans hS,he⟩

/-- Canonical coefficients of any actual injective source family reduce to
literal finite delta sums over unordered physical matchings. -/
theorem coefficient_eq_pairing_sum {T : Type*} [Fintype T]
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (v : T → Fin 4 → V) (hv : ∀ t, Function.Injective (v t)) (a : T → ℝ)
    (w : Fin 4 → V) (hw : Function.Injective w)
    (S : QuarticCanonical.Support V) (m : Fin 3)
    (hS : QuarticCanonical.tupleSupport w hw=S)
    (hp : pairing w=QuarticCanonical.canonicalSupportPairing enum S m) :
    QuarticCanonical.coefficient enum v hv a (S,m) =
      ∑ t, if pairing (v t)=pairing w then a t else 0 := by
  unfold QuarticCanonical.coefficient
  apply Finset.sum_congr rfl
  intro t _
  simp only [key_eq_iff_pairing enum (v t) w (hv t) hw S m hS hp]

/-- Actual global residual coefficients are defined from the faithful literal
source family, with the same g/2 normalization as GlobalResidual.residual4. -/
def coefficient (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (S : QuarticCanonical.Support V) (m : Fin 3) : ℝ :=
  QuarticCanonical.coefficient enum
    (fun t : DistinctGlobalTerm ex ey => globalTermSites ex ey t.val)
    (fun t => t.property) (fun t => globalTermCoefficient K ex ey g t.val) (S,m)

/-- Pairing equality already enforces faithfulness, so removing the explicit
subtype changes no matching coefficient. -/
theorem sum_distinct_pairing_eq_sum (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (w : Fin 4 → V) (hw : Function.Injective w) :
    (∑ t : DistinctGlobalTerm ex ey,
      if pairing (globalTermSites ex ey t.val)=pairing w
      then globalTermCoefficient K ex ey g t.val else 0) =
    ∑ t : GlobalTerm ex ey, if pairing (globalTermSites ex ey t)=pairing w
      then globalTermCoefficient K ex ey g t else 0 := by
  have hh : (∑ t : GlobalTerm ex ey,
      if Function.Injective (globalTermSites ex ey t) then
        (if pairing (globalTermSites ex ey t)=pairing w
          then globalTermCoefficient K ex ey g t else 0) else 0) =
      ∑ t : DistinctGlobalTerm ex ey,
        if pairing (globalTermSites ex ey t.val)=pairing w
          then globalTermCoefficient K ex ey g t.val else 0 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro t; simp) _
  rw [← hh]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hp : pairing (globalTermSites ex ey t)=pairing w
  · simp [hp,injective_of_pairing_eq _ _ hw hp]
  · simp [hp]

/-- The canonical actual coefficient is the sum of the literal local matching
fibers, with exactly the original g/2 bond normalization. -/
theorem coefficient_eq_bond_matching_sum
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (w : Fin 4 → V) (hw : Function.Injective w)
    (S : QuarticCanonical.Support V) (m : Fin 3)
    (hS : QuarticCanonical.tupleSupport w hw=S)
    (hp : pairing w=QuarticCanonical.canonicalSupportPairing enum S m) :
    coefficient enum K ex ey g S m = (g/2) *
      ((∑ u, matchingCoefficient K u (ex u) w) +
        ∑ u, matchingCoefficient K u (ey u) w) := by
  unfold coefficient
  rw [coefficient_eq_pairing_sum enum _ _ _ w hw S m hS hp,
    sum_distinct_pairing_eq_sum K ex ey g w hw]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,globalTermCoefficient,
    globalTermSites]
  simp [forwardNeighbor,Fin.sum_univ_succ,matchingCoefficient,Finset.mul_sum,mul_add,mul_ite]

/-- Direct unordered-matching coefficient of the actual global finite source. -/
def globalMatchingCoefficient (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (w : Fin 4 → V) : ℝ :=
  ∑ t : GlobalTerm ex ey, if pairing (globalTermSites ex ey t)=pairing w
    then globalTermCoefficient K ex ey g t else 0

theorem coefficient_eq_globalMatchingCoefficient
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (w : Fin 4 → V) (hw : Function.Injective w)
    (S : QuarticCanonical.Support V) (m : Fin 3)
    (hS : QuarticCanonical.tupleSupport w hw=S)
    (hp : pairing w=QuarticCanonical.canonicalSupportPairing enum S m) :
    coefficient enum K ex ey g S m = globalMatchingCoefficient K ex ey g w := by
  unfold coefficient globalMatchingCoefficient
  rw [coefficient_eq_pairing_sum enum _ _ _ w hw S m hS hp,
    sum_distinct_pairing_eq_sum K ex ey g w hw]

def mapPhysicalPairing (e : V ≃ V) (p : Finset (Finset V)) : Finset (Finset V) :=
  p.image (Finset.image e)

theorem mapPhysicalPairing_injective (e : V ≃ V) :
    Function.Injective (mapPhysicalPairing e) :=
  Finset.image_injective (Finset.image_injective e.injective)

theorem pairing_equiv (e : V ≃ V) (s : Fin 4 → V) :
    pairing (fun i => e (s i)) = mapPhysicalPairing e (pairing s) := by
  simp [pairing,mapPhysicalPairing]

/-- Actual global source reindexing proves covariance of matching coefficients.
This has no translation-invariant norm or orbit-freeness premise. -/
theorem globalMatchingCoefficient_equiv (K : V → V → ℝ) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u)=e (ex u)) (hy : ∀ u, ey (e u)=e (ey u))
    (hK : ∀ a b, K (e a) (e b)=K a b) (g : ℝ) (w : Fin 4 → V) :
    globalMatchingCoefficient K ex ey g (fun i => e (w i)) =
      globalMatchingCoefficient K ex ey g w := by
  unfold globalMatchingCoefficient
  rw [← Equiv.sum_comp (globalTermEquiv ex ey e hx hy)]
  apply Finset.sum_congr rfl
  intro t _
  have hs : globalTermSites ex ey (globalTermEquiv ex ey e hx hy t) =
      fun i => e (globalTermSites ex ey t i) :=
    funext (globalTermSites_equiv ex ey e hx hy t)
  rw [hs,globalTermCoefficient_equiv K ex ey e hx hy hK,
    pairing_equiv,pairing_equiv]
  simp only [(mapPhysicalPairing_injective e).eq_iff]

theorem matchingTuple_translated_support
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (e : V ≃ V) (S : QuarticCanonical.Support V) (m : Fin 3) :
    QuarticCanonical.tupleSupport (fun i => e (matchingTuple enum S m i))
      (e.injective.comp (matchingTuple_injective enum S m)) =
      QuarticRootCounting.supportEquiv e S := by
  apply Subtype.ext
  have hh : Finset.univ.image (matchingTuple enum S m)=S.val :=
    congrArg Subtype.val (matchingTuple_support enum S m)
  change Finset.univ.image (fun i => e (matchingTuple enum S m i)) = S.val.map e.toEmbedding
  rw [Finset.map_eq_image,← hh,Finset.image_image]
  rfl

theorem matchingTuple_translated_pairing
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (e : V ≃ V) (S : QuarticCanonical.Support V) (m : Fin 3) :
    pairing (fun i => e (matchingTuple enum S m i)) =
      QuarticCanonical.canonicalSupportPairing enum (QuarticRootCounting.supportEquiv e S)
        (QuarticCanonical.matchingEquiv enum e S m) := by
  rw [pairing_equiv,matchingTuple_pairing]
  calc
    _ = QuarticCanonical.mapPairing (fun i => e (QuarticCanonical.tuple enum S i))
        (QuarticCanonical.canonicalPairing m) := by
      simp [mapPhysicalPairing,QuarticCanonical.canonicalSupportPairing,
        QuarticCanonical.mapPairing,Finset.image_image,Function.comp_def]
    _ = _ := QuarticCanonical.canonicalSupportPairing_transport enum e S m

/-- Actual signed canonical coefficients transform by the constructed matching
permutation. This discharges covariance from the literal finite source action. -/
theorem coefficient_equiv
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u)=e (ex u)) (hy : ∀ u, ey (e u)=e (ey u))
    (hK : ∀ a b, K (e a) (e b)=K a b) (g : ℝ)
    (S : QuarticCanonical.Support V) (m : Fin 3) :
    coefficient enum K ex ey g (QuarticRootCounting.supportEquiv e S)
      (QuarticCanonical.matchingEquiv enum e S m) = coefficient enum K ex ey g S m := by
  rw [coefficient_eq_globalMatchingCoefficient enum K ex ey g
    (fun i => e (matchingTuple enum S m i))
    (e.injective.comp (matchingTuple_injective enum S m)) _ _
    (matchingTuple_translated_support enum e S m) (matchingTuple_translated_pairing enum e S m)]
  rw [globalMatchingCoefficient_equiv K ex ey e hx hy hK]
  exact (coefficient_eq_globalMatchingCoefficient enum K ex ey g
    (matchingTuple enum S m) (matchingTuple_injective enum S m) S m
    (matchingTuple_support enum S m) (matchingTuple_pairing enum S m)).symm

/-- The exact matching Gram weight is invariant under genuine source translation. -/
theorem matchingWeight_equiv
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey e : V ≃ V)
    (hx : ∀ u, ex (e u)=e (ex u)) (hy : ∀ u, ey (e u)=e (ey u))
    (hK : ∀ a b, K (e a) (e b)=K a b) (g : ℝ)
    (S : QuarticCanonical.Support V) :
    QuarticRootCounting.matchingWeight
      (coefficient enum K ex ey g (QuarticRootCounting.supportEquiv e S)) =
    QuarticRootCounting.matchingWeight (coefficient enum K ex ey g S) := by
  have hh := QuarticRootCounting.matchingWeight_equiv
    (coefficient enum K ex ey g (QuarticRootCounting.supportEquiv e S))
    (QuarticCanonical.matchingEquiv enum e S)
  simpa only [coefficient_equiv enum K ex ey e hx hy hK] using hh.symm

/-- Exact rooted area/4 count for the actual signed canonical coefficients.
Periodic four-site supports are counted correctly without stabilizer assumptions. -/
theorem actual_rooted_weight [AddGroup V]
    (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V)
    (hx : ∀ u t, ex (u+t)=ex u+t) (hy : ∀ u t, ey (u+t)=ey u+t)
    (hK : ∀ a b t, K (a+t) (b+t)=K a b) (g : ℝ) :
    (∑ S : QuarticCanonical.Support V,
      QuarticRootCounting.matchingWeight (coefficient enum K ex ey g S)) =
    (Fintype.card V : ℝ)/4 * QuarticRootCounting.rootedMass
      (fun S => QuarticRootCounting.matchingWeight (coefficient enum K ex ey g S)) 0 := by
  apply QuarticRootCounting.additive_totalMass_eq_card_div_four_rooted
  intro t S
  exact matchingWeight_equiv enum K ex ey (Equiv.addRight t)
    (fun u => hx u t) (fun u => hy u t) (fun a b => hK a b t) g S

/-- Exact canonical three-matching regrouping of the literal physical residual. -/
theorem residual4_eq_canonical (enum : ∀ S : QuarticCanonical.Support V, Fin 4 ≃ S.val)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V) =
      ∑ S : QuarticCanonical.Support V, ∑ m : Fin 3,
        coefficient enum K ex ey g S m •
          QuarticMatching.matchingOperator (QuarticCanonical.tuple enum S) m := by
  rw [coe_residual4_eq_distinct_terms]
  exact QuarticCanonical.regroup_by_support enum
    (fun t : DistinctGlobalTerm ex ey => globalTermSites ex ey t.val)
    (fun t => t.property) (fun t => globalTermCoefficient K ex ey g t.val)

end BilayerDressed.QuarticActualCoefficients
