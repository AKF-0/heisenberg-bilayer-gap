import Dressed.QuadraticRegrouping
import Dressed.SeedGraphIncidence

/-! Literal physical-edge R2 and the compact coefficient are identified by
finite sum identities, not by an assumed residual certificate. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuadraticRegrouping
variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R] [Algebra ℝ R]

 theorem pairPolynomial_eq_half_bilinear (K : Matrix V V ℝ) (c : V → Fin 3 → R) :
    GlobalResidual.pairPolynomial c K =
      (1/2 : ℝ) • ∑ α,bilinear K (fun i => c i α) (fun i => c i α) := by
  unfold GlobalResidual.pairPolynomial
  simp only [Finset.smul_sum]
  calc
    _ = ∑ i,∑ α : Fin 3,∑ j,(K i j/2) • (c i α*c j α) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ α : Fin 3,∑ i,∑ j,(K i j/2) • (c i α*c j α) := Finset.sum_comm
    _ = _ := by
      simp only [bilinear,Finset.smul_sum,smul_smul]
      congr 1
      funext α
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring

/-- The actual local polynomial with both endpoint rows excluded. -/
def literalBondR2 (c : V → Fin 3 → R) (K : Matrix V V ℝ) (u v : V) : R :=
  GlobalResidual.bondR2 (c u) (c v)
    (GlobalResidual.outsideField c K u v u) (GlobalResidual.outsideField c K u v v)
    (algebraMap ℝ R (K u v))

 theorem literalBondR2_eq (c : V → Fin 3 → R) (hc : ∀ u α,c u α*c u α=0)
    (K : Matrix V V ℝ) (hK : K.transpose=K) (hdiag : ∀ i,K i i=0)
    (u v : V) (huv : u≠v) :
    literalBondR2 c K u v=∑ α,fullBond K (fun w => c w α) u v :=
  bondR2_eq_fullBond c hc K hK hdiag u v huv

 theorem fullBond_symmetric (K : Matrix V V ℝ) (hK : K.transpose=K)
    (x : V → R) (u v : V) : fullBond K x u v=fullBond K x v u := by
  have hk : K v u=K u v := congrFun (congrFun hK u) v
  simp only [fullBond,hk,Algebra.smul_def]
  ring

 theorem literalBondR2_symmetric (c : V → Fin 3 → R) (hc : ∀ u α,c u α*c u α=0)
    (K : Matrix V V ℝ) (hK : K.transpose=K) (hdiag : ∀ i,K i i=0)
    (u v : V) : literalBondR2 c K u v=literalBondR2 c K v u := by
  by_cases huv : u=v
  · subst v; rfl
  · rw [literalBondR2_eq c hc K hK hdiag u v huv,
      literalBondR2_eq c hc K hK hdiag v u (Ne.symm huv)]
    apply Finset.sum_congr rfl
    intro α _
    exact fullBond_symmetric K hK _ u v

/-- Exact ordered-adjacency regrouping, including the physical factor one-half. -/
 theorem ordered_residual_compact (D K : Matrix V V ℝ)
    (hD : D.transpose=D) (hDdiag : ∀ i,D i i=0)
    (hK : K.transpose=K) (hKdiag : ∀ i,K i i=0)
    (c : V → Fin 3 → R) (hc : ∀ u α,c u α*c u α=0) (g : ℝ) :
    (2 : ℝ) • GlobalResidual.pairPolynomial c K+
      (g/4) • (∑ u,∑ v,D u v • literalBondR2 c K u v) =
      GlobalResidual.pairPolynomial c (compactCoefficient D K g) := by
  have hl : (∑ u,∑ v,D u v • literalBondR2 c K u v)=
      ∑ α : Fin 3,∑ u,∑ v,D u v • fullBond K (fun w => c w α) u v := by
    calc
      _ = ∑ u,∑ v,∑ α : Fin 3,D u v • fullBond K (fun w => c w α) u v := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        by_cases huv : u=v
        · subst v; simp [hDdiag]
        · rw [literalBondR2_eq c hc K hK hKdiag u v huv,Finset.smul_sum]
      _ = ∑ u,∑ α : Fin 3,∑ v,D u v • fullBond K (fun w => c w α) u v := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hl,pairPolynomial_eq_half_bilinear,pairPolynomial_eq_half_bilinear,
    smul_smul]
  norm_num
  simp only [Finset.smul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  simpa only [Finset.smul_sum] using
    one_color_compact D K hD hK (fun i => c i α) (fun i => hc i α) g

/-- The exact physical forward-bond R2 equals the compact coefficient on any
seed torus whose simple-adjacency incidence certificate has been established. -/
 theorem physical_edge_compact (n m : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m)
    (c : BilayerGap.Torus.Vertex n m → Fin 3 → R)
    (hc : ∀ u α,c u α*c u α=0) (g : ℝ) :
    (2 : ℝ) • GlobalResidual.pairPolynomial c ((SeedGraphs.graph n m h).kernel g)+
      (g/2) • ((∑ u : BilayerGap.Torus.Vertex n m,
        literalBondR2 c ((SeedGraphs.graph n m h).kernel g) u (BilayerGap.Torus.xNext n m u))+
        (∑ u : BilayerGap.Torus.Vertex n m,
        literalBondR2 c ((SeedGraphs.graph n m h).kernel g) u (BilayerGap.Torus.yNext n m u))) =
      GlobalResidual.pairPolynomial c ((SeedGraphs.graph n m h).quadraticResidual g) := by
  let G := SeedGraphs.graph n m h
  have hd : G.adjacency.transpose=G.adjacency := by ext i j; exact G.symmetric j i
  have hk : (G.kernel g).transpose=G.kernel g := by ext i j; exact G.kernel_symmetric g j i
  have hh := ordered_residual_compact G.adjacency (G.kernel g) hd G.diagonal
    hk (G.kernel_diagonal g) c hc g
  have hs := SeedGraphs.incidence_symmetric_sum n m h hi
    (literalBondR2 c (G.kernel g))
    (literalBondR2_symmetric c hc (G.kernel g) hk (G.kernel_diagonal g))
  change (∑ u,∑ v,G.adjacency u v • literalBondR2 c (G.kernel g) u v)=_ at hs
  rw [hs,smul_smul,compactCoefficient_eq] at hh
  rw [show (g/4)*2=g/2 by ring] at hh
  exact hh

end BilayerDressed.QuadraticRegrouping
