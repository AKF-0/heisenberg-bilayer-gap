import Dressed.CubicSeedSupersolution
import Dressed.QuadraticRegroupingAssembly

/-!
# The actual cubic degree-two residual

The physical forward-edge residual is regrouped using the actual cubic kernel.
Translation reduces its exact vacuum norm and absolute pair coefficient to one
rooted row. No degree-four/six estimate or interval envelope is assumed here.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicResidualPair
open BilayerGap BilayerDressed.SeedGraphs BilayerDressed.CubicSeedChecks
open BilayerDressed.CubicWick.FourRegularData BilayerDressed.QuadraticRegrouping
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem cubicKernel_diagonal (G : FourRegularData V) (g : ℝ) (i : V) :
    cubicKernel G g i i=0 := by
  simp [cubicKernel,cube,offDiagonal,G.diagonal,G.cube_diagonal]

 theorem cubicKernel_transpose (G : FourRegularData V) (g : ℝ) :
    (cubicKernel G g).transpose=cubicKernel G g := by
  ext i j
  exact cubicKernel_symmetric G g j i

 theorem compactCoefficient_diagonal (D K : Matrix V V ℝ)
    (hD : ∀ i,D i i=0) (hK : ∀ i,K i i=0) (g : ℝ) (i : V) :
    compactCoefficient D K g i i=0 := by
  simp [compactCoefficient,quadraticNonlinear,offDiagonal,
    Matrix.diagonal_mul,Matrix.mul_diagonal,hD,hK]

 theorem compactCoefficient_transpose (D K : Matrix V V ℝ)
    (hD : D.transpose=D) (hK : K.transpose=K) (g : ℝ) :
    (compactCoefficient D K g).transpose=compactCoefficient D K g := by
  have hh : (show Matrix V V ℝ from fun i j => D i j*K i j).transpose=
      (fun i j => D i j*K i j) := by
    ext i j
    change D j i*K j i=D i j*K i j
    rw [← Matrix.transpose_apply D,← Matrix.transpose_apply K,hD,hK]
  have hh3 : (show Matrix V V ℝ from fun i j => D i j*K i j*K i j).transpose=
      (fun i j => D i j*K i j*K i j) := by
    ext i j
    change D j i*K j i*K j i=D i j*K i j*K i j
    rw [← Matrix.transpose_apply D,← Matrix.transpose_apply K,hD,hK]
  simp only [compactCoefficient,quadraticNonlinear,Matrix.transpose_add,
    Matrix.transpose_sub,Matrix.transpose_smul,transpose_offDiagonal,
    Matrix.transpose_mul,Matrix.diagonal_transpose,hD,hK,hh,hh3]
  rw [show K*D+D*K=D*K+K*D by abel,
    show K*(D*K)=K*D*K by rw [mul_assoc]]
  congr 2
  abel_nf

/-- The cubic ansatz remains a polynomial in the adjacency, hence commutes with it. -/
 theorem adjacency_commute_cubic (G : FourRegularData V) (g : ℝ) :
    G.adjacency*cubicKernel G g=cubicKernel G g*G.adjacency := by
  have ho : offDiagonal (G.adjacency*G.adjacency)=
      G.adjacency*G.adjacency-(4 : ℝ) • (1 : Matrix V V ℝ) := by
    ext i j; exact G.off_square_eq i j
  simp only [cubicKernel,ho,cube,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,Matrix.one_mul,mul_assoc]

/-- The degree-two coefficient, not the older quadratic-ansatz residual. -/
def residual (G : FourRegularData V) (g : ℝ) : Matrix V V ℝ :=
  compactCoefficient G.adjacency (cubicKernel G g) g

 theorem residual_symmetric (G : FourRegularData V) (g : ℝ) (u v : V) :
    residual G g u v=residual G g v u := by
  have hd : G.adjacency.transpose=G.adjacency := by ext i j; exact G.symmetric j i
  exact (congrFun (congrFun
    (compactCoefficient_transpose G.adjacency (cubicKernel G g) hd
      (cubicKernel_transpose G g) g) u) v).symm

 theorem residual_diagonal (G : FourRegularData V) (g : ℝ) (u : V) :
    residual G g u u=0 :=
  compactCoefficient_diagonal G.adjacency (cubicKernel G g) G.diagonal
    (cubicKernel_diagonal G g) g u

/-- Every physical forward bond is counted once; the ordered-adjacency factor
is discharged by the actual incidence identity. -/
 theorem physical_edge_compact {R : Type*} [CommRing R] [Algebra ℝ R]
    (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (c : Torus.Vertex n m → Fin 3 → R) (hc : ∀ u α,c u α*c u α=0) (g : ℝ) :
    (2 : ℝ) • GlobalResidual.pairPolynomial c (cubicKernel (graph n m h) g)+
      (g/2) • ((∑ u : Torus.Vertex n m,
        literalBondR2 c (cubicKernel (graph n m h) g) u (Torus.xNext n m u))+
        (∑ u : Torus.Vertex n m,
        literalBondR2 c (cubicKernel (graph n m h) g) u (Torus.yNext n m u))) =
      GlobalResidual.pairPolynomial c (residual (graph n m h) g) := by
  let G := graph n m h
  have hd : G.adjacency.transpose=G.adjacency := by ext i j; exact G.symmetric j i
  have hh := ordered_residual_compact G.adjacency (cubicKernel G g) hd G.diagonal
    (cubicKernel_transpose G g) (cubicKernel_diagonal G g) c hc g
  have hs := incidence_symmetric_sum n m h hi (literalBondR2 c (cubicKernel G g))
    (literalBondR2_symmetric c hc (cubicKernel G g)
      (cubicKernel_transpose G g) (cubicKernel_diagonal G g))
  change (∑ u,∑ v,G.adjacency u v • literalBondR2 c (cubicKernel G g) u v)=_ at hs
  rw [hs,smul_smul,show (g/4)*2=g/2 by ring] at hh
  exact hh

/-- The commutative polynomial is evaluated in genuine creation matrices. -/
 theorem coe_pairPolynomial (K : Matrix V V ℝ) :
    ((GlobalResidual.pairPolynomial GlobalResidual.C K : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V)=pairKernelS K :=
  GlobalResidual.coe_S K

/-- The literal physical degree-two operator, before matrix coefficient regrouping. -/
def physicalPairResidual (n m : ℕ) (h : Conditions n m) (g : ℝ) :
    ConfigurationMatrix (Torus.Vertex n m) :=
  (2 : ℝ) • pairKernelS (cubicKernel (graph n m h) g)+
    (g/2) • ((∑ u : Torus.Vertex n m,
      ((literalBondR2 GlobalResidual.C (cubicKernel (graph n m h) g) u (Torus.xNext n m u) :
        GlobalResidual.creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m)))+
      (∑ u : Torus.Vertex n m,
      ((literalBondR2 GlobalResidual.C (cubicKernel (graph n m h) g) u (Torus.yNext n m u) :
        GlobalResidual.creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))))

 theorem physicalPairResidual_eq (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) :
    physicalPairResidual n m h g=pairKernelS (residual (graph n m h) g) := by
  have hh := congrArg (GlobalResidual.creationAlgebra (Torus.Vertex n m)).val
    (physical_edge_compact n m h hi GlobalResidual.C
      (fun u α => GlobalResidual.C_mul_same u α α) g)
  simp only [map_add,map_smul,map_sum] at hh
  simpa only [Subalgebra.val_apply,coe_pairPolynomial,physicalPairResidual] using hh

section Translation
variable {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]

/-- Simultaneous translation invariance, retaining the actual matrix entries. -/
def TranslationInvariant (A : Matrix X X ℝ) : Prop :=
  ∀ u v t,A (u+t) (v+t)=A u v

omit [DecidableEq X] in
 theorem translation_mul (A B : Matrix X X ℝ)
    (hA : TranslationInvariant A) (hB : TranslationInvariant B) :
    TranslationInvariant (A*B) := by
  intro u v t
  simp only [Matrix.mul_apply]
  calc
    _ = ∑ k,A (u+t) (k+t)*B (k+t) (v+t) :=
      (Equiv.sum_comp (Equiv.addRight t) (fun k => A (u+t) k*B k (v+t))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hA u k t,hB k v t]

omit [Fintype X] [DecidableEq X] in
 theorem translation_rooted (A : Matrix X X ℝ) (hA : TranslationInvariant A) (u v : X) :
    A u v=A 0 (v-u) := by
  simpa using hA 0 (v-u) u

omit [DecidableEq X] in
 theorem translation_row_sum (A : Matrix X X ℝ) (hA : TranslationInvariant A) (u : X) :
    (∑ v,A u v)=∑ v,A 0 v := by
  simp_rw [translation_rooted A hA u]
  exact (Equiv.subRight u).sum_comp _

omit [DecidableEq X] in
 theorem translation_full_sum (A : Matrix X X ℝ) (hA : TranslationInvariant A) :
    (∑ u,∑ v,A u v)=(Fintype.card X : ℝ)*∑ v,A 0 v := by
  simp_rw [translation_row_sum A hA]
  simp

 theorem translation_compact (D K : Matrix X X ℝ)
    (hD : TranslationInvariant D) (hK : TranslationInvariant K) (g : ℝ) :
    TranslationInvariant (compactCoefficient D K g) := by
  have hDK := translation_mul D K hD hK
  have hKD := translation_mul K D hK hD
  have hKDK := translation_mul (K*D) K hKD hK
  intro u v t
  simp only [compactCoefficient,quadraticNonlinear,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,offDiagonal,add_left_inj,
    Matrix.diagonal_mul,Matrix.mul_diagonal,hD u v t,hK u v t,
    hDK u v t,hKD u v t,hKDK u v t,hDK u u t,hDK v v t]

end Translation

section Torus
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)] (h : Conditions n m)

 theorem adjacency_translation : TranslationInvariant (graph n m h).adjacency := by
  intro u v t
  exact congrArg (fun k : ℕ => (k : ℝ)) (adjacency_translate n m u v t)

 theorem kernel_translation (g : ℝ) : TranslationInvariant (cubicKernel (graph n m h) g) := by
  have hD := adjacency_translation n m h
  have hD2 := translation_mul _ _ hD hD
  have hD3 := translation_mul _ _ hD2 hD
  intro u v t
  simp only [cubicKernel,cube,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,offDiagonal,add_left_inj,hD u v t,hD2 u v t,hD3 u v t]

 theorem residual_translation (g : ℝ) : TranslationInvariant (residual (graph n m h) g) :=
  translation_compact _ _ (adjacency_translation n m h) (kernel_translation n m h g) g

 theorem residual_rooted (g : ℝ) (u v : Torus.Vertex n m) :
    residual (graph n m h) g u v=residual (graph n m h) g 0 (v-u) :=
  translation_rooted _ (residual_translation n m h g) u v

/-- Exact cubic rooted row from graph walk counts. -/
def rootKernel (g : ℝ) (q : Torus.Vertex n m) : ℝ :=
  -(g/4)*(adjacencyNat n m 0 q : ℝ)+
    (g^2/8)*((offWalk2 n m 0 q : ℝ)-(adjacencyNat n m 0 q : ℝ))-
    (g^3/64)*(5*(walk3 n m 0 q : ℝ)-4*(offWalk2 n m 0 q : ℝ)-
      40*(adjacencyNat n m 0 q : ℝ))

 theorem kernel_root (hi : IncidenceIdentity n m) (g : ℝ) (q : Torus.Vertex n m) :
    cubicKernel (graph n m h) g 0 q=rootKernel n m g q := by
  simp only [cubicKernel,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [graph_cube_cast n m h hi,graph_off_square_cast n m h hi]
  rfl

/-- Neighbor convolution in the graph checker's root-row convention. -/
def rootDK (g : ℝ) (q : Torus.Vertex n m) : ℝ :=
  ∑ r,rootKernel n m g r*(adjacencyNat n m r q : ℝ)

/-- The double convolution is evaluated on the actual finite torus. -/
def rootKDK (g : ℝ) (q : Torus.Vertex n m) : ℝ :=
  ∑ r,rootKernel n m g r*rootDK n m g (q-r)

 theorem adjacency_kernel_root (hi : IncidenceIdentity n m) (g : ℝ) (q : Torus.Vertex n m) :
    ((graph n m h).adjacency*cubicKernel (graph n m h) g) 0 q=rootDK n m g q := by
  rw [adjacency_commute_cubic]
  simp only [Matrix.mul_apply,kernel_root n m h hi]
  rfl

 theorem kernel_adjacency_kernel_root (hi : IncidenceIdentity n m) (g : ℝ)
    (q : Torus.Vertex n m) :
    (cubicKernel (graph n m h) g*(graph n m h).adjacency*cubicKernel (graph n m h) g) 0 q=
      rootKDK n m g q := by
  rw [mul_assoc]
  rw [Matrix.mul_apply]
  unfold rootKDK
  apply Finset.sum_congr rfl
  intro r _
  rw [kernel_root n m h hi,
    translation_rooted _ (translation_mul _ _ (adjacency_translation n m h)
      (kernel_translation n m h g)) r q,adjacency_kernel_root n m h hi]

/-- The exact degree-two scalar polynomial used by the .1 graph certificate. -/
def rootResidual (g : ℝ) (q : Torus.Vertex n m) : ℝ :=
  if q=0 then 0 else
    2*rootKernel n m g q+(g/2)*(adjacencyNat n m 0 q : ℝ)+g*rootDK n m g q-
      g*(adjacencyNat n m 0 q : ℝ)*rootKernel n m g q+
      (g/2)*rootKDK n m g q-4*g*rootDK n m g 0*rootKernel n m g q+
      2*g*(adjacencyNat n m 0 q : ℝ)*(rootKernel n m g q)^2

 theorem residual_root (hi : IncidenceIdentity n m) (g : ℝ) (q : Torus.Vertex n m) :
    residual (graph n m h) g 0 q=rootResidual n m g q := by
  by_cases hq : q=0
  · subst q
    simp [residual_diagonal,rootResidual]
  · have h0q : (0 : Torus.Vertex n m)≠q := Ne.symm hq
    have hz : ((graph n m h).adjacency*cubicKernel (graph n m h) g) q q=
        ((graph n m h).adjacency*cubicKernel (graph n m h) g) 0 0 := by
      simpa using translation_rooted _
        (translation_mul _ _ (adjacency_translation n m h) (kernel_translation n m h g)) q q
    simp only [residual,compactCoefficient,quadraticNonlinear,Matrix.add_apply,
      Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,offDiagonal,if_neg h0q,
      Matrix.diagonal_mul,Matrix.mul_diagonal]
    rw [hz,kernel_adjacency_kernel_root n m h hi,←adjacency_commute_cubic,
      adjacency_kernel_root n m h hi,adjacency_kernel_root n m h hi,kernel_root n m h hi]
    simp only [rootResidual,if_neg hq]
    change _ = _
    dsimp only [graph]
    ring

/-- Exact physical vacuum norm, with three triplet colors and the ordered-pair half. -/
 theorem residual_vacuum_norm_sq (hi : IncidenceIdentity n m) (g : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
      (pairKernelS (residual (graph n m h) g)) vacuumVector‖^2=
      (3*((2*n)*(2*m) : ℝ)/2)*∑ q,(rootResidual n m g q)^2 := by
  rw [pairKernelS_vacuum_norm_sq _ (residual_symmetric _ _) (residual_diagonal _ _)]
  have ht : TranslationInvariant (fun u v => (residual (graph n m h) g u v)^2) := by
    intro u v t
    dsimp only
    rw [residual_translation n m h g u v t]
  rw [translation_full_sum _ ht]
  simp_rw [residual_root n m h hi]
  simp only [Torus.Vertex,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  ring

/-- The absolute pair-mean coefficient before any covariance envelope estimate. -/
def pairMeanCoefficient (g : ℝ) (L : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℝ) : ℝ :=
  (3/2 : ℝ)*∑ u,∑ v,|residual (graph n m h) g u v| *L u v

 theorem pairMeanCoefficient_root (hi : IncidenceIdentity n m) (g : ℝ)
    (L : Matrix (Torus.Vertex n m) (Torus.Vertex n m) ℝ) (hL : TranslationInvariant L) :
    pairMeanCoefficient n m h g L=
      (((2*n)*(2*m) : ℝ)/2)*∑ q,3*|rootResidual n m g q| *L 0 q := by
  have ht : TranslationInvariant (fun u v => |residual (graph n m h) g u v| *L u v) := by
    intro u v t
    dsimp only
    rw [residual_translation n m h g u v t,hL u v t]
  unfold pairMeanCoefficient
  rw [translation_full_sum _ ht]
  simp_rw [residual_root n m h hi]
  simp only [Torus.Vertex,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  rw [show (∑ q,3*|rootResidual n m g q| *L 0 q)=
      3*∑ q,|rootResidual n m g q| *L 0 q by simp [Finset.mul_sum,mul_assoc]]
  ring

/-- The exact norm statement also applies to the unregrouped physical operator. -/
 theorem physicalPairResidual_vacuum_norm_sq (hi : IncidenceIdentity n m) (g : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
      (physicalPairResidual n m h g) vacuumVector‖^2=
      (3*((2*n)*(2*m) : ℝ)/2)*∑ q,(rootResidual n m g q)^2 := by
  rw [physicalPairResidual_eq n m h hi]
  exact residual_vacuum_norm_sq n m h hi g

 theorem covarianceMajorant_translation (t τ : ℝ) :
    TranslationInvariant (FiniteWick.covarianceMajorant (positiveKernel n m h t) τ) := by
  intro u v r
  simp only [FiniteWick.covarianceMajorant,positiveKernel,kernel_translation n m h t u v r]

/-- The endpoint kernel may differ from the residual coupling. This is the
exact coefficient underlying the checker's uniform pair-mean envelope. -/
 theorem pairMeanCoefficient_majorant_root (hi : IncidenceIdentity n m) (g t τ : ℝ) :
    pairMeanCoefficient n m h g (FiniteWick.covarianceMajorant (positiveKernel n m h t) τ)=
      (((2*n)*(2*m) : ℝ)/2)*∑ q,3*|rootResidual n m g q| * (|rootKernel n m t q|+τ) := by
  rw [pairMeanCoefficient_root n m h hi g _ (covarianceMajorant_translation n m h t τ)]
  simp only [FiniteWick.covarianceMajorant,positiveKernel,kernel_root n m h hi]

/-- A coefficient envelope is a transparent intermediate input, not a numerical
certificate. Later interval proofs must discharge every entry of `hE`. -/
 theorem pairMeanCoefficient_le_envelope (hi : IncidenceIdentity n m) (g t τ : ℝ)
    (hτ : 0≤τ) (E : Torus.Vertex n m → ℝ)
    (hE : ∀ q,|rootResidual n m g q|≤E q) :
    pairMeanCoefficient n m h g (FiniteWick.covarianceMajorant (positiveKernel n m h t) τ)≤
      (((2*n)*(2*m) : ℝ)/2)*∑ q,3*E q*(|rootKernel n m t q|+τ) := by
  rw [pairMeanCoefficient_majorant_root n m h hi]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE q) (by norm_num))
    (add_nonneg (abs_nonneg _) hτ)

end Torus
end BilayerDressed.CubicResidualPair
