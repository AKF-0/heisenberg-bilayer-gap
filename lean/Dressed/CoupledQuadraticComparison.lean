import Dressed.GlobalCartesianBasis
import Dressed.FiniteOccupationTotalCutoff

/-!
# Actual Cartesian Hamiltonian versus a coupled finite quadratic reference

The normal part is bounded by an explicit local sum of squares. The two
permutation-edge families count each endpoint twice, giving degree four without
any volume loss. The reference is then identified with the compression of actual
finite total-cutoff occupation matrices, before any orthogonal mode rotation.
-/
noncomputable section
open scoped BigOperators Kronecker RealInnerProductSpace
namespace BilayerDressed.CoupledQuadratic
open Matrix BilayerGap
set_option maxHeartbeats 1400000
set_option maxRecDepth 4000
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev LocalOp := Matrix LocalBond.PairIndex LocalBond.PairIndex ℝ

/-- The actual three-color local pair-creation matrix. -/
def localPairCreate : LocalOp := ∑ α : Fin 3, rungCreate α ⊗ₖ rungCreate α

/-- Creation plus its real adjoint, with each local color counted once. -/
def localPair : LocalOp := localPairCreate + localPairCreate.transpose

/-- The number-conserving part of the actual Cartesian bond. -/
def localNormal : LocalOp := CartesianBasis.bond - (1/2 : ℝ) • localPair

/-- The local normal interaction shifted by half the endpoint number. -/
def localNormalGram : LocalOp := localNormal + (1/2 : ℝ) • PhysicalGram.localNumber

/-- An exact identity with the frozen explicit normal sum of squares. -/
theorem localNormalGram_identity (z : LocalBond.RealPair) :
    dotProduct z (localNormalGram.mulVec z) = LocalBond.normalSOS z := by
  simp only [localNormalGram, localNormal, CartesianBasis.bond,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    PhysicalGram.localNumber_quadratic, LocalBond.twiceBond_mulVec]
  simp [localPair, localPairCreate, rungCreate, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.single,
    Fintype.sum_prod_type, Fin.sum_univ_succ, LocalBond.action,
    LocalBond.normalSOS, LocalBond.numberForm, LocalBond.stNorm,
    LocalBond.ttNorm, LocalBond.offNorm]
  ring

/-- Positivity is proved from the displayed squares, not assumed as an operator premise. -/
theorem localNormalGram_nonneg (z : LocalBond.RealPair) :
    0 ≤ dotProduct z (localNormalGram.mulVec z) := by
  rw [localNormalGram_identity]
  unfold LocalBond.normalSOS LocalBond.offNorm
  positivity

/-- The genuine normal bond obeys V_normal ≥ −(n_u+n_v)/2. -/
theorem localNormal_lower_bound (z : LocalBond.RealPair) :
    -(1/2 : ℝ) * LocalBond.numberForm z ≤ dotProduct z (localNormal.mulVec z) := by
  have h := localNormalGram_nonneg z
  simp only [localNormalGram, Matrix.add_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul,
    PhysicalGram.localNumber_quadratic] at h
  linarith

/-- Transpose commutes with the actual entry-defined tensor lift. -/
theorem pairLift_transpose (A : LocalOp) (u v : V) :
    Torus.pairLift A.transpose u v = (Torus.pairLift A u v).transpose := by
  ext s t
  have he : (∀ w, w ≠ u → w ≠ v → s w = t w) ↔
      (∀ w, w ≠ u → w ≠ v → t w = s w) := by
    constructor <;> intro h w hwu hwv <;> exact (h w hwu hwv).symm
  simp only [Torus.pairLift, Matrix.transpose_apply, he]
  split_ifs <;> rfl

/-- Pair creation is lifted as an actual product of distinct-site creations. -/
theorem pairLift_localPairCreate (u v : V) (huv : u ≠ v) :
    Torus.pairLift localPairCreate u v = pairCreate u v := by
  simp only [localPairCreate, Torus.pairLift_sum, pairCreate, globalCreate,
    Torus.siteLift_mul_distinct _ _ huv]

/-- The global pair term includes the adjoint, without an extra edge factor. -/
def pair (u v : V) : ConfigurationMatrix V := pairCreate u v + (pairCreate u v).transpose

theorem pairLift_localPair (u v : V) (huv : u ≠ v) :
    Torus.pairLift localPair u v = pair u v := by
  rw [localPair, Torus.pairLift_add, pairLift_transpose,
    pairLift_localPairCreate u v huv]
  rfl

theorem pairLift_localNormalGram (u v : V) (huv : u ≠ v) :
    Torus.pairLift localNormalGram u v =
      Torus.pairLift CartesianBasis.bond u v - (1/2 : ℝ) • pair u v +
        (1/2 : ℝ) • (Torus.siteLift RealRungOperators.h u +
          Torus.siteLift RealRungOperators.h v) := by
  simp only [localNormalGram, localNormal, Torus.pairLift_add,
    Torus.pairLift_sub, Torus.pairLift_smul, pairLift_localPair u v huv,
    PhysicalGram.localNumber, Torus.pairLift_left _ huv, Torus.pairLift_right _ huv]

/-- One oriented permutation family counts every endpoint exactly twice. -/
theorem edge_sum_lower (e : Equiv.Perm V) (he : ∀ v, v ≠ e v)
    (x : Configuration V → ℝ) :
    (1/2 : ℝ) * (∑ v, PhysicalGram.qform (pair v (e v)) x) -
        PhysicalGram.qform (TripletNumber.number : ConfigurationMatrix V) x ≤
      ∑ v, PhysicalGram.qform (Torus.pairLift CartesianBasis.bond v (e v)) x := by
  have hn : 0 ≤ ∑ v : V, PhysicalGram.qform
      (Torus.pairLift localNormalGram v (e v)) x :=
    Finset.sum_nonneg fun v _ => PhysicalGram.pairLift_quadratic_nonneg
      localNormalGram localNormalGram_nonneg v (e v) (he v) x
  simp_rw [pairLift_localNormalGram _ _ (he _), PhysicalGram.qform_add,
    PhysicalGram.qform_sub, PhysicalGram.qform_smul] at hn
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hn
  simp_rw [PhysicalGram.qform_add] at hn
  rw [PhysicalGram.endpoint_number_sum] at hn
  change 0 ≤ _ - _ + (1/2 : ℝ) * (2 * PhysicalGram.qform TripletNumber.number x) at hn
  linarith

/-- The two positive-direction families retain parallel edges on a length-two
period. For ordinary square tori of lengths at least four they are the usual
single-count undirected edge list. -/
def edgePairSum (ex ey : Equiv.Perm V) : ConfigurationMatrix V :=
  (∑ v, pair v (ex v)) + ∑ v, pair v (ey v)

/-- The physical hard-core quadratic comparison matrix. -/
def hardCoreReference (ex ey : Equiv.Perm V) (g : ℝ) : ConfigurationMatrix V :=
  (1-2*g) • TripletNumber.number + (g/2) • edgePairSum ex ey

/-- Actual degree-four operator-form comparison, with no scalar energy-loss premise. -/
theorem graphHamiltonian_lower (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : Configuration V → ℝ) :
    PhysicalGram.qform (hardCoreReference ex ey g) x ≤
      PhysicalGram.qform (CartesianBasis.graphHamiltonian ex ey g) x := by
  have h₁ := mul_le_mul_of_nonneg_left (edge_sum_lower ex hx x) hg
  have h₂ := mul_le_mul_of_nonneg_left (edge_sum_lower ey hy x) hg
  simp only [hardCoreReference, edgePairSum, CartesianBasis.graphHamiltonian_as_bonds,
    PhysicalGram.qform_add, PhysicalGram.qform_smul, PhysicalGram.qform_sum]
  nlinarith only [h₁, h₂]


open FiniteOccupation

/-- The actual total-cutoff creation pair plus its real adjoint. -/
def occupationPair {M N : ℕ} (i j : Mode V) : TotalCutoff.Op V M N :=
  TotalCutoff.create i * TotalCutoff.create j +
    ((TotalCutoff.create i : TotalCutoff.Op V M N) * TotalCutoff.create j).transpose

/-- The creation matrices commute even at the total-cutoff boundary. -/
theorem occupationPair_symm {M N : ℕ} (i j : Mode V) :
    (occupationPair i j : TotalCutoff.Op V M N) = occupationPair j i := by
  simp only [occupationPair, (TotalCutoff.create_commute i j).eq]

/-- The coupled finite quadratic matrix with the conventional symmetric-kernel half factor. -/
def coupledReference {M N : ℕ} (ω : ℝ) (K : Matrix (Mode V) (Mode V) ℝ) :
    TotalCutoff.Op V M N :=
  ω • TotalCutoff.number + (1/2 : ℝ) • ∑ i, ∑ j, K i j • occupationPair i j

/-- A spatial permutation acts without changing the triplet color. -/
def modePerm (e : Equiv.Perm V) : Equiv.Perm (Mode V) :=
  Equiv.prodCongr e (Equiv.refl (Fin 3))

/-- One oriented color-preserving neighbor matrix. -/
def directedAdjacency (e : Equiv.Perm V) : Matrix (Mode V) (Mode V) ℝ :=
  fun i j => if j = modePerm e i then 1 else 0

/-- Four-neighbor adjacency with explicit multiplicities. If a period equals
two, the two coincident directions are parallel bonds, not silently collapsed. -/
def graphAdjacency (ex ey : Equiv.Perm V) : Matrix (Mode V) (Mode V) ℝ :=
  directedAdjacency ex + (directedAdjacency ex).transpose +
    (directedAdjacency ey + (directedAdjacency ey).transpose)

omit [Fintype V] in
theorem graphAdjacency_transpose (ex ey : Equiv.Perm V) :
    (graphAdjacency ex ey).transpose = graphAdjacency ex ey := by
  simp only [graphAdjacency, Matrix.transpose_add, Matrix.transpose_transpose]
  abel

/-- Each color mode has row degree exactly four, including parallel-edge multiplicity. -/
theorem graphAdjacency_row_sum (ex ey : Equiv.Perm V) (i : Mode V) :
    ∑ j, graphAdjacency ex ey i j = 4 := by
  have h (e : Equiv.Perm V) :
      (∑ j, (directedAdjacency e).transpose i j) = 1 := by
    have hh : ∀ j, i = modePerm e j ↔ j = (modePerm e).symm i := by
      intro j
      constructor
      · intro he
        rw [he, Equiv.symm_apply_apply]
      · intro he
        rw [he, Equiv.apply_symm_apply]
    simp [directedAdjacency, Matrix.transpose_apply, hh]
  simp only [graphAdjacency, Matrix.add_apply, Finset.sum_add_distrib, h]
  simp [directedAdjacency]
  norm_num

/-- The single-count edge form of the actual finite reference. -/
def occupationEdgePairSum {M N : ℕ} (ex ey : Equiv.Perm V) : TotalCutoff.Op V M N :=
  (∑ v, ∑ α : Fin 3, occupationPair (v, α) (ex v, α)) +
    ∑ v, ∑ α : Fin 3, occupationPair (v, α) (ey v, α)

/-- The same graph reference, written with physical coupling g. -/
def edgeReference {M N : ℕ} (ex ey : Equiv.Perm V) (g : ℝ) : TotalCutoff.Op V M N :=
  (1-2*g) • TotalCutoff.number + (g/2) • occupationEdgePairSum ex ey

theorem directedAdjacency_pair_sum {M N : ℕ} (e : Equiv.Perm V) :
    (∑ i, ∑ j, directedAdjacency e i j •
      (occupationPair i j : TotalCutoff.Op V M N)) =
      ∑ v, ∑ α : Fin 3, occupationPair (v, α) (e v, α) := by
  simp [directedAdjacency, Fintype.sum_prod_type, modePerm]

theorem transpose_directedAdjacency_pair_sum {M N : ℕ} (e : Equiv.Perm V) :
    (∑ i, ∑ j, (directedAdjacency e).transpose i j •
      (occupationPair i j : TotalCutoff.Op V M N)) =
      ∑ v, ∑ α : Fin 3, occupationPair (v, α) (e v, α) := by
  rw [Finset.sum_comm]
  simp only [Matrix.transpose_apply]
  simp_rw [occupationPair_symm]
  exact directedAdjacency_pair_sum e

/-- The symmetric kernel is exactly Δ=(g/2)Adj; the half factor cancels the
opposite orientations, leaving coefficient g/2 on each listed physical edge. -/
theorem edgeReference_eq_coupledReference {M N : ℕ}
    (ex ey : Equiv.Perm V) (g : ℝ) :
    (edgeReference ex ey g : TotalCutoff.Op V M N) =
      coupledReference (1-2*g) ((g/2) • graphAdjacency ex ey) := by
  simp only [coupledReference, Matrix.smul_apply, smul_eq_mul, MulAction.mul_smul,
    ← Finset.smul_sum]
  simp only [graphAdjacency, Matrix.add_apply, add_smul, Finset.sum_add_distrib,
    directedAdjacency_pair_sum, transpose_directedAdjacency_pair_sum,
    smul_add, smul_smul, edgeReference, occupationEdgePairSum]
  module

/-- Compression of each actual finite pair uses the proved distinct-site
product identity, not an unjustified multiplication of compressed matrices. -/
theorem physical_compression_occupationPair {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (occupationPair (u, α) (v, β) : TotalCutoff.Op V M (Fintype.card V)) *
        TotalCutoff.physicalInclusion (V := V) hM =
      globalCreate u α * globalCreate v β +
        (globalCreate u α * globalCreate v β).transpose := by
  rw [occupationPair, Matrix.mul_add, Matrix.add_mul,
    TotalCutoff.physical_compression_create_pair hM u v huv α β]
  congr 1
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
    congrArg Matrix.transpose
      (TotalCutoff.physical_compression_create_pair hM u v huv α β)

/-- Sum over the three physical colors, each once. -/
theorem physical_compression_colorPair {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (∑ α : Fin 3, occupationPair (u, α) (v, α) :
          TotalCutoff.Op V M (Fintype.card V)) *
        TotalCutoff.physicalInclusion (V := V) hM = pair u v := by
  simp only [Matrix.mul_sum, Matrix.sum_mul,
    physical_compression_occupationPair hM u v huv, Finset.sum_add_distrib,
    pair, BilayerDressed.pairCreate, Matrix.transpose_sum]

/-- Exact matrix identity for the actual hard-core comparison. -/
theorem physical_compression_edgeReference {M : ℕ} (hM : 2 ≤ M)
    (ex ey : Equiv.Perm V) (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v) (g : ℝ) :
    (TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (edgeReference ex ey g : TotalCutoff.Op V M (Fintype.card V)) *
        TotalCutoff.physicalInclusion (V := V) hM = hardCoreReference ex ey g := by
  simp only [edgeReference, occupationEdgePairSum, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    TotalCutoff.physical_compression_number,
    physical_compression_occupationPair hM _ _ (hx _),
    physical_compression_occupationPair hM _ _ (hy _),
    hardCoreReference, edgePairSum, pair, BilayerDressed.pairCreate,
    Matrix.transpose_sum, Finset.sum_add_distrib, smul_add]

/-- The finite coupled quadratic form is proved below the actual Cartesian
Hamiltonian through the frozen physical isometry W. No operator bound is a premise. -/
theorem graphHamiltonian_coupled_compression_lower {M : ℕ} (hM : 2 ≤ M)
    (ex ey : Equiv.Perm V) (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : Configuration V → ℝ) :
    PhysicalGram.qform
      ((TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (coupledReference (1-2*g) ((g/2) • graphAdjacency ex ey) :
          TotalCutoff.Op V M (Fintype.card V)) *
        TotalCutoff.physicalInclusion (V := V) hM) x ≤
      PhysicalGram.qform (CartesianBasis.graphHamiltonian ex ey g) x := by
  rw [← edgeReference_eq_coupledReference,
    physical_compression_edgeReference hM ex ey hx hy]
  exact graphHamiltonian_lower ex ey hx hy g hg x


section Forms
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Rectangular compression is exactly evaluation of the ambient quadratic form. -/
theorem compression_quadratic (W : Matrix κ ι ℝ) (A : Matrix κ κ ℝ) (x : ι → ℝ) :
    dotProduct x ((W.transpose * A * W).mulVec x) =
      dotProduct (W.mulVec x) (A.mulVec (W.mulVec x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Real Euclidean inner products in the ambient finite basis are ordinary forms. -/
theorem euclidean_inner_matrix (A : Matrix κ κ ℝ) (x : EuclideanSpace ℝ κ) :
    ⟪x, A.toEuclideanLin x⟫ = dotProduct (WithLp.ofLp x) (A.mulVec (WithLp.ofLp x)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
  simp only [star_trivial, dotProduct_comm]
end Forms

/-- The actual coupled form evaluated on W x, rather than an abstract compression premise. -/
theorem graphHamiltonian_coupled_form_lower {M : ℕ} (hM : 2 ≤ M)
    (ex ey : Equiv.Perm V) (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : Configuration V → ℝ) :
    dotProduct ((TotalCutoff.physicalInclusion (V := V) hM).mulVec x)
      ((coupledReference (1-2*g) ((g/2) • graphAdjacency ex ey) :
        TotalCutoff.Op V M (Fintype.card V)).mulVec
          ((TotalCutoff.physicalInclusion (V := V) hM).mulVec x)) ≤
      PhysicalGram.qform (CartesianBasis.graphHamiltonian ex ey g) x := by
  have h := graphHamiltonian_coupled_compression_lower hM ex ey hx hy g hg x
  rw [PhysicalGram.qform, compression_quadratic] at h
  exact h

/-- For the actual magic-rung physical representative the embedding is W U,
where U is the frozen global Cartesian parity map, not a mode rotation. -/
def physicalEmbedding {M : ℕ} (hM : 2 ≤ M) :
    Matrix (TotalCutoff.Basis V M (Fintype.card V)) (Configuration V) ℝ :=
  TotalCutoff.physicalInclusion hM * CartesianBasis.U

/-- This physical embedding is an exact finite isometry. -/
theorem physicalEmbedding_transpose_mul {M : ℕ} (hM : 2 ≤ M) :
    (physicalEmbedding (V := V) hM).transpose * physicalEmbedding (V := V) hM = 1 := by
  simp only [physicalEmbedding, Matrix.transpose_mul, CartesianBasis.U_transpose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (TotalCutoff.physicalInclusion (V := V) hM).transpose,
    TotalCutoff.physicalInclusion_transpose_mul, Matrix.one_mul, CartesianBasis.U_mul_U]

/-- The actual physical form bound follows from the already proved global
Cartesian-to-magic conjugation; no local adapters are multiplied on overlapping edges. -/
theorem physical_graphHamiltonian_coupled_form_lower {M : ℕ} (hM : 2 ≤ M)
    (ex ey : Equiv.Perm V) (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : Configuration V → ℝ) :
    dotProduct ((physicalEmbedding (V := V) hM).mulVec x)
      ((coupledReference (1-2*g) ((g/2) • graphAdjacency ex ey) :
        TotalCutoff.Op V M (Fintype.card V)).mulVec
          ((physicalEmbedding (V := V) hM).mulVec x)) ≤
      PhysicalGram.qform (PhysicalGram.graphHamiltonian ex ey g) x := by
  have h := graphHamiltonian_coupled_form_lower hM ex ey hx hy g hg
    ((CartesianBasis.U : ConfigurationMatrix V).mulVec x)
  change _ ≤ dotProduct (CartesianBasis.U.mulVec x)
    ((CartesianBasis.graphHamiltonian ex ey g).mulVec (CartesianBasis.U.mulVec x)) at h
  rw [← compression_quadratic (CartesianBasis.U : ConfigurationMatrix V)
    (CartesianBasis.graphHamiltonian ex ey g) x, CartesianBasis.U_transpose,
    CartesianBasis.graphHamiltonian_conjugation ex ey hx hy] at h
  simpa only [physicalEmbedding, Matrix.mulVec_mulVec, PhysicalGram.qform] using h

/-- Euclidean Hilbert-space form of the actual physical comparison. -/
theorem physical_graphHamiltonian_coupled_inner_lower {M : ℕ} (hM : 2 ≤ M)
    (ex ey : Equiv.Perm V) (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v)
    (g : ℝ) (hg : 0 ≤ g) (x : EuclideanSpace ℝ (Configuration V)) :
    ⟪(physicalEmbedding (V := V) hM).toEuclideanLin x,
      (coupledReference (1-2*g) ((g/2) • graphAdjacency ex ey) :
        TotalCutoff.Op V M (Fintype.card V)).toEuclideanLin
          ((physicalEmbedding (V := V) hM).toEuclideanLin x)⟫ ≤
      ⟪x, (PhysicalGram.graphHamiltonian ex ey g).toEuclideanLin x⟫ := by
  simp only [euclidean_inner_matrix, Matrix.ofLp_toEuclideanLin_apply]
  exact physical_graphHamiltonian_coupled_form_lower hM ex ey hx hy g hg (WithLp.ofLp x)

/-- Ordinary even rectangular torus with both circumferences at least four.
The right-hand side is the actual frozen physical Hamiltonian. -/
theorem physical_fullHamiltonian_coupled_inner_lower {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (g : ℝ) (hg : 0 ≤ g)
    (x : EuclideanSpace ℝ (Torus.FullConfig (2*n) (2*m))) :
    ⟪(physicalEmbedding (V := Torus.FullVertex (2*n) (2*m)) hM).toEuclideanLin x,
      (coupledReference (1-2*g) ((g/2) • graphAdjacency (Torus.xNext n m) (Torus.yNext n m)) :
        TotalCutoff.Op (Torus.FullVertex (2*n) (2*m)) M
          (Fintype.card (Torus.FullVertex (2*n) (2*m)))).toEuclideanLin
            ((physicalEmbedding hM).toEuclideanLin x)⟫ ≤
      ⟪x, (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).toEuclideanLin x⟫ := by
  have h := physical_graphHamiltonian_coupled_inner_lower hM (Torus.xNext n m)
    (Torus.yNext n m) (fun v => (Torus.xNext_ne n m (by omega) v).symm)
    (fun v => (Torus.yNext_ne n m (by omega) v).symm) g hg x
  simpa only [PhysicalGram.graphHamiltonian, PhysicalGram.number, Torus.fullHamiltonian,
    Torus.fullXNext, Torus.fullYNext, Torus.xNext, Torus.yNext] using h

end BilayerDressed.CoupledQuadratic
