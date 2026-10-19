import Gap.TorusLifts

/-!
# The concrete nearest-neighbor torus Hamiltonian is a matching average

The Hamiltonian below is defined directly as the sum of one-rung terms minus
coupling times the sum of actual products of lifted local matrices along positive
horizontal and vertical torus edges. Its equality with the average of four
independent-cluster Hamiltonians at coupling `4*g` is a proved matrix identity.
-/
noncomputable section
namespace BilayerGap
namespace Torus
open ClusterProducts Matrix
open scoped Kronecker

variable {I : Type*} [Fintype I]

/-- The local real rung-coordinate pair operator, in the 16-state lexicographic basis. -/
def localPair (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) + (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ h -
      t • ∑ a, (G a) ⊗ₖ (G a))

/-- One actual independent-matching Hamiltonian in the global rung configuration basis. -/
def matchingBlock (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (c : Fin 4) :
    Matrix (Config n m) (Config n m) ℝ :=
  Matrix.reindex (matchingBasis n m c) (matchingBasis n m c)
    (independentHamiltonian (localPair h G t) (PairCount n m))

/-- Onsite energy plus the actual nearest-neighbor products, counting each positive
periodic horizontal and vertical edge once. For n,m≥2 this is the ordinary torus. -/
def hamiltonian (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) : Matrix (Config n m) (Config n m) ℝ :=
  (∑ v, siteLift h v) - g •
    ((∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (xNext n m v)) +
      (∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (yNext n m v)))

/-- Actual side lengths, used by the Gibbs family and transfer limits. -/
abbrev FullVertex (L M : ℕ) := Fin L × Fin M
abbrev FullConfig (L M : ℕ) := FullVertex L M → Fin 4

def fullXNext (L M : ℕ) : Equiv.Perm (FullVertex L M) :=
  Equiv.prodCongr (finRotate L) (Equiv.refl _)

def fullYNext (L M : ℕ) : Equiv.Perm (FullVertex L M) :=
  Equiv.prodCongr (Equiv.refl _) (finRotate M)

/-- The actual-length Hamiltonian, without division-by-two coordinate casts. -/
def fullHamiltonian (L M : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) :
    Matrix (FullConfig L M) (FullConfig L M) ℝ :=
  (∑ v, siteLift h v) - g •
    ((∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (fullXNext L M v)) +
      (∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (fullYNext L M v)))

/-- Each matching contains every onsite term once, and only its own disjoint bonds. -/
theorem matchingBlock_expansion (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (c : Fin 4) :
    matchingBlock n m h G t c =
      (∑ v, siteLift h v) - t •
        ∑ i, ∑ a, siteLift (G a) (matching n m c (i,0)) *
          siteLift (G a) (matching n m c (i,1)) := by
  unfold matchingBlock matchingBasis
  rw [reindex_independent_eq_pair_sum]
  have hlocal : Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm (localPair h G t) =
      h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) + (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ h -
      t • ∑ a, (G a) ⊗ₖ (G a) := by
    ext i j
    simp [localPair,Matrix.reindex_apply]
  rw [hlocal]
  have hterm (i : Fin (PairCount n m)) :
      pairLift (h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) + (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ h -
        t • ∑ a, (G a) ⊗ₖ (G a)) (matching n m c (i,0)) (matching n m c (i,1)) =
      (siteLift h (matching n m c (i,0)) + siteLift h (matching n m c (i,1))) -
        t • ∑ a, siteLift (G a) (matching n m c (i,0)) *
          siteLift (G a) (matching n m c (i,1)) := by
    rw [pairLift_sub,pairLift_add,pairLift_left h (matching_endpoints_ne n m c i),
      pairLift_right h (matching_endpoints_ne n m c i),pairLift_smul,pairLift_sum]
    simp_rw [← siteLift_mul_distinct _ _ (matching_endpoints_ne n m c i)]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, matching_site_sum]

/-- The four bond-color classes cover the two positive-neighbor edge families exactly. -/
theorem four_matching_edge_sum (n m : ℕ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ c : Fin 4, ∑ i, ∑ a, siteLift (G a) (matching n m c (i,0)) *
        siteLift (G a) (matching n m c (i,1))) =
      (∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (xNext n m v)) +
      (∑ v, ∑ a, siteLift (G a) v * siteLift (G a) (yNext n m v)) := by
  rw [← horizontal_edge_sum n m (fun u v => ∑ a, siteLift (G a) u * siteLift (G a) v),
    ← vertical_edge_sum n m (fun u v => ∑ a, siteLift (G a) u * siteLift (G a) v)]
  simp [Fin.sum_univ_succ,matching,add_assoc]

/-- Exact physical sum identity: four independent matchings at `4*g`, averaged,
are precisely the onsite-minus-nearest-neighbor Hamiltonian at coupling `g`. -/
theorem hamiltonian_eq_matching_average (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) :
    hamiltonian n m h G g = (1/4 : ℝ) • ∑ c : Fin 4, matchingBlock n m h G (4*g) c := by
  simp_rw [matchingBlock_expansion]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, four_matching_edge_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  ext s t
  simp only [hamiltonian, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sum_apply, smul_eq_mul]
  ring

/-- Matching decomposition in the actual side-length convention. -/
theorem fullHamiltonian_even_eq_matching_average (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) :
    fullHamiltonian (2*n) (2*m) h G g =
      (1/4 : ℝ) • ∑ c : Fin 4, matchingBlock n m h G (4*g) c :=
  hamiltonian_eq_matching_average n m h G g

/-- The actual two-rung product singlet diagonal vanishes from local h00=G00=0. -/
theorem localPair_vacuum_diagonal (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ)
    (hh : h 0 0 = 0) (hG : ∀ a, G a 0 0 = 0) : localPair h G t 0 0 = 0 := by
  change (h ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) + (1 : Matrix (Fin 4) (Fin 4) ℝ) ⊗ₖ h -
    t • ∑ a, (G a) ⊗ₖ (G a)) (0,0) (0,0) = 0
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.kronecker_apply,Matrix.one_apply,hh,hG,zero_mul,mul_zero,Finset.sum_const_zero,
    smul_zero,add_zero,sub_zero]

/-- A common product vacuum for every size and every matching, with zero energy expectation. -/
theorem hamiltonian_vacuum_diagonal (n m : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (hh : h 0 0 = 0) (hG : ∀ a, G a 0 0 = 0) :
    hamiltonian n m h G g (fun _ => 0) (fun _ => 0) = 0 := by
  rw [hamiltonian_eq_matching_average]
  simp only [Matrix.smul_apply,Matrix.sum_apply]
  have hd (c : Fin 4) : matchingBlock n m h G (4*g) c (fun _ => 0) (fun _ => 0) = 0 :=
    reindexed_vacuum_diagonal (matching n m c) (localPair h G (4*g))
      (localPair_vacuum_diagonal h G (4*g) hh hG)
  simp only [hd,Finset.sum_const_zero,smul_zero]

#print axioms matchingBlock_expansion
#print axioms hamiltonian_eq_matching_average
#print axioms hamiltonian_vacuum_diagonal

/-- The actual-length Hamiltonian is Hermitian for all side lengths, including
any degenerate edges: no even-size zero-extension is required for the Gibbs family. -/
theorem fullHamiltonian_hermitian (L M : ℕ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (G : I → Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (hh : h.IsHermitian) (hG : ∀ a, (G a).transpose = -G a) :
    (fullHamiltonian L M h G g).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  have hs (v : FullVertex L M) : siteLift h v t s = siteLift h v s t := by
    simpa only [star_trivial] using (siteLift_hermitian h hh v).apply s t
  have hp (a : I) (u v : FullVertex L M) :
      (siteLift (G a) u * siteLift (G a) v) t s =
        (siteLift (G a) u * siteLift (G a) v) s t := by
    simpa only [star_trivial] using
      (siteLift_antisymmetric_product_hermitian (G a) (hG a) u v).apply s t
  simp only [fullHamiltonian, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sum_apply, star_trivial]
  simp_rw [hs,hp]

#print axioms fullHamiltonian_hermitian

end Torus
end BilayerGap
