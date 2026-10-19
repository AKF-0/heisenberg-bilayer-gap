import Gap.SpectralFamily
import Gap.Assembly

/-!
# Conditional finite-seed criterion on every valid square

The hypotheses are an actual finite Gibbs energy family, two countable spatial
moment representations at every positive inverse temperature, and three finite
seed inequalities. No gap, propagated-purity or interpolation conclusion is a
hypothesis. The concrete bilayer transfer representation and model seed must
still be supplied to instantiate this criterion.
-/
noncomputable section
namespace BilayerGap

theorem scaledVolume_eq (v : Volume) (j : ℕ) :
    scaledVolume v j = ⟨v.x*2^j, v.y*2^j, v.beta*(2^j:ℕ)⟩ := by
  induction j with
  | zero => simp [scaledVolume]
  | succ j ih =>
    rw [scaledVolume, ih]
    simp only [diagonalStep, doubleCoord, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    congr 1 <;> ring

/-- At every dyadic scale, all sizes in the spatial box have the physical Gibbs
purity required for the finite-spectrum gap extraction. -/
theorem SpectralFamily.scaled_box_purity (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b → SpatialMomentData (fun L M => F.partition ⟨L,M,b⟩))
    (v : Volume) (hv : ValidVolume v) (K r : ℝ)
    (hK : 0<K) (hr0 : 0<r) (hr1 : r<1) (hu0 : r/K<1) (hG : G7 (r/K) ≤ K)
    (hseed : 1-staircaseA F.partition v ≤ r/K ∧
      1-staircaseB F.partition v ≤ r/K ∧ 1-staircaseC F.partition v ≤ r/K)
    (j L M : ℕ) (hL : ValidSize L) (hM : ValidSize M)
    (hxlo : (scaledVolume v j).x ≤ L) (hxhi : L ≤ 2*(scaledVolume v j).x)
    (hylo : (scaledVolume v j).y ≤ M) (hyhi : M ≤ 2*(scaledVolume v j).y) :
    1-7*dyadicBound K r j ≤
      finitePurity (gibbsWeight (F.energy L M) (v.beta*(2^j:ℕ))) := by
  let D := F.purityDomain moments
  let w := scaledVolume v j
  have hw : ValidVolume w := scaledVolume_valid D v hv j
  obtain ⟨ha,hb,hc⟩ := coordinate_staircase_bootstrap D v hv K r hK hr0 hr1 hu0 hG hseed j
  have hu1 : dyadicBound K r j < 1 :=
    lt_of_le_of_lt (dyadicBound_le_initial hK hr0 hr1 j) hu0
  have hθ : ((L:ℝ)*M)/(4*(w.x:ℝ)*w.y) ≤ 1 := by
    have hx : (0:ℝ)<w.x := by exact_mod_cast hw.1.pos
    have hy : (0:ℝ)<w.y := by exact_mod_cast hw.2.1.pos
    apply (div_le_one (by positivity)).2
    have hLhi : (L:ℝ) ≤ 2*(w.x:ℝ) := by exact_mod_cast hxhi
    have hMhi : (M:ℝ) ≤ 2*(w.y:ℝ) := by exact_mod_cast hyhi
    calc
      (L:ℝ)*M ≤ (2*(w.x:ℝ))*(2*(w.y:ℝ)) := mul_le_mul hLhi hMhi (by positivity) (by positivity)
      _ = 4*(w.x:ℝ)*w.y := by ring
  have hinterp := F.rectangle_purity moments w hw hL hM hxlo hxhi hylo hyhi
  have h := purity_lower_from_interpolation
    (staircaseA F.partition w) (staircaseB F.partition w) (staircaseC F.partition w)
    (dyadicBound K r j) (((L:ℝ)*M)/(4*(w.x:ℝ)*w.y))
    (partitionRatio F.partition .time ⟨L,M,w.beta⟩)
    (dyadicBound_pos hK hr0 j).le hu1 (by linarith) (by linarith) (by linarith)
    (D.upper .x w hw) (D.upper .y _ (D.closed .x w hw))
    (D.upper .time _ (D.closed .y _ (D.closed .x w hw))) hθ hinterp
  rw [F.time_ratio] at h
  simpa only [w, scaledVolume_eq] using h

/-- The core finite-seed theorem: a size-independent strict gap for every even
square above the seed size. The two spatial moment representations are explicit
premises, not an opaque assumed purity inequality. -/
theorem SpectralFamily.square_gap_of_finite_seed (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b → SpatialMomentData (fun L M => F.partition ⟨L,M,b⟩))
    (n : ℕ) (b K r : ℝ) (hn : ValidSize n) (hb : 0<b)
    (hK : 0<K) (hr0 : 0<r) (hr1 : r<1) (hu0 : r/K<1) (hG : G7 (r/K) ≤ K)
    (hsmall : 7*(r/K)<1) (hmargin : 7<K*(1-7*(r/K)))
    (hseed : 1-staircaseA F.partition ⟨n,n,b⟩ ≤ r/K ∧
      1-staircaseB F.partition ⟨n,n,b⟩ ≤ r/K ∧
      1-staircaseC F.partition ⟨n,n,b⟩ ≤ r/K)
    (L : ℕ) (hL : ValidSize L) (hnL : n≤L)
    (i₀ k : Fin (F.dim L L : ℕ)) (hk : i₀≠k)
    (hground : ∀ i, F.energy L L i₀ ≤ F.energy L L i) :
    Real.log (1/r)/b < F.energy L L k-F.energy L L i₀ := by
  obtain ⟨j,hlo,hhi⟩ := exists_dyadic_size_box n L hn.pos hnL
  apply finite_gibbs_gap_of_scaled_purity (F.energy L L) i₀ k j b K r
    hb hK hr0 hr1 hsmall hmargin hk hground
  apply F.scaled_box_purity moments ⟨n,n,b⟩ ⟨hn,hn,hb⟩ K r
    hK hr0 hr1 hu0 hG hseed j L L hL hL
  · simpa only [scaledVolume_eq] using hlo
  · simpa only [scaledVolume_eq] using hhi.le
  · simpa only [scaledVolume_eq] using hlo
  · simpa only [scaledVolume_eq] using hhi.le

/-- Convenient exact constants used by both analytic seed constructions. -/
theorem SpectralFamily.square_gap_one_percent (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b → SpatialMomentData (fun L M => F.partition ⟨L,M,b⟩))
    (n : ℕ) (b : ℝ) (hn : ValidSize n) (hb : 0<b)
    (hseed : 1-staircaseA F.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseB F.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseC F.partition ⟨n,n,b⟩ ≤ 1/100)
    (L : ℕ) (hL : ValidSize L) (hnL : n≤L)
    (i₀ k : Fin (F.dim L L : ℕ)) (hk : i₀≠k)
    (hground : ∀ i, F.energy L L i₀ ≤ F.energy L L i) :
    Real.log (100/27)/b < F.energy L L k-F.energy L L i₀ := by
  have hrat : (27/100:ℝ)/27 = 1/100 := by norm_num
  have hG : G7 ((27/100:ℝ)/27) ≤ 27 := by
    simpa only [hrat] using G7_one_percent_lt.le
  have h := F.square_gap_of_finite_seed moments n b 27 (27/100) hn hb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hG
    (by norm_num) (by norm_num) (by simpa only [hrat] using hseed) L hL hnL i₀ k hk hground
  norm_num at h ⊢
  exact h

/-- The criterion also proves existence and uniqueness of the ground eigenvector,
not merely a conditional bound assuming a nondegenerate ground state. -/
theorem SpectralFamily.unique_ground_of_one_percent (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b → SpatialMomentData (fun L M => F.partition ⟨L,M,b⟩))
    (n : ℕ) (b : ℝ) (hn : ValidSize n) (hb : 0<b)
    (hseed : 1-staircaseA F.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseB F.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseC F.partition ⟨n,n,b⟩ ≤ 1/100)
    (L : ℕ) (hL : ValidSize L) (hnL : n≤L) :
    ∃! i₀ : Fin (F.dim L L : ℕ), ∀ i, F.energy L L i₀ ≤ F.energy L L i := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ (F.energy L L) Finset.univ_nonempty
  have hground : ∀ i, F.energy L L i₀ ≤ F.energy L L i := by simpa using hi₀
  refine ⟨i₀,hground,?_⟩
  intro k hk
  by_contra hne
  have hgap := F.square_gap_one_percent moments n b hn hb hseed L hL hnL
    i₀ k (Ne.symm hne) hground
  have hpositive : 0 < Real.log (100/27)/b :=
    div_pos (Real.log_pos (by norm_num)) hb
  have hle := hk i₀
  linarith

#print axioms scaledVolume_eq
#print axioms SpectralFamily.scaled_box_purity
#print axioms SpectralFamily.square_gap_of_finite_seed
#print axioms SpectralFamily.square_gap_one_percent
#print axioms SpectralFamily.unique_ground_of_one_percent
end BilayerGap
