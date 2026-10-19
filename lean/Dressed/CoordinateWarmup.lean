import Gap.LimitCriterion
import Dressed.ScalarWarmupCertificate

/-! Six ordered, unequal-error warmups for the actual coordinate partition
ratios. Only the three initial seed bounds remain explicit. Every update is
in the pinned coordinate order A, then B using new A, then C using new A/B. -/
noncomputable section
namespace BilayerDressed.CoordinateWarmup
open BilayerGap
set_option maxHeartbeats 3000000

/-- The rational triple bounds the three actual staircase defects. -/
def Bounds (Z : Volume → ℝ) (v : Volume) (a b c : ℚ) : Prop :=
  1-staircaseA Z v ≤ (a:ℝ) ∧ 1-staircaseB Z v ≤ (b:ℝ) ∧
    1-staircaseC Z v ≤ (c:ℝ)

theorem update_mono_cast {x y z : ℝ} {a b c : ℚ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : x ≤ (a:ℝ)) (hb : y ≤ (b:ℝ)) (hc : z ≤ (c:ℝ))
    (ha1 : a < 1) (hb1 : b < 1) (hc1 : c < 1) :
    purityStep (stairDefect x y z) ≤ (ScalarWarmup.update a b c : ℝ) := by
  have haR : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hbR : (b:ℝ) < 1 := by exact_mod_cast hb1
  have hcR : (c:ℝ) < 1 := by exact_mod_cast hc1
  have hu := stairDefect_bounds hx (ha.trans_lt haR) hy (hb.trans_lt hbR) hz (hc.trans_lt hcR)
  have hv := stairDefect_bounds (hx.trans ha) haR (hy.trans hb) hbR (hz.trans hc) hcR
  have hm : stairDefect x y z ≤ stairDefect (a:ℝ) (b:ℝ) (c:ℝ) := by
    unfold stairDefect
    gcongr <;> linarith
  have hh := purityStep_mono hu.1 hm hv.2
  convert hh using 1; simp [ScalarWarmup.update,purityStep,stairDefect]

/-- One complete genuine coordinate update, with separately certified upper errors. -/
theorem step {Z : Volume → ℝ} {D : Volume → Prop} (hd : PurityDomain Z D)
    (v : Volume) (hv : D v) {a b c a' b' c' : ℚ}
    (ha1 : a < 1) (hb1 : b < 1) (hc1 : c < 1)
    (ha1' : a' < 1) (hb1' : b' < 1)
    (hsA : ScalarWarmup.update a b c ≤ a')
    (hsB : ScalarWarmup.update b c a' ≤ b')
    (hsC : ScalarWarmup.update c a' b' ≤ c')
    (h : Bounds Z v a b c) : Bounds Z (diagonalStep v) a' b' c' := by
  have hh := coordinate_staircase_update hd v hv
  have hv' : D (diagonalStep v) := hd.closed .x _ (hd.closed .y _ (hd.closed .time _ hv))
  have hA : 0 ≤ 1-staircaseA Z v := sub_nonneg.mpr (hd.upper .x v hv)
  have hB : 0 ≤ 1-staircaseB Z v := sub_nonneg.mpr (hd.upper .y _ (hd.closed .x _ hv))
  have hC : 0 ≤ 1-staircaseC Z v := sub_nonneg.mpr (hd.upper .time _ (hd.closed .y _ (hd.closed .x _ hv)))
  have hA' : 0 ≤ 1-staircaseA Z (diagonalStep v) := sub_nonneg.mpr (hd.upper .x _ hv')
  have hB' : 0 ≤ 1-staircaseB Z (diagonalStep v) := sub_nonneg.mpr (hd.upper .y _ (hd.closed .x _ hv'))
  have ha : 1-staircaseA Z (diagonalStep v) ≤ (a':ℝ) :=
    (hh.1.trans (update_mono_cast hA hB hC h.1 h.2.1 h.2.2 ha1 hb1 hc1)).trans
      (by exact_mod_cast hsA)
  have hb : 1-staircaseB Z (diagonalStep v) ≤ (b':ℝ) :=
    (hh.2.1.trans (update_mono_cast hB hC hA' h.2.1 h.2.2 ha hb1 hc1 ha1')).trans
      (by exact_mod_cast hsB)
  have hc : 1-staircaseC Z (diagonalStep v) ≤ (c':ℝ) :=
    (hh.2.2.trans (update_mono_cast hC hA' hB' h.2.2 ha hb hc1 ha1' hb1')).trans
      (by exact_mod_cast hsC)
  exact ⟨ha,hb,hc⟩

/-- Six verified unequal-error warmups applied to the actual partition function. -/
theorem six_steps {Z : Volume → ℝ} {D : Volume → Prop} (hd : PurityDomain Z D)
    (v : Volume) (hv : D v)
    (h : Bounds Z v ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0) :
    Bounds Z (scaledVolume v 6) ScalarWarmup.a6 ScalarWarmup.b6 ScalarWarmup.c6 := by
  have hvalid := scaledVolume_valid hd v hv
  have h1 := step hd v hv ScalarWarmup.bounds0.2.1 ScalarWarmup.bounds0.2.2.2.1
    ScalarWarmup.bounds0.2.2.2.2.2 ScalarWarmup.bounds1.2.1 ScalarWarmup.bounds1.2.2.2.1
    ScalarWarmup.step1_a.le ScalarWarmup.step1_b.le ScalarWarmup.step1_c.le h
  have h2 := step hd _ (hvalid 1) ScalarWarmup.bounds1.2.1 ScalarWarmup.bounds1.2.2.2.1
    ScalarWarmup.bounds1.2.2.2.2.2 ScalarWarmup.bounds2.2.1 ScalarWarmup.bounds2.2.2.2.1
    ScalarWarmup.step2_a.le ScalarWarmup.step2_b.le ScalarWarmup.step2_c.le h1
  have h3 := step hd _ (hvalid 2) ScalarWarmup.bounds2.2.1 ScalarWarmup.bounds2.2.2.2.1
    ScalarWarmup.bounds2.2.2.2.2.2 ScalarWarmup.bounds3.2.1 ScalarWarmup.bounds3.2.2.2.1
    ScalarWarmup.step3_a.le ScalarWarmup.step3_b.le ScalarWarmup.step3_c.le h2
  have h4 := step hd _ (hvalid 3) ScalarWarmup.bounds3.2.1 ScalarWarmup.bounds3.2.2.2.1
    ScalarWarmup.bounds3.2.2.2.2.2 ScalarWarmup.bounds4.2.1 ScalarWarmup.bounds4.2.2.2.1
    ScalarWarmup.step4_a.le ScalarWarmup.step4_b.le ScalarWarmup.step4_c.le h3
  have h5 := step hd _ (hvalid 4) ScalarWarmup.bounds4.2.1 ScalarWarmup.bounds4.2.2.2.1
    ScalarWarmup.bounds4.2.2.2.2.2 ScalarWarmup.bounds5.2.1 ScalarWarmup.bounds5.2.2.2.1
    ScalarWarmup.step5_a.le ScalarWarmup.step5_b.le ScalarWarmup.step5_c.le h4
  exact step hd _ (hvalid 5) ScalarWarmup.bounds5.2.1 ScalarWarmup.bounds5.2.2.2.1
    ScalarWarmup.bounds5.2.2.2.2.2 ScalarWarmup.bounds6.2.1 ScalarWarmup.bounds6.2.2.2.1
    ScalarWarmup.step6_a.le ScalarWarmup.step6_b.le ScalarWarmup.step6_c.le h5

/-- Actual terminal coordinate and common error, not merely a numeric recurrence. -/
theorem seed_256_1024 {Z : Volume → ℝ} {D : Volume → Prop} (hd : PurityDomain Z D)
    (hv : D ⟨4,4,16⟩)
    (h : Bounds Z ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0) :
    1-staircaseA Z ⟨256,256,1024⟩ ≤ 1/400 ∧
    1-staircaseB Z ⟨256,256,1024⟩ ≤ 1/400 ∧
    1-staircaseC Z ⟨256,256,1024⟩ ≤ 1/400 := by
  have hh := six_steps hd ⟨4,4,16⟩ hv h
  have he : scaledVolume ⟨4,4,16⟩ 6 = (⟨256,256,1024⟩ : Volume) := by
    norm_num [scaledVolume,diagonalStep,doubleCoord]
  rw [he] at hh
  exact ⟨hh.1.trans (by norm_num [ScalarWarmup.a6]),
    hh.2.1.trans (by norm_num [ScalarWarmup.b6]),
    hh.2.2.trans (by norm_num [ScalarWarmup.c6])⟩


/-- Exact real common-error constant consumed by the pinned generic criterion. -/
theorem common_G7_bound : G7 (1/400) ≤ 26 := by
  norm_num [G7,Finset.sum_range_succ]

/-- The six genuine coordinate updates feed the generic all-size criterion.
The moment limits and initial three seed bounds are the only analytic inputs. -/
theorem square_gap_of_initial_bounds (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b →
      FiniteSpatialMomentLimits (fun L M => F.partition ⟨L,M,b⟩))
    (hseed : Bounds F.partition ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L)
    (i k : Fin (F.dim L L : ℕ)) (hik : i ≠ k)
    (hground : ∀ j, F.energy L L i ≤ F.energy L L j) :
    Real.log (200/13)/1024 < F.energy L L k-F.energy L L i := by
  have hs := seed_256_1024 (F.limitPurityDomain moments)
    (show ValidVolume ⟨4,4,16⟩ from ⟨⟨by norm_num,by decide⟩,⟨by norm_num,by decide⟩,by norm_num⟩)
    hseed
  have hh := F.square_gap_of_limit_seed moments 256 1024 26 (13/200)
    ⟨by norm_num,by decide⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; exact common_G7_bound)
    (by norm_num) (by norm_num)
    (by simpa only [show (13/200:ℝ)/26=1/400 by norm_num] using hs) L hL hlarge i k hik hground
  norm_num at hh ⊢
  exact hh

/-- Ground simplicity follows from the same actual seed inputs; it is not a premise. -/
theorem unique_ground_of_initial_bounds (F : SpectralFamily)
    (moments : ∀ b : ℝ, 0 < b →
      FiniteSpatialMomentLimits (fun L M => F.partition ⟨L,M,b⟩))
    (hseed : Bounds F.partition ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L) :
    ∃! i : Fin (F.dim L L : ℕ), ∀ j, F.energy L L i ≤ F.energy L L j := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (F.energy L L) Finset.univ_nonempty
  have hground : ∀ j,F.energy L L i ≤ F.energy L L j := by simpa using hi
  refine ⟨i,hground,?_⟩
  intro k hk
  by_contra hne
  have hgap := square_gap_of_initial_bounds F moments hseed L hL hlarge i k (Ne.symm hne) hground
  have hp : 0 < Real.log (200/13)/1024 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have he := hk i
  linarith

end BilayerDressed.CoordinateWarmup
