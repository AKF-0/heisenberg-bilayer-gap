import Mathlib

/-!
# Countable spatial moment interpolation

The index type may be arbitrary, so the results include finite and countable
spatial spectra. Summability of the smaller positive moment is an explicit
premise; summability of every larger moment and the interpolation inequalities
are proved, not assumed. No partition-function or transfer-operator identity is
asserted by this file.
-/

namespace BilayerGap

noncomputable section

/-- A nonnegative summable family has a summable real power for every exponent
at least one; its powered sum is at most the corresponding power of its sum. -/
theorem summable_rpow_and_tsum_le {ι : Type*} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : Summable x) {q : ℝ} (hq : 1 ≤ q) :
    Summable (fun i => (x i) ^ q) ∧
      (∑' i, (x i) ^ q) ≤ (∑' i, x i) ^ q := by
  let S : ℝ := ∑' i, x i
  have hS : 0 ≤ S := tsum_nonneg hx
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqsub : 0 ≤ q - 1 := sub_nonneg.mpr hq
  have hpoint : ∀ i, (x i) ^ q ≤ S ^ (q - 1) * x i := by
    intro i
    have hxi : x i ≤ S := hs.le_tsum i (fun j _ => hx j)
    calc
      (x i) ^ q = (x i) ^ (q - 1) * x i := by
        simpa only [sub_add_cancel] using
          (Real.rpow_add_one' (hx i) (y := q - 1) (by linarith))
      _ ≤ S ^ (q - 1) * x i :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hx i) hxi hqsub) (hx i)
  have hmajor : Summable (fun i => S ^ (q - 1) * x i) := hs.mul_left _
  have hp : Summable (fun i => (x i) ^ q) :=
    Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (hx i) q) hpoint hmajor
  refine ⟨hp, ?_⟩
  calc
    (∑' i, (x i) ^ q) ≤ ∑' i, S ^ (q - 1) * x i :=
      Summable.tsum_le_tsum hpoint hp hmajor
    _ = S ^ (q - 1) * S := by rw [tsum_mul_left]
    _ = S ^ q := by
      simpa only [sub_add_cancel] using
        (Real.rpow_add_one' hS (y := q - 1) (by linarith)).symm

/-- Moment monotonicity with arbitrary positive real exponents. -/
theorem moment_rpow_interpolation {ι : Type*} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hs : Summable (fun i => (x i) ^ p)) :
    Summable (fun i => (x i) ^ q) ∧
      (∑' i, (x i) ^ q) ≤ (∑' i, (x i) ^ p) ^ (q / p) := by
  have hratio : 1 ≤ q / p := (one_le_div hp).2 hpq
  have hid : ∀ i, ((x i) ^ p) ^ (q / p) = (x i) ^ q := by
    intro i
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  have h := summable_rpow_and_tsum_le
    (fun i => Real.rpow_nonneg (hx i) p) hs hratio
  simpa only [hid] using h

/-- The natural moment of a real spectrum, with absolute values as required
for nonnegative spatial moment representations. -/
def absMoment {ι : Type*} (lambda : ι → ℝ) (n : ℕ) : ℝ :=
  ∑' i, |lambda i| ^ n

/-- The precise upper interpolation inequality `Z(L) ≤ Z(n)^(L/n)`,
including the proof that the higher moment is summable. -/
theorem absMoment_upper {ι : Type*} {lambda : ι → ℝ} {n L : ℕ}
    (hn : 0 < n) (hnL : n ≤ L) (hs : Summable (fun i => |lambda i| ^ n)) :
    Summable (fun i => |lambda i| ^ L) ∧
      absMoment lambda L ≤ (absMoment lambda n) ^ ((L : ℝ) / n) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hpq : (n : ℝ) ≤ L := by exact_mod_cast hnL
  have h := moment_rpow_interpolation (fun i => abs_nonneg (lambda i)) hp hpq
    (by simpa only [Real.rpow_natCast] using hs)
  simpa only [Real.rpow_natCast, absMoment] using h

/-- Reverse interpolation from a larger endpoint: `Z(N)^(L/N) ≤ Z(L)`.
The smaller moment summability also proves endpoint summability. -/
theorem absMoment_lower {ι : Type*} {lambda : ι → ℝ} {L N : ℕ}
    (hL : 0 < L) (hLN : L ≤ N) (hs : Summable (fun i => |lambda i| ^ L)) :
    (absMoment lambda N) ^ ((L : ℝ) / N) ≤ absMoment lambda L := by
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmL : 0 ≤ absMoment lambda L := tsum_nonneg (fun i => pow_nonneg (abs_nonneg _) _)
  have hmN : 0 ≤ absMoment lambda N := tsum_nonneg (fun i => pow_nonneg (abs_nonneg _) _)
  have hupper := (absMoment_upper hL hLN hs).2
  have hpow := Real.rpow_le_rpow hmN hupper (div_nonneg hLr.le hNr.le)
  have hexp : ((N : ℝ) / L) * ((L : ℝ) / N) = 1 := by field_simp
  rw [← Real.rpow_mul hmL, hexp, Real.rpow_one] at hpow
  exact hpow

/-- Both endpoints of a spatial scale interval follow from one lower moment. -/
theorem absMoment_scale_box {ι : Type*} {lambda : ι → ℝ} {n L : ℕ}
    (hn : 0 < n) (hnL : n ≤ L) (hL2n : L ≤ 2 * n)
    (hs : Summable (fun i => |lambda i| ^ n)) :
    (absMoment lambda (2 * n)) ^ ((L : ℝ) / (2 * n)) ≤ absMoment lambda L ∧
      absMoment lambda L ≤ (absMoment lambda n) ^ ((L : ℝ) / n) := by
  have hupper := absMoment_upper hn hnL hs
  refine ⟨?_, hupper.2⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (absMoment_lower (lt_of_lt_of_le hn hnL) hL2n hupper.1)

#print axioms summable_rpow_and_tsum_le
#print axioms moment_rpow_interpolation
#print axioms absMoment_upper
#print axioms absMoment_lower
#print axioms absMoment_scale_box

end

end BilayerGap
