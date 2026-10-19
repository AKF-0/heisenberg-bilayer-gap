import Gap.Moments

/-!
# Spatial interpolation from countable moment representations

The two spectra are separate and may depend on the transverse size. Only their
absolute fourth moments are assumed summable. Moment equalities are required
only at even sizes at least four. The rectangular partition-function inequalities
are proved from this data rather than entered as hypotheses.
-/

namespace BilayerGap

noncomputable section

/-- The spatial sizes appearing in the torus theorem. -/
def ValidSize (n : ℕ) : Prop := 4 ≤ n ∧ Even n

/-- Actual, separate countable moment representations in the two directions. -/
structure SpatialMomentData (Z : ℕ → ℕ → ℝ) where
  xSpectrum : ℕ → ℕ → ℝ
  ySpectrum : ℕ → ℕ → ℝ
  x_summable : ∀ M, ValidSize M → Summable (fun i => |xSpectrum M i| ^ 4)
  y_summable : ∀ L, ValidSize L → Summable (fun i => |ySpectrum L i| ^ 4)
  x_moment : ∀ L M, ValidSize L → ValidSize M → Z L M = absMoment (xSpectrum M) L
  y_moment : ∀ L M, ValidSize L → ValidSize M → Z L M = absMoment (ySpectrum L) M

theorem ValidSize.pos {n : ℕ} (hn : ValidSize n) : 0 < n := by
  exact lt_of_lt_of_le (by norm_num) hn.1

theorem ValidSize.double {n : ℕ} (hn : ValidSize n) : ValidSize (2 * n) := by
  have hfour := hn.1
  refine ⟨by omega, ?_⟩
  exact even_two_mul n

theorem SpatialMomentData.nonneg {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {L M : ℕ} (hL : ValidSize L) (hM : ValidSize M) : 0 ≤ Z L M := by
  rw [D.x_moment L M hL hM]
  exact tsum_nonneg (fun i => pow_nonneg (abs_nonneg _) _)

/-- One-coordinate upper interpolation, including derivation of summability
from the supplied fourth moment. -/
theorem SpatialMomentData.x_upper {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {n L M : ℕ} (hn : ValidSize n) (hL : ValidSize L) (hM : ValidSize M)
    (hnL : n ≤ L) : Z L M ≤ (Z n M) ^ ((L : ℝ) / n) := by
  rw [D.x_moment L M hL hM, D.x_moment n M hn hM]
  have hs := (absMoment_upper (by norm_num : 0 < 4) hn.1 (D.x_summable M hM)).1
  exact (absMoment_upper hn.pos hnL hs).2

theorem SpatialMomentData.y_upper {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {L m M : ℕ} (hL : ValidSize L) (hm : ValidSize m) (hM : ValidSize M)
    (hmM : m ≤ M) : Z L M ≤ (Z L m) ^ ((M : ℝ) / m) := by
  rw [D.y_moment L M hL hM, D.y_moment L m hL hm]
  have hs := (absMoment_upper (by norm_num : 0 < 4) hm.1 (D.y_summable L hL)).1
  exact (absMoment_upper hm.pos hmM hs).2

theorem SpatialMomentData.x_lower {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {L N M : ℕ} (hL : ValidSize L) (hN : ValidSize N) (hM : ValidSize M)
    (hLN : L ≤ N) : (Z N M) ^ ((L : ℝ) / N) ≤ Z L M := by
  rw [D.x_moment L M hL hM, D.x_moment N M hN hM]
  have hs := (absMoment_upper (by norm_num : 0 < 4) hL.1 (D.x_summable M hM)).1
  exact absMoment_lower hL.pos hLN hs

theorem SpatialMomentData.y_lower {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {L M N : ℕ} (hL : ValidSize L) (hM : ValidSize M) (hN : ValidSize N)
    (hMN : M ≤ N) : (Z L N) ^ ((M : ℝ) / N) ≤ Z L M := by
  rw [D.y_moment L M hL hM, D.y_moment L N hL hN]
  have hs := (absMoment_upper (by norm_num : 0 < 4) hM.1 (D.y_summable L hL)).1
  exact absMoment_lower hM.pos hMN hs

/-- The two-dimensional upper partition-function bound obtained by applying
one-coordinate countable moment interpolation twice. -/
theorem SpatialMomentData.rectangle_upper {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {n m L M : ℕ} (hn : ValidSize n) (hm : ValidSize m)
    (hL : ValidSize L) (hM : ValidSize M) (hnL : n ≤ L) (hmM : m ≤ M) :
    Z L M ≤ (Z n m) ^ (((L : ℝ) * M) / ((n : ℝ) * m)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  calc
    Z L M ≤ (Z n M) ^ ((L : ℝ) / n) := D.x_upper hn hL hM hnL
    _ ≤ ((Z n m) ^ ((M : ℝ) / m)) ^ ((L : ℝ) / n) :=
      Real.rpow_le_rpow (D.nonneg hn hM) (D.y_upper hn hm hM hmM) (by positivity)
    _ = (Z n m) ^ (((L : ℝ) * M) / ((n : ℝ) * m)) := by
      rw [← Real.rpow_mul (D.nonneg hn hm)]
      congr 1
      field_simp

/-- The matching lower endpoint bound, likewise from two actual moment steps. -/
theorem SpatialMomentData.rectangle_lower {Z : ℕ → ℕ → ℝ} (D : SpatialMomentData Z)
    {L M N Q : ℕ} (hL : ValidSize L) (hM : ValidSize M)
    (hN : ValidSize N) (hQ : ValidSize Q) (hLN : L ≤ N) (hMQ : M ≤ Q) :
    (Z N Q) ^ (((L : ℝ) * M) / ((N : ℝ) * Q)) ≤ Z L M := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.pos
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  calc
    (Z N Q) ^ (((L : ℝ) * M) / ((N : ℝ) * Q)) =
        ((Z N Q) ^ ((M : ℝ) / Q)) ^ ((L : ℝ) / N) := by
      rw [← Real.rpow_mul (D.nonneg hN hQ)]
      congr 1
      field_simp
    _ ≤ (Z N M) ^ ((L : ℝ) / N) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (D.nonneg hN hQ) _)
        (D.y_lower hN hM hQ hMQ) (by positivity)
    _ ≤ Z L M := D.x_lower hL hN hM hLN

/-- A scalar quotient bridge, with no interpolation hypothesis hidden in it. -/
theorem interpolation_ratio_bound {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d)
    (hupper : c ≤ a ^ (4 * e)) (hlower : b ^ e ≤ d) :
    (b / a ^ 8) ^ e ≤ d / c ^ 2 := by
  have hden : c ^ 2 ≤ (a ^ (4 * e)) ^ 2 := pow_le_pow_left₀ hc.le hupper 2
  have heq : (a ^ 8) ^ e = (a ^ (4 * e)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
      ← Real.rpow_mul ha.le]
    congr 1
    norm_num
    ring
  rw [Real.div_rpow hb (pow_nonneg ha.le _), heq]
  exact div_le_div₀ hd hlower (sq_pos_of_pos hc) hden

/-- The staircase product cancels to the exact endpoint quotient. -/
theorem staircase_partition_product {a x y z : ℝ} (ha : a ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / a ^ 2) ^ 4 * (y / x ^ 2) ^ 2 * (z / y ^ 2) = z / a ^ 8 := by
  field_simp

/-- Equation (5.1): the full thermal purity lower bound in a rectangular
scale box. `Z` is the partition function at beta and `W` at twice beta.
Both supplied moment representations are used to prove the two Z bounds. -/
theorem spatial_purity_interpolation {Z W : ℕ → ℕ → ℝ}
    (DZ : SpatialMomentData Z) (DW : SpatialMomentData W)
    (hZpos : ∀ L M, ValidSize L → ValidSize M → 0 < Z L M)
    {n m L M : ℕ} (hn : ValidSize n) (hm : ValidSize m)
    (hL : ValidSize L) (hM : ValidSize M)
    (hnL : n ≤ L) (hL2n : L ≤ 2 * n) (hmM : m ≤ M) (hM2m : M ≤ 2 * m) :
    ((Z (2 * n) m / (Z n m) ^ 2) ^ 4 *
      (Z (2 * n) (2 * m) / (Z (2 * n) m) ^ 2) ^ 2 *
      (W (2 * n) (2 * m) / (Z (2 * n) (2 * m)) ^ 2)) ^
        (((L : ℝ) * M) / (4 * (n : ℝ) * m)) ≤ W L M / (Z L M) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  rw [staircase_partition_product (hZpos n m hn hm).ne'
    (hZpos (2 * n) m hn.double hm).ne' (hZpos (2 * n) (2 * m) hn.double hm.double).ne']
  apply interpolation_ratio_bound (hZpos n m hn hm)
    (DW.nonneg hn.double hm.double) (hZpos L M hL hM) (DW.nonneg hL hM)
  · have hexp : 4 * (((L : ℝ) * M) / (4 * (n : ℝ) * m)) =
        ((L : ℝ) * M) / ((n : ℝ) * m) := by field_simp
    rw [hexp]
    exact DZ.rectangle_upper hn hm hL hM hnL hmM
  · have hdenEq : (2 * (n : ℝ)) * (2 * (m : ℝ)) = 4 * (n : ℝ) * m := by ring
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hdenEq] using
      (DW.rectangle_lower hL hM hn.double hm.double hL2n hM2m)

#print axioms SpatialMomentData.rectangle_upper
#print axioms SpatialMomentData.rectangle_lower
#print axioms spatial_purity_interpolation

end

end BilayerGap
