import Gap.Bootstrap
import Gap.Thermal
import Gap.Coordinates
import Gap.Seeds

/-!
# Verified interfaces joining the scalar and finite Gibbs layers

These are conditional theorems. The spatial-moment interpolation inequality and
the model's initial seed are not synthesized from the bilayer Hamiltonian here.
-/
noncomputable section
namespace BilayerGap

/-- Exact real endpoint needed by the scalar bootstrap; not an approximate float. -/
theorem G7_one_percent_lt : G7 ((1:ℝ)/100) < 27 := by
  norm_num [G7, Finset.sum_range_succ]

/-- Dyadic size boxes cover every integer size above the seed. Evenness is not
needed for the covering itself, only for the spatial moment application. -/
theorem exists_dyadic_size_box (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    ∃ j : ℕ, n*2^j ≤ L ∧ L < 2*(n*2^j) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hLR : (n:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  have hdiv : (1:ℝ) ≤ (L:ℝ)/(n:ℝ) := (le_div_iff₀ hnR).2 (by simpa)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hdiv (show (1:ℝ)<2 by norm_num)
  refine ⟨j, ?_, ?_⟩
  · have hh : (n:ℝ)*(2:ℝ)^j ≤ (L:ℝ) := by
      have := (le_div_iff₀ hnR).1 hjlo
      nlinarith
    exact_mod_cast hh
  · have hh : (L:ℝ) < 2*((n:ℝ)*(2:ℝ)^j) := by
      have := (div_lt_iff₀ hnR).1 hjhi
      rw [pow_succ] at this
      nlinarith
    exact_mod_cast hh

/-- The scalar final step in spatial interpolation, with the genuine
partition/moment interpolation estimate kept as a visible hypothesis. -/
theorem purity_lower_from_interpolation (a b c u θ T : ℝ)
    (_hu0 : 0 ≤ u) (hu1 : u < 1)
    (ha : 1-u ≤ a) (hb : 1-u ≤ b) (hc : 1-u ≤ c)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hθ : θ ≤ 1)
    (hinterp : (a^4*b^2*c)^θ ≤ T) :
    1-7*u ≤ T := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hpos : 0 < a^4*b^2*c := by positivity
  have hupper : a^4*b^2*c ≤ 1 := by
    calc
      a^4*b^2*c ≤ (1:ℝ)^4*1^2*1 := by gcongr
      _ = 1 := by norm_num
  have hprod : (1-u)^7 ≤ a^4*b^2*c := by
    calc
      (1-u)^7 = (1-u)^4*(1-u)^2*(1-u) := by ring
      _ ≤ a^4*b^2*c := by gcongr <;> linarith
  exact (seven_factor_lower hu1.le).trans
    (hprod.trans ((Real.self_le_rpow_of_le_one hpos.le hupper hθ).trans hinterp))

/-- The precise finite-spectrum gap consequence, once the spatial argument has
provided the physical Gibbs purity at the synchronized scale. -/
theorem finite_gibbs_gap_of_scaled_purity {ι : Type*} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] (E : ι → ℝ) (i₀ k : ι) (j : ℕ)
    (b K r : ℝ) (hb : 0 < b) (hK : 0 < K) (hr0 : 0 < r) (hr1 : r < 1)
    (hsmall : 7*(r/K) < 1) (hmargin : 7 < K*(1-7*(r/K)))
    (hk : i₀ ≠ k) (hground : ∀ i, E i₀ ≤ E i)
    (hpurity : 1-7*dyadicBound K r j ≤
      finitePurity (gibbsWeight E (b*(2^j:ℕ)))) :
    Real.log (1/r)/b < E k-E i₀ := by
  have hN : 0 < (2^j:ℕ) := pow_pos (by norm_num) _
  have hNR : 0 < ((2^j:ℕ):ℝ) := by exact_mod_cast hN
  have hscale : 0 ≤ b*((2^j:ℕ):ℝ) := (mul_pos hb hNR).le
  have hu : 7*dyadicBound K r j < 1 := by
    have := dyadicBound_le_initial hK hr0 hr1 j
    linarith
  apply gap_of_dyadic_exponential_bound b r (E k-E i₀) (2^j) hb hr0 hN
  calc
    Real.exp (-(b*((2^j:ℕ):ℝ))*(E k-E i₀)) ≤
        (7*dyadicBound K r j)/(1-7*dyadicBound K r j) :=
      gibbs_excited_exponential_bound E _ _ i₀ k hscale hu hk hground hpurity
    _ < r^(2^j) := dyadic_seven_ratio_lt hK hr0 hr1 hmargin j

#print axioms G7_one_percent_lt
#print axioms exists_dyadic_size_box
#print axioms purity_lower_from_interpolation
#print axioms finite_gibbs_gap_of_scaled_purity
end BilayerGap
