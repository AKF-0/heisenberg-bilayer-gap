import Gap.Squaring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite probability weights and conditional Gibbs gap extraction

This file does not construct the bilayer Hamiltonian or diagonalize it.
Its statements are finite-probability facts and a real exponential inequality.
The link from physical Gibbs energies to these hypotheses remains explicit.
-/
noncomputable section

namespace BilayerGap

open scoped BigOperators

/-- For a normalized nonnegative weight list, purity cannot exceed a largest weight. -/
theorem finitePurity_le_largest {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (i₀ : ι)
    (hnonneg : ∀ i, 0 ≤ w i) (hnorm : ∑ i, w i = 1)
    (hmax : ∀ i, w i ≤ w i₀) : finitePurity w ≤ w i₀ := by
  calc
    finitePurity w ≤ ∑ i, w i * w i₀ := by
      apply Finset.sum_le_sum
      intro i _
      simpa [pow_two] using mul_le_mul_of_nonneg_left (hmax i) (hnonneg i)
    _ = w i₀ := by rw [← Finset.sum_mul, hnorm, one_mul]

/-- Distinct weights fit inside the total mass; no maximality assumption is needed. -/
theorem two_weights_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hnonneg : ∀ k, 0 ≤ w k) (hnorm : ∑ k, w k = 1) :
    w i + w j ≤ 1 := by
  have h : ∑ k ∈ ({i,j} : Finset ι), w k ≤ ∑ k, w k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro k _ _; exact hnonneg k)
  simpa [Finset.sum_pair hij, hnorm] using h

/-- Purity above one half makes a maximal weight unique. -/
theorem largest_weight_unique_of_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (i₀ : ι)
    (hnonneg : ∀ i, 0 ≤ w i) (hnorm : ∑ i, w i = 1)
    (hmax : ∀ i, w i ≤ w i₀) (hp : (1:ℝ)/2 < finitePurity w) :
    ∀ j, w j = w i₀ → j = i₀ := by
  have hlarge : (1:ℝ)/2 < w i₀ := lt_of_lt_of_le hp (finitePurity_le_largest w i₀ hnonneg hnorm hmax)
  intro j heq
  by_contra hne
  have hsum := two_weights_le_one w j i₀ hne hnonneg hnorm
  linarith

/-- A purity defect bound controls each non-maximal eigenvector's weight ratio. -/
theorem excited_ratio_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (i₀ j : ι) (hj : i₀ ≠ j) (u : ℝ)
    (hnonneg : ∀ i, 0 ≤ w i) (hnorm : ∑ i, w i = 1)
    (hmax : ∀ i, w i ≤ w i₀) (hu : u < 1)
    (hp : 1-u ≤ finitePurity w) :
    w j / w i₀ ≤ u/(1-u) := by
  have hbase : 1-u ≤ w i₀ := le_trans hp (finitePurity_le_largest w i₀ hnonneg hnorm hmax)
  have hpos : 0 < w i₀ := lt_of_lt_of_le (sub_pos.mpr hu) hbase
  have hsum := two_weights_le_one w i₀ j hj hnonneg hnorm
  apply (div_le_div_iff₀ hpos (sub_pos.mpr hu)).2
  have hmul := mul_le_mul_of_nonneg_right (show w j ≤ 1-w i₀ by linarith) (le_of_lt (sub_pos.mpr hu))
  nlinarith

/-- An exponential ratio bound synchronized at inverse temperature b·N gives a
uniform energy bound. This is conditional on the supplied exponential bound,
not a theorem asserting that any particular Hamiltonian satisfies it. -/
theorem gap_of_dyadic_exponential_bound (b r γ : ℝ) (N : ℕ)
    (hb : 0 < b) (hr : 0 < r) (hN : 0 < N)
    (hbound : Real.exp (-(b*(N:ℝ))*γ) < r^N) :
    Real.log (1/r) / b < γ := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have heq : Real.exp ((N:ℝ)*Real.log r) = r^N := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  have hlog : -(b*(N:ℝ))*γ < (N:ℝ)*Real.log r := by
    exact Real.exp_lt_exp.mp (by simpa [heq] using hbound)
  have hlog_inv : Real.log (1/r) = - Real.log r := by simp
  rw [hlog_inv]
  apply (div_lt_iff₀ hb).2
  nlinarith

/-- Finite Gibbs partition function for an eigenvector-resolved energy list. -/
noncomputable def gibbsZ {ι : Type*} [Fintype ι] (E : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ i, Real.exp (-b * E i)

noncomputable def gibbsWeight {ι : Type*} [Fintype ι] (E : ι → ℝ) (b : ℝ) (i : ι) : ℝ :=
  Real.exp (-b * E i) / gibbsZ E b

theorem gibbsZ_pos {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (b : ℝ) :
    0 < gibbsZ E b := by
  classical
  unfold gibbsZ
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩

theorem gibbsWeight_pos {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (b : ℝ) (i : ι) :
    0 < gibbsWeight E b i :=
  div_pos (Real.exp_pos _) (gibbsZ_pos E b)

theorem gibbsWeight_sum {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (b : ℝ) :
    ∑ i, gibbsWeight E b i = 1 := by
  simp only [gibbsWeight, ← Finset.sum_div]
  change gibbsZ E b / gibbsZ E b = 1
  exact div_self (gibbsZ_pos E b).ne'

/-- Gibbs collision purity is exactly the partition-function ratio used in
coordinate `time`, with no assumed identification. -/
theorem gibbs_purity_partition_ratio {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (b : ℝ) :
    finitePurity (gibbsWeight E b) = gibbsZ E (2*b)/(gibbsZ E b)^2 := by
  unfold finitePurity gibbsWeight
  simp only [div_pow, ← Finset.sum_div]
  congr 1
  unfold gibbsZ
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Doubling inverse temperature really squares and renormalizes Gibbs weights. -/
theorem gibbsWeight_double {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (b : ℝ) (i : ι) :
    gibbsWeight E (2*b) i = (gibbsWeight E b i)^2 /
      finitePurity (gibbsWeight E b) := by
  rw [gibbs_purity_partition_ratio]
  unfold gibbsWeight
  have hexp : Real.exp (-(2*b)*E i) = Real.exp (-b*E i)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  field_simp [(gibbsZ_pos E b).ne', (gibbsZ_pos E (2*b)).ne']

/-- The physical temperature direction satisfies the purity-squaring estimate. -/
theorem gibbs_purity_squaring {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (b : ℝ) :
    1-finitePurity (gibbsWeight E (2*b)) ≤
      (1-finitePurity (gibbsWeight E b))^2 /
        (2*finitePurity (gibbsWeight E b)^2) := by
  have h := finite_purity_squaring (gibbsWeight E b)
    (fun i => (gibbsWeight_pos E b i).le) (gibbsWeight_sum E b)
  have heq : gibbsWeight E (2*b) = fun i => (gibbsWeight E b i)^2 /
      finitePurity (gibbsWeight E b) := by
    funext i
    exact gibbsWeight_double E b i
  rw [heq]
  exact h

theorem ground_gibbsWeight_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (b : ℝ) (i₀ : ι) (hb : 0 ≤ b) (hground : ∀ i, E i₀ ≤ E i) :
    ∀ i, gibbsWeight E b i ≤ gibbsWeight E b i₀ := by
  intro i
  apply div_le_div_of_nonneg_right _ (gibbsZ_pos E b).le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (hground i) (neg_nonpos.mpr hb)

theorem gibbsWeight_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (b : ℝ) (i j : ι) :
    gibbsWeight E b j / gibbsWeight E b i = Real.exp (-b*(E j-E i)) := by
  unfold gibbsWeight
  calc
    (Real.exp (-b*E j) / gibbsZ E b) / (Real.exp (-b*E i) / gibbsZ E b) =
        Real.exp (-b*E j) / Real.exp (-b*E i) := by
      field_simp [(gibbsZ_pos E b).ne', (Real.exp_pos (-b*E i)).ne']
    _ = Real.exp (-b*(E j-E i)) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- High Gibbs purity really excludes a repeated ground energy in the energy
list; this is not an assumption that the ground state was already unique. -/
theorem ground_energy_unique_of_gibbs_purity {ι : Type*} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] (E : ι → ℝ) (b : ℝ) (i₀ : ι)
    (hb : 0 ≤ b) (hground : ∀ i, E i₀ ≤ E i)
    (hp : (1:ℝ)/2 < finitePurity (gibbsWeight E b)) :
    ∀ j, E j = E i₀ → j = i₀ := by
  intro j heq
  apply largest_weight_unique_of_purity (gibbsWeight E b) i₀
    (fun i => (gibbsWeight_pos E b i).le) (gibbsWeight_sum E b)
    (ground_gibbsWeight_max E b i₀ hb hground) hp j
  simp only [gibbsWeight, heq]

/-- A finite Gibbs purity lower bound yields an exponential bound for each
excited eigenvector, with explicit normalization and ground-minimality. -/
theorem gibbs_excited_exponential_bound {ι : Type*} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] (E : ι → ℝ) (b u : ℝ) (i₀ j : ι)
    (hb : 0 ≤ b) (hu : u < 1) (hj : i₀ ≠ j) (hground : ∀ i, E i₀ ≤ E i)
    (hp : 1-u ≤ finitePurity (gibbsWeight E b)) :
    Real.exp (-b*(E j-E i₀)) ≤ u/(1-u) := by
  rw [← gibbsWeight_ratio E b i₀ j]
  exact excited_ratio_bound (gibbsWeight E b) i₀ j hj u
    (fun i => (gibbsWeight_pos E b i).le) (gibbsWeight_sum E b)
    (ground_gibbsWeight_max E b i₀ hb hground) hu hp

#print axioms gibbsWeight_sum
#print axioms gibbsWeight_ratio
#print axioms ground_energy_unique_of_gibbs_purity
#print axioms gibbs_excited_exponential_bound

#print axioms finitePurity_le_largest
#print axioms two_weights_le_one
#print axioms largest_weight_unique_of_purity
#print axioms excited_ratio_bound
#print axioms gap_of_dyadic_exponential_bound

end BilayerGap
