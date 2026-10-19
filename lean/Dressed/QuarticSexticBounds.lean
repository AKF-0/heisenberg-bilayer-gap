import Dressed.ColorSectorBounds
import Dressed.GlobalResidualDegrees

/-!
# Literal quartic and sextic residuals in the physical Hilbert operator norm

Every norm below is a Euclidean continuous-linear-map norm. The coefficient
matrices can be arbitrary; no commutation, Wick rule, or independent-field
assumption is used in the bounds. The final coercion interface identifies these
literal noncommutative polynomials with the exact creation-algebra residuals.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticSextic
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1500000

/-- The actual finite configuration Hilbert-space operator norm. -/
abbrev hnorm (M : ConfigurationMatrix V) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) M‖

/-- Ordered coefficient contraction, with no commutativity assumption. -/
def fieldDot (A B : Fin 3 → ConfigurationMatrix V) : ConfigurationMatrix V :=
  ∑ α, A α * B α

/-- Literal ordered quartic polynomial, including both signs and all k terms. -/
def literalR4 (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (k : ℝ) :
    ConfigurationMatrix V :=
  -(∑ α : Fin 3, globalCreate u α * A α * fieldDot A B) -
  (∑ β : Fin 3, globalCreate v β * B β * fieldDot A B) +
  ∑ α : Fin 3, ∑ β : Fin 3, globalCreate u α * globalCreate v β *
    (B α * A β - (if α = β then fieldDot A B else 0) - A α * A β - B α * B β +
      (3*k) • (A α * B β) - (if α = β then k • fieldDot A B else 0))

/-- The full sextic polynomial, with no discarded term. -/
def literalR6 (u v : V) (A B : Fin 3 → ConfigurationMatrix V) :
    ConfigurationMatrix V :=
  ∑ α : Fin 3, ∑ β : Fin 3,
    globalCreate u α * globalCreate v β * A α * B β * fieldDot A B

lemma hnorm_mul_le (M N : ConfigurationMatrix V) :
    hnorm (M*N) ≤ hnorm M * hnorm N := by
  simp only [hnorm, map_mul]
  exact norm_mul_le _ _

lemma hnorm_sum_le {I : Type*} [Fintype I] (M : I → ConfigurationMatrix V) :
    hnorm (∑ i,M i) ≤ ∑ i,hnorm (M i) := by
  simp only [hnorm, map_sum]
  exact norm_sum_le _ _

lemma hnorm_add_le (M N : ConfigurationMatrix V) :
    hnorm (M+N) ≤ hnorm M + hnorm N := by
  simp only [hnorm, map_add]
  exact norm_add_le _ _

lemma hnorm_sub_le (M N : ConfigurationMatrix V) :
    hnorm (M-N) ≤ hnorm M + hnorm N := by
  simp only [hnorm, map_sub]
  exact norm_sub_le _ _

@[simp] lemma hnorm_neg (M : ConfigurationMatrix V) : hnorm (-M) = hnorm M := by
  simp [hnorm]

@[simp] lemma hnorm_smul (c : ℝ) (M : ConfigurationMatrix V) :
    hnorm (c • M) = |c| * hnorm M := by
  simp [hnorm, norm_smul, Real.norm_eq_abs]

lemma fieldDot_norm_le (A B : Fin 3 → ConfigurationMatrix V) (l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm (fieldDot A B) ≤ 3*l^2 := by
  calc
    _ ≤ ∑ α : Fin 3,hnorm (A α * B α) := hnorm_sum_le _
    _ ≤ ∑ _α : Fin 3,l^2 := Finset.sum_le_sum fun α _ =>
      (hnorm_mul_le _ _).trans (by simpa only [pow_two] using (mul_le_mul (hA α) (hB α) (norm_nonneg _) hl))
    _ = _ := by simp

lemma single_cubic_norm_le (u : V) (A B D : Fin 3 → ConfigurationMatrix V) (l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l)
    (hB : ∀ α,hnorm (B α) ≤ l) (hD : ∀ α,hnorm (D α) ≤ l) :
    hnorm (∑ α : Fin 3,globalCreate u α * A α * fieldDot B D) ≤
      3*Real.sqrt 3*l^3 := by
  have hd := fieldDot_norm_le B D l hl hB hD
  have ha : ∀ α,hnorm (A α * fieldDot B D) ≤ 3*l^3 := by
    intro α
    calc
      _ ≤ hnorm (A α)*hnorm (fieldDot B D) := hnorm_mul_le _ _
      _ ≤ l*(3*l^2) := mul_le_mul (hA α) hd (norm_nonneg _) hl
      _ = _ := by ring
  have hh := ColorSector.single_creation_sum_opNorm_le u
    (fun α => A α * fieldDot B D) (3*l^3) (by positivity) ha
  calc
    _ = hnorm (∑ α : Fin 3,globalCreate u α * (A α * fieldDot B D)) := by
      simp only [mul_assoc]
    _ ≤ Real.sqrt 3 * (3*l^3) := hh
    _ = _ := by ring

lemma double_product_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm (∑ α : Fin 3,∑ β : Fin 3,
      globalCreate u α * globalCreate v β * (A α * B β)) ≤ 3*l^2 := by
  apply ColorSector.double_creation_sum_opNorm_le u v _ (l^2) (sq_nonneg l)
  intro α β
  exact (hnorm_mul_le _ _).trans (by simpa only [pow_two] using (mul_le_mul (hA α) (hB β) (norm_nonneg _) hl))

lemma diagonal_norm_le (u v : V) (M : ConfigurationMatrix V) :
    hnorm (∑ α : Fin 3,∑ β : Fin 3,
      globalCreate u α * globalCreate v β * (if α = β then M else 0)) ≤
      Real.sqrt 3 * hnorm M := by
  classical
  have he : (∑ α : Fin 3,∑ β : Fin 3,
      globalCreate u α * globalCreate v β * (if α = β then M else 0)) =
      pairCreate u v * M := by
    simp [pairCreate, Finset.sum_mul, mul_ite]
  rw [he]
  exact (hnorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (pairCreate_opNorm_le_sqrt_three u v) (norm_nonneg _))

lemma diagonal_dot_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm (∑ α : Fin 3,∑ β : Fin 3,
      globalCreate u α * globalCreate v β * (if α = β then fieldDot A B else 0)) ≤
      3*Real.sqrt 3*l^2 := by
  exact (diagonal_norm_le u v _).trans (by
    have hh := mul_le_mul_of_nonneg_left (fieldDot_norm_le A B l hl hA hB)
      (Real.sqrt_nonneg 3)
    nlinarith)

lemma literalR6_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm (literalR6 u v A B) ≤ 9*l^4 := by
  have hab : ∀ α β,hnorm (A α * B β * fieldDot A B) ≤ 3*l^4 := by
    intro α β
    have hab : hnorm (A α * B β) ≤ l^2 :=
      (hnorm_mul_le _ _).trans (by simpa only [pow_two] using (mul_le_mul (hA α) (hB β) (norm_nonneg _) hl))
    calc
      _ ≤ hnorm (A α * B β)*hnorm (fieldDot A B) := hnorm_mul_le _ _
      _ ≤ l^2*(3*l^2) := mul_le_mul hab (fieldDot_norm_le A B l hl hA hB)
        (norm_nonneg _) (sq_nonneg l)
      _ = _ := by ring
  have hh := ColorSector.double_creation_sum_opNorm_le u v
    (fun α β => A α * B β * fieldDot A B) (3*l^4) (by positivity) hab
  calc
    _ = hnorm (∑ α : Fin 3,∑ β : Fin 3,
      globalCreate u α * globalCreate v β * (A α * B β * fieldDot A B)) := by
        simp only [literalR6, mul_assoc]
    _ ≤ 3*(3*l^4) := hh
    _ = _ := by ring


/-- Split the literal polynomial without changing any order of matrix factors. -/
lemma literalR4_split (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (k : ℝ) :
    literalR4 u v A B k =
    -(∑ α : Fin 3,globalCreate u α * A α * fieldDot A B) -
    (∑ β : Fin 3,globalCreate v β * B β * fieldDot A B) +
    ((∑ α : Fin 3,∑ β : Fin 3,globalCreate u α * globalCreate v β * (B α * A β)) -
     (∑ α : Fin 3,∑ β : Fin 3,globalCreate u α * globalCreate v β *
       (if α = β then fieldDot A B else 0)) -
     (∑ α : Fin 3,∑ β : Fin 3,globalCreate u α * globalCreate v β * (A α * A β)) -
     (∑ α : Fin 3,∑ β : Fin 3,globalCreate u α * globalCreate v β * (B α * B β)) +
     (3*k) • (∑ α : Fin 3,∑ β : Fin 3,
       globalCreate u α * globalCreate v β * (A α * B β)) -
     k • (∑ α : Fin 3,∑ β : Fin 3,globalCreate u α * globalCreate v β *
       (if α = β then fieldDot A B else 0))) := by
  classical
  simp only [literalR4, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_smul_comm, Finset.smul_sum, mul_ite, smul_ite, smul_zero, mul_zero]

lemma hnorm_six_terms_le (P Q R S T W : ConfigurationMatrix V) :
    hnorm (P-Q-R-S+T-W) ≤
      hnorm P + hnorm Q + hnorm R + hnorm S + hnorm T + hnorm W := by
  have h1 := hnorm_sub_le P Q
  have h2 := hnorm_sub_le (P-Q) R
  have h3 := hnorm_sub_le (P-Q-R) S
  have h4 := hnorm_add_le (P-Q-R-S) T
  have h5 := hnorm_sub_le (P-Q-R-S+T) W
  linarith

/-- Complete quartic bound, using orthogonal physical output-color sectors. -/
theorem literalR4_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V) (k l : ℝ)
    (hl : 0 ≤ l) (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm (literalR4 u v A B k) ≤
      (9+3*Real.sqrt 3)*l^2*(1+|k|) + 6*Real.sqrt 3*l^3 := by
  have hX := single_cubic_norm_le u A A B l hl hA hA hB
  have hY := single_cubic_norm_le v B A B l hl hB hA hB
  have hP := double_product_norm_le u v B A l hl hB hA
  have hD := diagonal_dot_norm_le u v A B l hl hA hB
  have hQ := double_product_norm_le u v A A l hl hA hA
  have hR := double_product_norm_le u v B B l hl hB hB
  have hT := double_product_norm_le u v A B l hl hA hB
  rw [literalR4_split]
  refine (hnorm_add_le _ _).trans ?_
  refine (add_le_add (hnorm_sub_le _ _) (hnorm_six_terms_le _ _ _ _ _ _)).trans ?_
  simp only [hnorm_neg, hnorm_smul, abs_mul, show |(3:ℝ)| = 3 by norm_num]
  have hks := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 3*|k|)
  have hkd := mul_le_mul_of_nonneg_left hD (abs_nonneg k)
  nlinarith


/-- Exact identification with the creation-algebra polynomial from the local bond calculation. -/
theorem coe_bondR6 (u v : V) (A B : Fin 3 → GlobalResidual.creationAlgebra V) :
    ((GlobalResidual.bondR6 (GlobalResidual.C u) (GlobalResidual.C v) A B :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) =
      literalR6 u v (fun α => A α) (fun α => B α) := by
  simp [GlobalResidual.bondR6, literalR6, fieldDot, LocalBond.dot]

/-- Exact identification retaining both diagonal k terms and all quartic signs. -/
theorem coe_bondR4 (u v : V) (A B : Fin 3 → GlobalResidual.creationAlgebra V) (k : ℝ) :
    ((GlobalResidual.bondR4 (GlobalResidual.C u) (GlobalResidual.C v) A B
      (algebraMap ℝ (GlobalResidual.creationAlgebra V) k) :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) =
      literalR4 u v (fun α => A α) (fun α => B α) k := by
  have h3 : ((3 : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) =
      algebraMap ℝ (ConfigurationMatrix V) 3 := by
    change (GlobalResidual.creationAlgebra V).val (3 : GlobalResidual.creationAlgebra V) = _
    simp only [map_ofNat]
  simp [GlobalResidual.bondR4, literalR4, fieldDot, LocalBond.dot,
    Algebra.smul_def, map_mul, mul_assoc, apply_ite, h3]

/-- The exact degree-four creation-algebra residual has the proved physical norm bound. -/
theorem bondR4_norm_le (u v : V) (A B : Fin 3 → GlobalResidual.creationAlgebra V)
    (k l : ℝ) (hl : 0 ≤ l)
    (hA : ∀ α,hnorm (A α : ConfigurationMatrix V) ≤ l)
    (hB : ∀ α,hnorm (B α : ConfigurationMatrix V) ≤ l) :
    hnorm ((GlobalResidual.bondR4 (GlobalResidual.C u) (GlobalResidual.C v) A B
      (algebraMap ℝ (GlobalResidual.creationAlgebra V) k) :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) ≤
      (9+3*Real.sqrt 3)*l^2*(1+|k|) + 6*Real.sqrt 3*l^3 := by
  rw [coe_bondR4]
  exact literalR4_norm_le u v _ _ k l hl hA hB

/-- The exact degree-six creation-algebra residual is retained and bounded. -/
theorem bondR6_norm_le (u v : V) (A B : Fin 3 → GlobalResidual.creationAlgebra V)
    (l : ℝ) (hl : 0 ≤ l)
    (hA : ∀ α,hnorm (A α : ConfigurationMatrix V) ≤ l)
    (hB : ∀ α,hnorm (B α : ConfigurationMatrix V) ≤ l) :
    hnorm ((GlobalResidual.bondR6 (GlobalResidual.C u) (GlobalResidual.C v) A B :
      GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) ≤ 9*l^4 := by
  rw [coe_bondR6]
  exact literalR6_norm_le u v _ _ l hl hA hB

/-- An exact rational arithmetic bound at the finite small-coupling checkpoint. -/
theorem quartic_scalar_bound (g k l : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 3/200)
    (hl : 0 ≤ l) (hlmax : l ≤ (39/50)*g) (hk : |k| ≤ (13/50)*g) :
    (g/2)*((9+3*Real.sqrt 3)*l^2*(1+|k|)+6*Real.sqrt 3*l^3) ≤ (9/2)*g^3 := by
  have hr : Real.sqrt 3 ≤ 7/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hb : (9+3*Real.sqrt 3)*l^2*(1+|k|)+6*Real.sqrt 3*l^3 ≤
      (57/4)*((39/50)*g)^2*(1+(13/50)*g)+(21/2)*((39/50)*g)^3 := by
    gcongr <;> linarith
  have hp := mul_nonneg (pow_nonneg hg 3) (sub_nonneg.mpr hgmax)
  calc
    _ ≤ (g/2)*((57/4)*((39/50)*g)^2*(1+(13/50)*g)+
      (21/2)*((39/50)*g)^3) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := by nlinarith [pow_nonneg hg 3]

/-- The sextic coefficient remains below the claimed finite constant. -/
theorem sextic_scalar_bound (g l : ℝ) (hg : 0 ≤ g) (hl : 0 ≤ l)
    (hlmax : l ≤ (39/50)*g) : (g/2)*(9*l^4) ≤ 2*g^5 := by
  have hp := pow_le_pow_left₀ hl hlmax 4
  have hh := mul_le_mul_of_nonneg_left hp hg
  nlinarith [pow_nonneg hg 5]


/-- Physical g/2 edge prefactor, at the finite coupling checkpoint. -/
theorem literalR4_scaled_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V)
    (g k l : ℝ) (hg : 0 ≤ g) (hgmax : g ≤ 3/200)
    (hl : 0 ≤ l) (hlmax : l ≤ (39/50)*g) (hk : |k| ≤ (13/50)*g)
    (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm ((g/2) • literalR4 u v A B k) ≤ (9/2)*g^3 := by
  rw [hnorm_smul, abs_of_nonneg (by positivity : 0 ≤ g/2)]
  exact (mul_le_mul_of_nonneg_left (literalR4_norm_le u v A B k l hl hA hB)
    (by positivity)).trans (quartic_scalar_bound g k l hg hgmax hl hlmax hk)

/-- The sextic edge term is never dropped when multiplying by g/2. -/
theorem literalR6_scaled_norm_le (u v : V) (A B : Fin 3 → ConfigurationMatrix V)
    (g l : ℝ) (hg : 0 ≤ g) (hl : 0 ≤ l) (hlmax : l ≤ (39/50)*g)
    (hA : ∀ α,hnorm (A α) ≤ l) (hB : ∀ α,hnorm (B α) ≤ l) :
    hnorm ((g/2) • literalR6 u v A B) ≤ 2*g^5 := by
  rw [hnorm_smul, abs_of_nonneg (by positivity : 0 ≤ g/2)]
  exact (mul_le_mul_of_nonneg_left (literalR6_norm_le u v A B l hl hA hB)
    (by positivity)).trans (sextic_scalar_bound g l hg hl hlmax)

/-- Summing exactly 2n physical edges yields the finite quartic 9ng³ bound. -/
theorem sum_literalR4_norm_le {E : Type*} [Fintype E]
    (u v : E → V) (A B : E → Fin 3 → ConfigurationMatrix V) (k : E → ℝ)
    (n : ℕ) (hcard : Fintype.card E = 2*n) (g l : ℝ)
    (hg : 0 ≤ g) (hgmax : g ≤ 3/200) (hl : 0 ≤ l) (hlmax : l ≤ (39/50)*g)
    (hk : ∀ e,|k e| ≤ (13/50)*g)
    (hA : ∀ e α,hnorm (A e α) ≤ l) (hB : ∀ e α,hnorm (B e α) ≤ l) :
    hnorm (∑ e,(g/2) • literalR4 (u e) (v e) (A e) (B e) (k e)) ≤
      9*(n:ℝ)*g^3 := by
  calc
    _ ≤ ∑ e,hnorm ((g/2) • literalR4 (u e) (v e) (A e) (B e) (k e)) :=
      hnorm_sum_le _
    _ ≤ ∑ _e : E,(9/2)*g^3 := Finset.sum_le_sum fun e _ =>
      literalR4_scaled_norm_le _ _ _ _ g _ l hg hgmax hl hlmax (hk e) (hA e) (hB e)
    _ = _ := by simp [hcard]; ring

/-- Summing exactly 2n physical edges retains and bounds the sextic term by 4ng⁵. -/
theorem sum_literalR6_norm_le {E : Type*} [Fintype E]
    (u v : E → V) (A B : E → Fin 3 → ConfigurationMatrix V)
    (n : ℕ) (hcard : Fintype.card E = 2*n) (g l : ℝ)
    (hg : 0 ≤ g) (hl : 0 ≤ l) (hlmax : l ≤ (39/50)*g)
    (hA : ∀ e α,hnorm (A e α) ≤ l) (hB : ∀ e α,hnorm (B e α) ≤ l) :
    hnorm (∑ e,(g/2) • literalR6 (u e) (v e) (A e) (B e)) ≤
      4*(n:ℝ)*g^5 := by
  calc
    _ ≤ ∑ e,hnorm ((g/2) • literalR6 (u e) (v e) (A e) (B e)) := hnorm_sum_le _
    _ ≤ ∑ _e : E,2*g^5 := Finset.sum_le_sum fun e _ =>
      literalR6_scaled_norm_le _ _ _ _ g l hg hl hlmax (hA e) (hB e)
    _ = _ := by simp [hcard]; ring

end BilayerDressed.QuarticSextic
