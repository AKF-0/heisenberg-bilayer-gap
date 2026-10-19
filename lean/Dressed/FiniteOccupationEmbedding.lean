import Dressed.PairVacuumNorm
import Dressed.NumberSpectrum
import Dressed.ProjectionAlgebra

/-!
# Finite-cutoff occupation representation of the physical hard-core space

The ambient basis is `(V × Fin 3) → Fin (M + 1)`, with coordinate cutoff
`M ≥ 2`. The physical four-state rung is embedded as vacuum or one occupied
color. Creation is the actual weighted one-coordinate increment matrix,
including its zero boundary column. No infinite Fock space or CCR is assumed.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation
open Matrix
set_option maxHeartbeats 1000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Mode (V : Type*) := V × Fin 3
abbrev Occupation (V : Type*) (M : ℕ) := Mode V → Fin (M + 1)
abbrev Op (V : Type*) (M : ℕ) := Matrix (Occupation V M) (Occupation V M) ℝ

/-- Rung index zero is vacuum; color `α` is precisely rung index `α.succ`. -/
def rungBits (i : Fin 4) (α : Fin 3) : ℕ := if i = α.succ then 1 else 0

theorem rungBits_injective : Function.Injective rungBits := by
  decide +kernel

theorem rungBits_step_iff (i j : Fin 4) (α : Fin 3) :
    (rungBits i α = rungBits j α + 1 ∧
      ∀ β, β ≠ α → rungBits i β = rungBits j β) ↔
    (i = α.succ ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases α <;> decide +kernel

theorem rungBits_sum (i : Fin 4) :
    (∑ α : Fin 3, rungBits i α) = if i = 0 then 0 else 1 := by
  fin_cases i <;> decide +kernel

/-- The concrete basis injection, with at most one color occupied at each site. -/
def encode {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) : Occupation V M :=
  fun i => ⟨rungBits (s i.1) i.2, by
    unfold rungBits
    split_ifs <;> omega⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem encode_val {M : ℕ} (hM : 2 ≤ M)
    (s : Configuration V) (i : Mode V) :
    (encode hM s i).val = rungBits (s i.1) i.2 := rfl

omit [Fintype V] [DecidableEq V] in
theorem encode_injective {M : ℕ} (hM : 2 ≤ M) :
    Function.Injective (encode (V := V) hM) := by
  intro s t h
  funext v
  apply rungBits_injective
  funext α
  exact congrArg Fin.val (congrFun h (v, α))

omit [Fintype V] [DecidableEq V] in
/-- Every physical occupation coordinate is zero or one. -/
theorem encode_coordinate_le_one {M : ℕ} (hM : 2 ≤ M)
    (s : Configuration V) (i : Mode V) : (encode hM s i).val ≤ 1 := by
  simp only [encode_val, rungBits]
  split_ifs <;> omega

omit [Fintype V] [DecidableEq V] in
/-- At most one of the three colors is occupied at any physical site. -/
theorem encode_site_sum_le_one {M : ℕ} (hM : 2 ≤ M)
    (s : Configuration V) (v : V) :
    (∑ α : Fin 3, (encode hM s (v, α)).val) ≤ 1 := by
  simp only [encode_val, rungBits_sum]
  split_ifs <;> omega

/-- Actual rectangular inclusion matrix from physical to occupation configurations. -/
def inclusion {M : ℕ} (hM : 2 ≤ M) :
    Matrix (Occupation V M) (Configuration V) ℝ :=
  fun ν s => if ν = encode hM s then 1 else 0

/-- Compression evaluates ambient entries at the injected physical indices. -/
theorem compression_entry {M : ℕ} (hM : 2 ≤ M) (A : Op V M)
    (s t : Configuration V) :
    ((inclusion (V := V) hM).transpose * A * inclusion (V := V) hM) s t =
      A (encode hM s) (encode hM t) := by
  classical
  simp [Matrix.mul_apply, Matrix.transpose_apply, inclusion]

/-- The inclusion is an exact real isometry: `Wᵀ W = I`. -/
theorem inclusion_transpose_mul {M : ℕ} (hM : 2 ≤ M) :
    (inclusion (V := V) hM).transpose * inclusion (V := V) hM = 1 := by
  classical
  ext s t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclusion]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [(encode_injective hM).eq_iff, Matrix.one_apply]

/-- Exact support of an increment, oriented as output then input. -/
def Raises {M : ℕ} (i : Mode V) (ν μ : Occupation V M) : Prop :=
  (ν i).val = (μ i).val + 1 ∧ ∀ j, j ≠ i → ν j = μ j

/-- Increment one allowed occupation coordinate, without any modular wraparound. -/
def increment {M : ℕ} (i : Mode V) (μ : Occupation V M) (hμ : (μ i).val < M) :
    Occupation V M :=
  Function.update μ i ⟨(μ i).val + 1, by omega⟩

omit [Fintype V] in
/-- The updated configuration satisfies the exact increment support relation. -/
theorem raises_increment {M : ℕ} (i : Mode V) (μ : Occupation V M)
    (hμ : (μ i).val < M) : Raises i (increment i μ hμ) μ := by
  constructor
  · simp [increment]
  · intro j hji
    simp [increment, Function.update_of_ne hji]

/-- Genuine finite-cutoff bosonic creation matrix. No wraparound at `M`. -/
def create {M : ℕ} (i : Mode V) : Op V M :=
  fun ν μ => if Raises i ν μ then Real.sqrt ((μ i).val + 1 : ℝ) else 0

omit [Fintype V] [DecidableEq V] in
theorem create_eq_zero_of_cutoff {M : ℕ} (i : Mode V) (ν μ : Occupation V M)
    (hμ : (μ i).val = M) : create i ν μ = 0 := by
  have hnot : ¬ Raises i ν μ := by
    intro h
    have hν := (ν i).isLt
    have hh := h.1
    omega
  simp [create, hnot]

omit [Fintype V] in
/-- The nonzero allowed entry has precisely the bosonic square-root weight. -/
theorem create_increment_entry {M : ℕ} (i : Mode V) (μ : Occupation V M)
    (hμ : (μ i).val < M) :
    create i (increment i μ hμ) μ = Real.sqrt ((μ i).val + 1 : ℝ) := by
  simp [create, raises_increment]

omit [Fintype V] in
/-- On physical endpoints, one occupation increment is exactly hard-core creation. -/
theorem raises_encode_iff {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3)
    (s t : Configuration V) :
    Raises (v, α) (encode hM s) (encode hM t) ↔
      t v = 0 ∧ s = Function.update t v α.succ := by
  classical
  constructor
  · rintro ⟨hval, hout⟩
    have hlocal : s v = α.succ ∧ t v = 0 := by
      apply (rungBits_step_iff _ _ _).mp
      refine ⟨hval, ?_⟩
      intro β hβα
      exact congrArg Fin.val (hout (v, β) (by simpa))
    refine ⟨hlocal.2, ?_⟩
    funext w
    by_cases hw : w = v
    · subst w
      simpa using hlocal.1
    · rw [Function.update_of_ne hw]
      apply rungBits_injective
      funext β
      exact congrArg Fin.val (hout (w, β) (by intro h; exact hw (congrArg Prod.fst h)))
  · rintro ⟨ht, rfl⟩
    constructor
    · simp [encode, rungBits, ht, eq_comm]
    · rintro ⟨w, β⟩ hwβ
      apply Fin.ext
      by_cases hw : w = v
      · subst w
        have hβα : β ≠ α := by simpa using hwβ
        simp [encode, rungBits, ht, Ne.symm hβα, eq_comm]
      · simp [encode, Function.update_of_ne hw]

/-- Entrywise equality with the frozen concrete tensor-lift creation. -/
theorem create_encode_entry {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3)
    (s t : Configuration V) :
    create (M := M) (v, α) (encode hM s) (encode hM t) = globalCreate v α s t := by
  classical
  rw [create, raises_encode_iff, globalCreate_entry_column]
  by_cases ht : t v = 0
  · simp [ht, encode, rungBits, eq_comm]
  · simp [ht]

/-- `C_{v,α} = Wᵀ a†_{v,α} W`, proved from the actual matrix entries. -/
theorem compression_create {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3) :
    (inclusion (V := V) hM).transpose * (create (M := M) (v, α) : Op V M) * inclusion (V := V) hM =
      globalCreate v α := by
  ext s t
  rw [compression_entry, create_encode_entry]

omit [Fintype V] in
/-- Pure creation cannot repair an unphysical input: with physical output,
the input is exactly the physical configuration obtained by erasing one triplet. -/
theorem input_is_physical_of_raises {M : ℕ} (hM : 2 ≤ M)
    (v : V) (α : Fin 3) (s : Configuration V) (μ : Occupation V M)
    (h : Raises (v, α) (encode hM s) μ) :
    s v = α.succ ∧ μ = encode hM (Function.update s v 0) := by
  have hs : s v = α.succ := by
    by_contra hs
    have hh := h.1
    simp [encode, rungBits, hs] at hh
  have hμ : (μ (v, α)).val = 0 := by
    have hh := h.1
    change rungBits (s v) α = (μ (v, α)).val + 1 at hh
    rw [rungBits, if_pos hs] at hh
    omega
  refine ⟨hs, ?_⟩
  funext ⟨w, β⟩
  apply Fin.ext
  by_cases hw : w = v
  · subst w
    by_cases hβα : β = α
    · subst β
      simp [encode, rungBits, hμ, eq_comm]
    · have hout := congrArg Fin.val (h.2 (v, β) (by simpa using hβα))
      simpa [encode, rungBits, hs, Ne.symm hβα, eq_comm] using hout.symm
  · have hout := congrArg Fin.val (h.2 (w, β) (by
      intro heq
      exact hw (congrArg Prod.fst heq)))
    simpa [encode, Function.update_of_ne hw] using hout.symm

omit [Fintype V] in
/-- With physical output, every nonphysical input creation entry vanishes. -/
theorem create_entry_zero_of_nonphysical_input {M : ℕ} (hM : 2 ≤ M)
    (v : V) (α : Fin 3) (s : Configuration V) (μ : Occupation V M)
    (hμ : μ ∉ Set.range (encode (V := V) hM)) :
    create (M := M) (v, α) (encode hM s) μ = 0 := by
  have hnot : ¬ Raises (v, α) (encode hM s) μ := by
    intro h
    exact hμ ⟨Function.update s v 0,
      (input_is_physical_of_raises hM v α s μ h).2.symm⟩
  simp [create, hnot]

/-- The correct one-sided intertwiner. The opposite direction is false because
ambient creation can produce doubly occupied, hence nonphysical, outputs. -/
theorem inclusion_transpose_create {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3) :
    (inclusion (V := V) hM).transpose * (create (M := M) (v, α) : Op V M) =
      globalCreate v α * (inclusion (V := V) hM).transpose := by
  ext s μ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclusion]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hμ : μ ∈ Set.range (encode (V := V) hM)
  · obtain ⟨t, rfl⟩ := hμ
    simp only [(encode_injective hM).eq_iff, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact create_encode_entry hM v α s t
  · rw [create_entry_zero_of_nonphysical_input hM v α s μ hμ]
    symm
    apply Finset.sum_eq_zero
    intro t _
    have hne : μ ≠ encode hM t := fun heq => hμ ⟨t, heq.symm⟩
    simp [hne]

/-- Orthogonal projection onto the actual embedded physical hard-core space. -/
def physicalProjector {M : ℕ} (hM : 2 ≤ M) : Op V M :=
  inclusion (V := V) hM * (inclusion (V := V) hM).transpose

/-- The concrete physical projector is symmetric. -/
theorem physicalProjector_transpose {M : ℕ} (hM : 2 ≤ M) :
    (physicalProjector (V := V) hM).transpose = physicalProjector (V := V) hM := by
  simp only [physicalProjector, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The concrete physical projector is idempotent. -/
theorem physicalProjector_idempotent {M : ℕ} (hM : 2 ≤ M) :
    physicalProjector (V := V) hM * physicalProjector (V := V) hM =
      physicalProjector (V := V) hM := by
  unfold physicalProjector
  calc
    _ = inclusion (V := V) hM *
        ((inclusion (V := V) hM).transpose * inclusion (V := V) hM) *
        (inclusion (V := V) hM).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [inclusion_transpose_mul, Matrix.mul_one]

/-- Pure creation does not carry a nonphysical input back into the physical space. -/
theorem physical_creation_no_repair {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3) :
    physicalProjector (V := V) hM * (create (M := M) (v, α) : Op V M) *
        (1 - physicalProjector (V := V) hM) = 0 := by
  have hcomp : (inclusion (V := V) hM).transpose *
      (1 - physicalProjector (V := V) hM) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, physicalProjector, ← Matrix.mul_assoc,
      inclusion_transpose_mul, Matrix.one_mul, sub_self]
  calc
    _ = inclusion (V := V) hM *
        ((inclusion (V := V) hM).transpose * create (M := M) (v, α)) *
        (1 - physicalProjector (V := V) hM) := by
      simp only [physicalProjector, Matrix.mul_assoc]
    _ = inclusion (V := V) hM *
        (globalCreate v α * (inclusion (V := V) hM).transpose) *
        (1 - physicalProjector (V := V) hM) := by rw [inclusion_transpose_create]
    _ = (inclusion (V := V) hM * globalCreate v α) *
        ((inclusion (V := V) hM).transpose *
          (1 - physicalProjector (V := V) hM)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hcomp, Matrix.mul_zero]

/-- The actual occupation embedding discharges the abstract no-repair premise
used by the existing polynomial projection algebra. -/
theorem physical_creation_projectionStable {M : ℕ} (hM : 2 ≤ M)
    (v : V) (α : Fin 3) :
    BilayerDressed.ProjectionStable (physicalProjector (V := V) hM)
      (create (v, α) : Op V M) :=
  (BilayerDressed.projectionStable_iff_discarded_zero _ _).mpr
    (physical_creation_no_repair hM v α)

omit [Fintype V] in
/-- A two-increment path at distinct sites with physical endpoints has a physical
intermediate. This is the support fact needed for pair compression; arbitrary
compression of products is not being assumed. -/
theorem intermediate_is_physical {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3)
    (s t : Configuration V) (μ : Occupation V M)
    (hleft : Raises (u, α) (encode hM s) μ)
    (hright : Raises (v, β) μ (encode hM t)) :
    μ = encode hM (Function.update t v (s v)) := by
  funext ⟨w, γ⟩
  by_cases hw : w = v
  · subst w
    have hvu : (v, γ) ≠ (u, α) := by
      intro h
      exact huv (congrArg Prod.fst h).symm
    simpa [encode] using (hleft.2 (v, γ) hvu).symm
  · have hwv : (w, γ) ≠ (v, β) := by
      intro h
      exact hw (congrArg Prod.fst h)
    simpa [encode, Function.update_of_ne hw] using hright.2 (w, γ) hwv

omit [Fintype V] in
/-- Nonphysical intermediate configurations contribute exactly zero. -/
theorem pair_entry_zero_outside_physical {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3)
    (s t : Configuration V) (μ : Occupation V M)
    (hμ : μ ∉ Set.range (encode (V := V) hM)) :
    create (M := M) (u, α) (encode hM s) μ * create (M := M) (v, β) μ (encode hM t) = 0 := by
  by_cases hl : Raises (u, α) (encode hM s) μ
  · by_cases hr : Raises (v, β) μ (encode hM t)
    · exact False.elim (hμ ⟨Function.update t v (s v),
        (intermediate_is_physical hM u v huv α β s t μ hl hr).symm⟩)
    · simp [create, hr]
  · simp [create, hl]

/-- Entrywise product equality, justified by the physical intermediate support. -/
theorem create_pair_encode_entry {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3) (s t : Configuration V) :
    ((create (M := M) (u, α) : Op V M) * create (M := M) (v, β)) (encode hM s) (encode hM t) =
      (globalCreate u α * globalCreate v β) s t := by
  simp only [Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (encode hM) (encode_injective hM)
  · intro μ hμ
    exact pair_entry_zero_outside_physical hM u v huv α β s t μ hμ
  · intro r
    rw [create_encode_entry, create_encode_entry]

/-- Genuine distinct-site pair compression, for arbitrary colors. -/
theorem compression_create_pair {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3) :
    (inclusion (V := V) hM).transpose *
        ((create (M := M) (u, α) : Op V M) * create (M := M) (v, β)) * inclusion (V := V) hM =
      globalCreate u α * globalCreate v β := by
  ext s t
  rw [compression_entry, create_pair_encode_entry hM u v huv]

/-- Actual ambient sum over the three same-color pair channels. -/
def pairCreate {M : ℕ} (u v : V) : Op V M :=
  ∑ α : Fin 3, create (M := M) (u, α) * create (M := M) (v, α)

/-- Compression agrees with the frozen physical SU(2)-invariant pair creation. -/
theorem compression_pairCreate {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) :
    (inclusion (V := V) hM).transpose * (pairCreate u v : Op V M) *
        inclusion (V := V) hM = BilayerDressed.pairCreate u v := by
  simp only [pairCreate, BilayerDressed.pairCreate, Matrix.mul_sum, Matrix.sum_mul,
    compression_create_pair hM u v huv]

/-- Total occupation degree in the actual finite product basis. -/
def totalDegree {M : ℕ} (ν : Occupation V M) : ℕ := ∑ i, (ν i).val

/-- Every actual creation support entry raises total degree by exactly one. -/
theorem totalDegree_of_raises {M : ℕ} (i : Mode V) (ν μ : Occupation V M)
    (h : Raises i ν μ) : totalDegree ν = totalDegree μ + 1 := by
  have hν := Finset.sum_erase_add (Finset.univ : Finset (Mode V))
    (fun j => (ν j).val) (Finset.mem_univ i)
  have hμ := Finset.sum_erase_add (Finset.univ : Finset (Mode V))
    (fun j => (μ j).val) (Finset.mem_univ i)
  have hout : (∑ j ∈ (Finset.univ : Finset (Mode V)).erase i, (ν j).val) =
      ∑ j ∈ (Finset.univ : Finset (Mode V)).erase i, (μ j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h.2 j (Finset.mem_erase.mp hj).1]
  have hi := h.1
  dsimp only at hν hμ
  unfold totalDegree
  omega

/-- Creation has no entries between any other pair of homogeneous grades. -/
theorem create_eq_zero_of_degree {M : ℕ} (i : Mode V) (ν μ : Occupation V M)
    (hdegree : totalDegree ν ≠ totalDegree μ + 1) : create i ν μ = 0 := by
  have hnot : ¬ Raises i ν μ := fun h => hdegree (totalDegree_of_raises i ν μ h)
  simp [create, hnot]

/-- Total-degree cutoff, kept separate from the per-coordinate cutoff. -/
abbrev TotalOccupation (V : Type*) [Fintype V] (M N : ℕ) :=
  {ν : Occupation V M // totalDegree ν ≤ N}

/-- Exact homogeneous occupation grade. -/
abbrev ExactGrade (V : Type*) [Fintype V] (M n : ℕ) :=
  {ν : Occupation V M // totalDegree ν = n}

omit [DecidableEq V] in
/-- Physical encoded degree is the exact number of nonvacuum rungs. -/
theorem totalDegree_encode {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) :
    totalDegree (encode hM s) = ∑ v, if s v = 0 then 0 else 1 := by
  simp only [totalDegree, Fintype.sum_prod_type, encode_val, rungBits_sum]

omit [DecidableEq V] in
/-- No encoded physical state has more particles than sites. -/
theorem totalDegree_encode_le_card {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) :
    totalDegree (encode hM s) ≤ Fintype.card V := by
  rw [totalDegree_encode]
  calc
    (∑ v, if s v = 0 then 0 else 1) ≤ ∑ _v : V, 1 := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    _ = Fintype.card V := by simp

/-- The same physical basis injection lands in the site-count total cutoff. -/
def encodeTotal {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) :
    TotalOccupation V M (Fintype.card V) :=
  ⟨encode hM s, totalDegree_encode_le_card hM s⟩

omit [DecidableEq V] in
/-- Exact real-valued match with the frozen physical triplet-count energy. -/
theorem totalDegree_encode_cast {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) :
    (totalDegree (encode hM s) : ℝ) = TripletNumber.energy s := by
  rw [totalDegree_encode]
  simp [TripletNumber.energy, TripletNumber.localEnergy, Nat.cast_sum]

/-- Genuine diagonal total occupation-number matrix. -/
def number {M : ℕ} : Op V M := Matrix.diagonal (fun ν => (totalDegree ν : ℝ))

/-- `N_physical = Wᵀ N_occupation W`, for the already verified physical number. -/
theorem compression_number {M : ℕ} (hM : 2 ≤ M) :
    (inclusion (V := V) hM).transpose * (number : Op V M) * inclusion (V := V) hM =
      TripletNumber.number := by
  ext s t
  rw [compression_entry, TripletNumber.number_eq_diagonal]
  simp only [number, Matrix.diagonal_apply, (encode_injective hM).eq_iff,
    totalDegree_encode_cast]

/-- Spectral projector onto a total-degree cutoff in the ambient product space. -/
def degreeLEProjector {M : ℕ} (N : ℕ) : Op V M :=
  Matrix.diagonal (fun ν => if totalDegree ν ≤ N then 1 else 0)

/-- The entire physical included space, not merely individual chosen vectors,
lies inside the total-degree cutoff at the number of sites. -/
theorem degreeLEProjector_inclusion {M : ℕ} (hM : 2 ≤ M) :
    (degreeLEProjector (Fintype.card V) : Op V M) * inclusion (V := V) hM =
      inclusion (V := V) hM := by
  ext ν s
  rw [degreeLEProjector, Matrix.diagonal_mul]
  by_cases hν : ν = encode hM s
  · subst ν
    simp [totalDegree_encode_le_card]
  · simp [inclusion, hν]

end BilayerDressed.FiniteOccupation
