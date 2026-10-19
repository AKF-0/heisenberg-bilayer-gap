import Dressed.FiniteOccupationCCR

/-!
# Actual total-degree cutoff matrices

The basis is the subtype of product occupations with total degree at most N.
Creation is the genuine submatrix compression, not an abstract operator.
Pure-creation compression is exact because intermediate degree cannot decrease.
The mixed CCR is restricted to input grades strictly below N, with N ≤ M.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation.TotalCutoff
open Matrix
set_option maxHeartbeats 1400000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Basis (V : Type*) [Fintype V] (M N : ℕ) := TotalOccupation V M N
abbrev Op (V : Type*) [Fintype V] (M N : ℕ) :=
  Matrix (Basis V M N) (Basis V M N) ℝ

/-- Actual coordinate inclusion from the total cutoff into the product cutoff. -/
def inclusion (M N : ℕ) : Matrix (Occupation V M) (Basis V M N) ℝ :=
  fun ν μ => if ν = μ.val then 1 else 0

/-- Genuine entrywise compression to the total-cutoff subtype. -/
def compress {M N : ℕ} (A : FiniteOccupation.Op V M) : Op V M N :=
  A.submatrix Subtype.val Subtype.val

theorem inclusion_transpose_mul (M N : ℕ) :
    (inclusion (V := V) M N).transpose * inclusion (V := V) M N = 1 := by
  ext ν μ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclusion]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Subtype.val_inj, Matrix.one_apply]

theorem compression_entry {M N : ℕ} (A : FiniteOccupation.Op V M)
    (ν μ : Basis V M N) :
    ((inclusion (V := V) M N).transpose * A * inclusion (V := V) M N) ν μ =
      A ν.val μ.val := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, inclusion]

theorem compression_eq {M N : ℕ} (A : FiniteOccupation.Op V M) :
    (inclusion (V := V) M N).transpose * A * inclusion (V := V) M N =
      (compress (N := N) A : Op V M N) := by
  ext ν μ
  exact compression_entry A ν μ

/-- A product compression is valid when all excluded intermediate terms vanish.
This explicit premise is checked separately for each operator order. -/
theorem compress_mul_entry_of_support {M N : ℕ}
    (A B : FiniteOccupation.Op V M) (ν μ : Basis V M N)
    (hsupport : ∀ ρ : Occupation V M, N < totalDegree ρ → A ν.val ρ * B ρ μ.val = 0) :
    ((compress (N := N) A : Op V M N) * compress (N := N) B) ν μ = (A * B) ν.val μ.val := by
  simp only [Matrix.mul_apply, compress, Matrix.submatrix_apply]
  apply Fintype.sum_of_injective (Subtype.val : Basis V M N → Occupation V M)
    Subtype.val_injective
  · intro ρ hρ
    have hlarge : N < totalDegree ρ := by
      by_contra h
      exact hρ ⟨⟨ρ, by omega⟩, rfl⟩
    exact hsupport ρ hlarge
  · intro ρ
    rfl

/-- Actual total-cutoff creation. -/
def create {M N : ℕ} (i : Mode V) : Op V M N :=
  compress (FiniteOccupation.create (M := M) i)

/-- Actual total-cutoff annihilation, the real adjoint. -/
def annihilate {M N : ℕ} (i : Mode V) : Op V M N :=
  (create (M := M) (N := N) i).transpose

omit [DecidableEq V] in
theorem annihilate_eq_compress {M N : ℕ} (i : Mode V) :
    annihilate (M := M) (N := N) i =
      (compress (FiniteOccupation.annihilate (M := M) i) : Op V M N) := rfl

/-- A nonzero compressed creation entry raises degree exactly once. -/
theorem degree_of_create_ne_zero {M N : ℕ} (i : Mode V) (ν μ : Basis V M N)
    (h : create (M := M) (N := N) i ν μ ≠ 0) :
    totalDegree ν.val = totalDegree μ.val + 1 :=
  FiniteOccupation.degree_of_create_ne_zero i ν.val μ.val h

/-- A nonzero compressed annihilation entry lowers degree exactly once. -/
theorem degree_of_annihilate_ne_zero {M N : ℕ} (i : Mode V) (ν μ : Basis V M N)
    (h : annihilate (M := M) (N := N) i ν μ ≠ 0) :
    totalDegree μ.val = totalDegree ν.val + 1 :=
  FiniteOccupation.degree_of_annihilate_ne_zero i ν.val μ.val h

/-- Creation cannot repair an input that already exceeds the total cutoff. -/
theorem ambient_create_zero_of_large_input {M N : ℕ} (i : Mode V)
    (ν : Basis V M N) (ρ : Occupation V M) (hρ : N < totalDegree ρ) :
    FiniteOccupation.create (M := M) i ν.val ρ = 0 := by
  by_contra h
  have hd := FiniteOccupation.degree_of_create_ne_zero i ν.val ρ h
  have hν := ν.property
  omega

/-- Pure creation on the output side permits exact product compression. -/
theorem create_mul_compress {M N : ℕ} (i : Mode V) (B : FiniteOccupation.Op V M) :
    create (M := M) (N := N) i * (compress (N := N) B : Op V M N) =
      compress (FiniteOccupation.create (M := M) i * B) := by
  ext ν μ
  apply compress_mul_entry_of_support
  intro ρ hρ
  rw [ambient_create_zero_of_large_input i ν ρ hρ, zero_mul]

/-- Annihilation on the input side also has no excluded intermediate term. -/
theorem compress_mul_annihilate {M N : ℕ} (A : FiniteOccupation.Op V M) (i : Mode V) :
    (compress (N := N) A : Op V M N) * annihilate (M := M) (N := N) i =
      compress (A * FiniteOccupation.annihilate (M := M) i) := by
  ext ν μ
  rw [annihilate_eq_compress]
  apply compress_mul_entry_of_support
  intro ρ hρ
  have hz : FiniteOccupation.annihilate (M := M) i ρ μ.val = 0 := by
    by_contra h
    have hd := FiniteOccupation.degree_of_annihilate_ne_zero i ρ μ.val h
    have hμ := μ.property
    omega
  rw [hz, mul_zero]

/-- The exact pure-creation pair compression, at every total grade. -/
theorem create_mul_create {M N : ℕ} (i j : Mode V) :
    create (M := M) (N := N) i * create (M := M) (N := N) j =
      compress (FiniteOccupation.create (M := M) i * FiniteOccupation.create (M := M) j) :=
  create_mul_compress i _

/-- Compressed creations commute globally, including the last two grades. -/
theorem create_commute {M N : ℕ} (i j : Mode V) :
    Commute (create (M := M) (N := N) i) (create (M := M) (N := N) j) := by
  change create (M := M) (N := N) i * create (M := M) (N := N) j =
    create (M := M) (N := N) j * create (M := M) (N := N) i
  rw [create_mul_create, create_mul_create, (FiniteOccupation.create_commute i j).eq]

/-- The exact number operator compressed to the total-degree cutoff. -/
def number {M N : ℕ} : Op V M N := compress (FiniteOccupation.number : FiniteOccupation.Op V M)

omit [DecidableEq V] in
theorem number_eq_diagonal {M N : ℕ} : (number : Op V M N) =
    Matrix.diagonal (fun ν : Basis V M N => (totalDegree ν.val : ℝ)) := by
  ext ν μ
  simp only [number, compress, Matrix.submatrix_apply, FiniteOccupation.number,
    Matrix.diagonal_apply, Subtype.val_inj]

theorem sum_create_annihilate {M N : ℕ} :
    (∑ i : Mode V, create (M := M) (N := N) i * annihilate (M := M) (N := N) i) =
      (number : Op V M N) := by
  simp only [annihilate_eq_compress, create_mul_compress, number]
  ext ν μ
  simp only [Matrix.sum_apply, compress, Matrix.submatrix_apply]
  rw [← Matrix.sum_apply, FiniteOccupation.sum_create_annihilate]

/-- Creation kills the total top grade, independently of the coordinate cutoff. -/
theorem create_top_entry {M N : ℕ} (i : Mode V) (ν μ : Basis V M N)
    (hμ : totalDegree μ.val = N) : create (M := M) (N := N) i ν μ = 0 := by
  by_contra h
  have hd := degree_of_create_ne_zero i ν μ h
  have hν := ν.property
  omega

/-- A compressed creation pair has no matrix entries outside its exact degree shift. -/
theorem create_pair_eq_zero_of_degree {M N : ℕ} (i j : Mode V) (ν μ : Basis V M N)
    (hdegree : totalDegree ν.val ≠ totalDegree μ.val + 2) :
    (create (M := M) (N := N) i * create (M := M) (N := N) j) ν μ = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  by_cases hi : create (M := M) (N := N) i ν ρ = 0
  · rw [hi, zero_mul]
  · by_cases hj : create (M := M) (N := N) j ρ μ = 0
    · rw [hj, mul_zero]
    · have hleft := degree_of_create_ne_zero i ν ρ hi
      have hright := degree_of_create_ne_zero j ρ μ hj
      exact False.elim (hdegree (by omega))

/-- A creation pair kills both upper input grades; no missing top matrix entry
is silently restored when passing from product to total cutoff. -/
theorem create_pair_top_entry {M N : ℕ} (i j : Mode V) (ν μ : Basis V M N)
    (hμ : N < totalDegree μ.val + 2) :
    (create (M := M) (N := N) i * create (M := M) (N := N) j) ν μ = 0 := by
  apply create_pair_eq_zero_of_degree
  have hν := ν.property
  omega

/-- For input below the total cutoff, the raised intermediate remains inside.
This is the additional check needed for the annihilation-creation order. -/
theorem annihilate_create_safe_entry {M N : ℕ} (i j : Mode V) (ν μ : Basis V M N)
    (hμ : totalDegree μ.val < N) :
    (annihilate (M := M) (N := N) i * create (M := M) (N := N) j) ν μ =
      (FiniteOccupation.annihilate (M := M) i * FiniteOccupation.create (M := M) j)
        ν.val μ.val := by
  rw [annihilate_eq_compress]
  apply compress_mul_entry_of_support
  intro ρ hρ
  have hz : FiniteOccupation.create (M := M) j ρ μ.val = 0 := by
    by_contra h
    have hd := FiniteOccupation.degree_of_create_ne_zero j ρ μ.val h
    omega
  rw [hz, mul_zero]

/-- The exact safe-column CCR on the actual total-cutoff matrices. -/
theorem commutator_safe_entry {M N : ℕ} (hNM : N ≤ M)
    (i j : Mode V) (ν μ : Basis V M N) (hμ : totalDegree μ.val < N) :
    (annihilate (M := M) (N := N) i * create (M := M) (N := N) j -
        create (M := M) (N := N) j * annihilate (M := M) (N := N) i) ν μ =
      if i = j then if ν = μ then 1 else 0 else 0 := by
  rw [Matrix.sub_apply, annihilate_create_safe_entry i j ν μ hμ,
    annihilate_eq_compress, create_mul_compress]
  change _ - (FiniteOccupation.create (M := M) j * FiniteOccupation.annihilate (M := M) i)
    ν.val μ.val = _
  rw [← Matrix.sub_apply, FiniteOccupation.commutator]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, topProjector, Matrix.diagonal_apply, Subtype.val_inj]
    by_cases hνμ : ν = μ
    · subst μ
      have hcoord := coordinate_le_totalDegree ν.val i
      have hnot : (ν.val i).val ≠ M := by omega
      simp [hnot]
    · simp [hνμ]
  · simp [hij]

/-- Projection onto all grades at most n inside the actual total-cutoff space. -/
def degreeLEProjector {M N : ℕ} (n : ℕ) : Op V M N :=
  Matrix.diagonal (fun ν => if totalDegree ν.val ≤ n then 1 else 0)

/-- Ordinary CCR only below the total top grade. M = N is allowed. -/
theorem commutator_on_degreeLE {M N n : ℕ} (hNM : N ≤ M) (hnN : n < N)
    (i j : Mode V) :
    (annihilate (M := M) (N := N) i * create (M := M) (N := N) j -
        create (M := M) (N := N) j * annihilate (M := M) (N := N) i) *
        degreeLEProjector n =
      if i = j then (degreeLEProjector n : Op V M N) else 0 := by
  ext ν μ
  rw [degreeLEProjector, Matrix.mul_diagonal]
  by_cases hμ : totalDegree μ.val ≤ n
  · have hsafe : totalDegree μ.val < N := lt_of_le_of_lt hμ hnN
    rw [commutator_safe_entry hNM i j ν μ hsafe]
    by_cases hij : i = j <;> by_cases hνμ : ν = μ <;>
      simp [hij, hνμ, hμ]
  · by_cases hij : i = j <;> by_cases hνμ : ν = μ <;>
      simp [hij, hνμ, hμ]

/-- On the total top grade the missing creation term leaves the negative
annihilation-then-creation product, rather than a false identity commutator. -/
theorem commutator_top_entry {M N : ℕ} (i j : Mode V) (ν μ : Basis V M N)
    (hμ : totalDegree μ.val = N) :
    (annihilate (M := M) (N := N) i * create (M := M) (N := N) j -
        create (M := M) (N := N) j * annihilate (M := M) (N := N) i) ν μ =
      -(create (M := M) (N := N) j * annihilate (M := M) (N := N) i) ν μ := by
  rw [Matrix.sub_apply]
  have hz : (annihilate (M := M) (N := N) i * create (M := M) (N := N) j) ν μ = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro ρ _
    rw [create_top_entry j ρ μ hμ, mul_zero]
  rw [hz, zero_sub]

/-- The actual zero-occupation basis state lies in every total cutoff. -/
def vacuum {M N : ℕ} : Basis V M N :=
  ⟨fun _ => 0, by simp [totalDegree]⟩

omit [DecidableEq V] in
@[simp] theorem degree_vacuum {M N : ℕ} :
    totalDegree (vacuum : Basis V M N).val = 0 := by
  simp [vacuum, totalDegree]

/-- The degree-zero subspace has exactly the one vacuum basis label. -/
theorem eq_vacuum_of_degree_zero {M N : ℕ} (ν : Basis V M N)
    (hν : totalDegree ν.val = 0) : ν = vacuum := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := coordinate_le_totalDegree ν.val i
  change (ν.val i).val = 0
  omega

/-- Actual annihilation kills the finite-cutoff vacuum entrywise. -/
theorem annihilate_vacuum_entry {M N : ℕ} (i : Mode V) (ν : Basis V M N) :
    annihilate (M := M) (N := N) i ν vacuum = 0 := by
  by_contra h
  have hd := degree_of_annihilate_ne_zero i ν vacuum h
  rw [degree_vacuum] at hd
  omega

/-- The corresponding statement for the genuine vacuum column vector. -/
theorem annihilate_vacuum_vector {M N : ℕ} (i : Mode V) :
    (annihilate (M := M) (N := N) i).mulVec (Pi.single vacuum 1) = 0 := by
  ext ν
  simp [Matrix.mulVec_single, Matrix.col_apply, annihilate_vacuum_entry]

/-- The actual total-cutoff basis cannot exceed the product-basis dimension. -/
theorem card_le_product (M N : ℕ) :
    Fintype.card (Basis V M N) ≤ Fintype.card (Occupation V M) :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

omit [DecidableEq V] in
/-- The physical basis map into the site-count total cutoff is injective. -/
theorem physical_encode_injective {M : ℕ} (hM : 2 ≤ M) :
    Function.Injective (encodeTotal (V := V) hM) := by
  intro s t h
  exact encode_injective hM (congrArg Subtype.val h)

/-- Actual physical inclusion into the smaller total-cutoff space. -/
def physicalInclusion {M : ℕ} (hM : 2 ≤ M) :
    Matrix (Basis V M (Fintype.card V)) (Configuration V) ℝ :=
  fun ν s => if ν = encodeTotal hM s then 1 else 0

/-- The physical-to-total inclusion is an isometry, not a dimension assumption. -/
theorem physicalInclusion_transpose_mul {M : ℕ} (hM : 2 ≤ M) :
    (physicalInclusion (V := V) hM).transpose * physicalInclusion (V := V) hM = 1 := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, physicalInclusion]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [(physical_encode_injective hM).eq_iff, Matrix.one_apply]

/-- The two actual basis inclusions compose to the previously verified W. -/
theorem inclusion_mul_physicalInclusion {M : ℕ} (hM : 2 ≤ M) :
    inclusion (V := V) M (Fintype.card V) * physicalInclusion (V := V) hM =
      FiniteOccupation.inclusion (V := V) hM := by
  ext ν s
  simp [Matrix.mul_apply, inclusion, physicalInclusion, FiniteOccupation.inclusion,
    encodeTotal]

/-- Physical dimension is at most the total-cutoff dimension, in the direction
required for lower bounds on ascending eigenvalues under compression. -/
theorem card_physical_le_total {M : ℕ} (hM : 2 ≤ M) :
    Fintype.card (Configuration V) ≤ Fintype.card (Basis V M (Fintype.card V)) :=
  Fintype.card_le_of_injective (encodeTotal hM) (physical_encode_injective hM)

/-- Entrywise physical compression inside the smaller total-cutoff space. -/
theorem physical_compression_entry {M : ℕ} (hM : 2 ≤ M)
    (A : Op V M (Fintype.card V)) (s t : Configuration V) :
    ((physicalInclusion (V := V) hM).transpose * A * physicalInclusion (V := V) hM) s t =
      A (encodeTotal hM s) (encodeTotal hM t) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, physicalInclusion]

/-- The hard-core creation is also the compression of the actual total-cutoff creation. -/
theorem physical_compression_create {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3) :
    (physicalInclusion (V := V) hM).transpose *
        (create (v, α) : Op V M (Fintype.card V)) * physicalInclusion (V := V) hM =
      globalCreate v α := by
  ext s t
  rw [physical_compression_entry]
  exact create_encode_entry hM v α s t

/-- The physical distinct-site pair identity survives the intermediate total cutoff. -/
theorem physical_compression_create_pair {M : ℕ} (hM : 2 ≤ M)
    (u v : V) (huv : u ≠ v) (α β : Fin 3) :
    (physicalInclusion (V := V) hM).transpose *
        (create (M := M) (N := Fintype.card V) (u, α) *
          create (M := M) (N := Fintype.card V) (v, β)) * physicalInclusion (V := V) hM =
      globalCreate u α * globalCreate v β := by
  ext s t
  rw [physical_compression_entry, create_mul_create]
  exact create_pair_encode_entry hM u v huv α β s t

/-- The physical number is exactly the compressed total-cutoff number. -/
theorem physical_compression_number {M : ℕ} (hM : 2 ≤ M) :
    (physicalInclusion (V := V) hM).transpose *
        (number : Op V M (Fintype.card V)) * physicalInclusion (V := V) hM =
      TripletNumber.number := by
  ext s t
  rw [physical_compression_entry, TripletNumber.number_eq_diagonal]
  change FiniteOccupation.number (encode hM s) (encode hM t) = _
  simp only [FiniteOccupation.number, Matrix.diagonal_apply, (encode_injective hM).eq_iff,
    totalDegree_encode_cast]

end BilayerDressed.FiniteOccupation.TotalCutoff
