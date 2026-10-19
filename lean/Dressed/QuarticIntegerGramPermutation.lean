import Dressed.QuarticIntegerNormEvaluation

/-! The exact signed integer Gram polynomial is invariant under any permutation
of the three matching coefficients. This does not supply a sorting correspondence
or identify any actual coefficient with a representative. Those finite witness
relations remain separate. No claim of unweighted mean invariance is made.
-/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerGramPermutation
open QuarticIntegerArrays QuarticIntegerNorm
set_option maxHeartbeats 600000

/-- Both the diagonal convolution sum and the sum inside the cross term are
transported by an actual bijection of the three matching labels. -/
theorem gram_reindex (a : Fin 3 → Coefficients) (p : Equiv.Perm (Fin 3)) :
    gram (fun i=>a (p i))=gram a := by
  have hc : (∑ i : Fin 3,convolution (a (p i)) (a (p i)))=
      ∑ i : Fin 3,convolution (a i) (a i) :=
    Equiv.sum_comp p (fun i=>convolution (a i) (a i))
  have ha : (∑ i : Fin 3,a (p i))=∑ i : Fin 3,a i := Equiv.sum_comp p a
  simp only [gram]
  rw [hc,ha]

/-- Explicit finite permutations, in lexicographic image order. -/
def permutation : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _,Equiv.swap 1 2,Equiv.swap 0 1,
    (Equiv.swap 1 2).trans (Equiv.swap 0 1),
    (Equiv.swap 0 1).trans (Equiv.swap 1 2),Equiv.swap 0 2]

def literalOrder : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![0,2,1],![1,0,2],![1,2,0],![2,0,1],![2,1,0]]

/-- Kernel-checked exact interpretation of all six literal orderings. -/
theorem permutation_apply : ∀ s : Fin 6,∀ i : Fin 3,
    permutation s i=literalOrder s i := by
  decide +kernel

theorem gram_literal_order (a : Fin 3 → Coefficients) (s : Fin 6) :
    gram (fun i=>a (literalOrder s i))=gram a := by
  simpa only [permutation_apply] using gram_reindex a (permutation s)

/-- Literal 012 ordering of the same signed coefficient triple. -/
theorem gram012 (a b c : Coefficients) :
    gram ![a,b,c]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (0 : Fin 6) i))=(![a,b,c] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (0 : Fin 6)

/-- Literal 021 ordering of the same signed coefficient triple. -/
theorem gram021 (a b c : Coefficients) :
    gram ![a,c,b]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (1 : Fin 6) i))=(![a,c,b] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (1 : Fin 6)

/-- Literal 102 ordering of the same signed coefficient triple. -/
theorem gram102 (a b c : Coefficients) :
    gram ![b,a,c]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (2 : Fin 6) i))=(![b,a,c] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (2 : Fin 6)

/-- Literal 120 ordering of the same signed coefficient triple. -/
theorem gram120 (a b c : Coefficients) :
    gram ![b,c,a]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (3 : Fin 6) i))=(![b,c,a] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (3 : Fin 6)

/-- Literal 201 ordering of the same signed coefficient triple. -/
theorem gram201 (a b c : Coefficients) :
    gram ![c,a,b]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (4 : Fin 6) i))=(![c,a,b] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (4 : Fin 6)

/-- Literal 210 ordering of the same signed coefficient triple. -/
theorem gram210 (a b c : Coefficients) :
    gram ![c,b,a]=gram ![a,b,c] := by
  have hf : (fun i : Fin 3=>(![a,b,c] : Fin 3 → Coefficients)
      (literalOrder (5 : Fin 6) i))=(![c,b,a] : Fin 3 → Coefficients) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hf] using gram_literal_order (![a,b,c] : Fin 3 → Coefficients) (5 : Fin 6)

end BilayerDressed.QuarticIntegerGramPermutation
