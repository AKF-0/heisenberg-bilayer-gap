import Dressed.QuarticIntegerRowValidity

/-! Bounded literal row checks compose without changing the certified condition.
Every row and every inter-chunk boundary is retained. Endpoint certificates can
be propagated along a balanced append tree without rechecking a long prefix.
The final raw-list equality and exact array length remain explicit premises.
-/
namespace BilayerDressed.QuarticIntegerRowChunks
open QuarticRootedRowTable
set_option maxHeartbeats 800000

/-- The unchanged validity and adjacent-code conditions for one literal chunk. -/
structure CheckedChunk (A : ℕ) (xs : List Row) : Prop where
  valid : xs.all (fun r=>decide (Valid A r))=true
  chain : List.IsChain (fun r s=>code A r<code A s) xs

/-- Empty chunks are permitted and introduce no hidden boundary comparison. -/
theorem CheckedChunk.nil (A : ℕ) : CheckedChunk A [] :=
  ⟨rfl,List.IsChain.nil⟩

/-- Exact append composition. The one displayed boundary condition is required
in addition to both internal chain certificates. -/
theorem CheckedChunk.append {A : ℕ} {xs ys : List Row}
    (hx : CheckedChunk A xs) (hy : CheckedChunk A ys)
    (hboundary : ∀ r ∈ xs.getLast?,∀ s ∈ ys.head?,code A r<code A s) :
    CheckedChunk A (xs++ys) := by
  constructor
  · simp only [List.all_append,hx.valid,hy.valid,Bool.and_self]
  · exact hx.chain.append hy.chain hboundary

/-- Two concrete endpoint identities reduce the boundary check to one exact
integer comparison. No whole-prefix traversal is part of this implication. -/
theorem CheckedChunk.append_of_endpoints {A : ℕ} {xs ys : List Row}
    (hx : CheckedChunk A xs) (hy : CheckedChunk A ys) (r s : Row)
    (hlast : xs.getLast?=some r) (hhead : ys.head?=some s)
    (hlt : code A r<code A s) : CheckedChunk A (xs++ys) := by
  apply hx.append hy
  simpa only [hlast,hhead,Option.mem_some_iff,forall_eq'] using hlt

/-- A nonempty chunk with cached, proved endpoints. These endpoint identities
are carried by proofs rather than recomputed on each growing concatenation. -/
structure EndpointChunk (A : ℕ) (first last : Row) (xs : List Row) : Prop where
  checked : CheckedChunk A xs
  head_eq : xs.head?=some first
  last_eq : xs.getLast?=some last

/-- Endpoint-aware composition can be used in any parenthesization, including
a balanced tree of bounded numerical checks. -/
theorem EndpointChunk.append {A : ℕ} {first middleLeft middleRight last : Row}
    {xs ys : List Row} (hx : EndpointChunk A first middleLeft xs)
    (hy : EndpointChunk A middleRight last ys)
    (hboundary : code A middleLeft<code A middleRight) :
    EndpointChunk A first last (xs++ys) := by
  constructor
  · exact hx.checked.append_of_endpoints hy.checked middleLeft middleRight
      hx.last_eq hy.head_eq hboundary
  · simp only [List.head?_append,hx.head_eq,Option.some_or]
  · simp only [List.getLast?_append,hy.last_eq,Option.some_or]

/-- Composition results provide exactly the frozen row-validity and StrictMono
inputs. Completeness still requires the separate exact binomial row count. -/
theorem hypotheses_of_chunk {A R : ℕ} (raw : Array Row) (hsize : raw.size=R)
    (xs : List Row) (hraw : raw.toList=xs) (hc : CheckedChunk A xs) :
    (∀ i : Fin R,Valid A (row raw i)) ∧
      StrictMono (fun i : Fin R=>code A (row raw i)) := by
  apply QuarticIntegerRowValidity.hypotheses_of_linear_checks raw hsize
  · simpa only [hraw] using hc.valid
  · simpa only [hraw] using hc.chain

theorem hypotheses_of_endpointChunk {A R : ℕ} (raw : Array Row) (hsize : raw.size=R)
    (xs : List Row) (hraw : raw.toList=xs) (first last : Row)
    (hc : EndpointChunk A first last xs) :
    (∀ i : Fin R,Valid A (row raw i)) ∧
      StrictMono (fun i : Fin R=>code A (row raw i)) :=
  hypotheses_of_chunk raw hsize xs hraw hc.checked

end BilayerDressed.QuarticIntegerRowChunks
