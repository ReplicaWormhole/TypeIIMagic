import FiniteFiber.FiniteNestedPauli
import FiniteFiber.FiniteTensorMatrixChain

/-!
# Compatible finite stabilizer states along a tensor inclusion

`NestedFinitePauliStabilizerData` already proves equality of the smaller
density matrix with the right partial trace of the larger one.  This file
combines that fact with the trace/partial-trace adjointness theorem to obtain
the corresponding equality of finite-volume state functionals.

The result is still finite-dimensional: it does not construct a countable
quasilocal C-star algebra or its GNS representation.  It is the exact
compatibility datum required by that next construction.

The initial-segment adapter below eliminates one formerly supplied piece of
data: once the larger stabilizer representation is expressed by its literal
`Fin (n + m)` Pauli labels, its tensor decomposition in the physical
coordinates is derived from `FiniteTensorMatrixChain`.
-/

namespace FiniteFiber

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker
open scoped FiniteFiber.FiniteQubitMatrix

/--
Actual nested finite stabilizer data written directly in the literal
initial/final `Fin` coordinates.  The matrix tensor decomposition is not an
assumption: it is derived from the finite Pauli-string factorization theorem.

The inclusion and survivor condition remain explicit because they encode the
global local-stabilizer-group fact that tracing out the final block retains
exactly the smaller local group.
-/
structure InitialSegmentNestedFinitePauliStabilizerData
    (G H : Type*) [Group G] [Group H] (n m : ℕ) where
  /-- The actual stabilizer data on the `n + m` qubit region. -/
  large : FinitePauliStabilizerData G (n + m)
  /-- The actual stabilizer data on the retained `n` qubit region. -/
  small : FinitePauliStabilizerData H n
  /-- The inclusion of the smaller local stabilizer group into the larger one. -/
  inclusion : H →* G
  /-- The inclusion is an actual subgroup embedding. -/
  inclusion_injective : Function.Injective inclusion
  /-- A term is identity on the final block exactly when it comes from the smaller group. -/
  survivor_iff : ∀ g : G,
    IsIdentityPauliString (fun j : Fin m => large.labels g (Fin.natAdd n j)) ↔
      ∃ h : H, inclusion h = g
  /-- Inclusion preserves the Hermitian Pauli sign. -/
  negative_compat : ∀ h : H,
    large.negative (inclusion h) = small.negative h
  /-- Inclusion preserves the labels on the retained initial block. -/
  left_compat : ∀ h : H,
    (fun i : Fin n => large.labels (inclusion h) (Fin.castAdd m i)) = small.labels h

namespace InitialSegmentNestedFinitePauliStabilizerData

variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/--
The literal-coordinate data instantiate the general nested stabilizer
contract.  Its `large_decomposes` clause is discharged by the checked Pauli
matrix factorization, rather than being supplied separately.
-/
noncomputable def toNestedFinitePauliStabilizerData
    (D : InitialSegmentNestedFinitePauliStabilizerData G H n m) :
    NestedFinitePauliStabilizerData G H n m where
  large := D.large
  small := D.small
  coordinateEquiv := qubitIndexInitialSegmentEquiv n m
  negative := D.large.negative
  left := fun g i => D.large.labels g (Fin.castAdd m i)
  right := fun g j => D.large.labels g (Fin.natAdd n j)
  large_decomposes := by
    intro g
    rw [D.large.representation_eq]
    exact signedPauliStringMatrix_reindex_initialSegment n m _ _
  inclusion := D.inclusion
  inclusion_injective := D.inclusion_injective
  survivor_iff := D.survivor_iff
  negative_compat := D.negative_compat
  left_compat := D.left_compat

/--
The actual finite stabilizer densities of literal-coordinate nested data obey
the manuscript's partial-trace compatibility equation.
-/
theorem partialTrace_reindexedLargeDensity_eq_smallDensity
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : InitialSegmentNestedFinitePauliStabilizerData G H n m) :
    partialTraceRight D.toNestedFinitePauliStabilizerData.reindexedLargeDensity =
      D.small.stabilizerDensity := by
  exact D.toNestedFinitePauliStabilizerData.partialTrace_reindexedLargeDensity_eq_smallDensity

/--
The resulting finite stabilizer states agree under the physical
initial-segment matrix embedding.
-/
theorem stabilizerStateFunctional_embedInitialSegment
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : InitialSegmentNestedFinitePauliStabilizerData G H n m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    D.large.stabilizerStateFunctional (embedInitialSegment n m A) =
      D.small.stabilizerStateFunctional A := by
  change (D.large.stabilizerDensity * embedInitialSegment n m A).trace =
    (D.small.stabilizerDensity * A).trace
  rw [trace_mul_embedInitialSegment_eq_trace_partialTraceRight_reindex]
  change (partialTraceRight D.toNestedFinitePauliStabilizerData.reindexedLargeDensity * A).trace =
    (D.small.stabilizerDensity * A).trace
  rw [D.partialTrace_reindexedLargeDensity_eq_smallDensity]

end InitialSegmentNestedFinitePauliStabilizerData

namespace NestedFinitePauliStabilizerData

variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/--
The state defined by the larger stabilizer density agrees with the smaller
state on every observable embedded as `A tensor 1` in the chosen coordinates.
-/
theorem stabilizerStateFunctional_coordinateEmbedRight
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    D.large.stabilizerStateFunctional
      (coordinateEmbedRight (QubitIndex n) (QubitIndex m) (QubitIndex (n + m))
        D.coordinateEquiv A) =
      D.small.stabilizerStateFunctional A := by
  change (D.large.stabilizerDensity *
    coordinateEmbedRight (QubitIndex n) (QubitIndex m) (QubitIndex (n + m))
      D.coordinateEquiv A).trace =
    (D.small.stabilizerDensity * A).trace
  rw [trace_mul_coordinateEmbedRight_eq_trace_partialTraceRight_reindex]
  change (partialTraceRight D.reindexedLargeDensity * A).trace =
    (D.small.stabilizerDensity * A).trace
  rw [D.partialTrace_reindexedLargeDensity_eq_smallDensity]

/--
When the supplied nested data use the literal initial/final `Fin` split, the
pairwise compatible state relation is expressed by `embedInitialSegment`.
This remains a one-inclusion statement; no coherent directed system is claimed
here.
-/
theorem stabilizerStateFunctional_embedInitialSegment
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m)
    (hcoordinate : D.coordinateEquiv = qubitIndexInitialSegmentEquiv n m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    D.large.stabilizerStateFunctional (embedInitialSegment n m A) =
      D.small.stabilizerStateFunctional A := by
  simpa [embedInitialSegment, hcoordinate] using
    D.stabilizerStateFunctional_coordinateEmbedRight A

end NestedFinitePauliStabilizerData

end FiniteFiber
