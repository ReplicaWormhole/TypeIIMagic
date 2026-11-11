/-
# Conditional theorem contract

**Source basis:** `main.tex:1740-1752`, with proposed proof steps at
`main.tex:1915-2004`.

This file intentionally does not declare the manuscript theorem as proved.
Before it can be stated faithfully in Lean, the project needs an actual model
of the infinite Pauli/regional algebra, the asserted star isomorphism,
product-GNS/spatial-tensor data, and the relevant von Neumann classification
assumptions. `SOURCE-CONTRACT.md` records those prerequisites.

The imports provide the currently checked finite, algebraic, conditional-GNS,
and trace-obstruction components in their intended dependency order.
-/

import Formalization.Manuscript.SourceDefinitions
import Formalization.Manuscript.FiniteModel
import Formalization.Manuscript.AlgebraicLimit
import Formalization.Manuscript.ProductState
import Formalization.Manuscript.GNSBridge
import Formalization.Manuscript.TraceDichotomy
import AristotleCandidates.InfiniteAlgebraicRegionalEquiv
import AristotleCandidates.InfiniteAlgebraicStateTransport
import AristotleCandidates.CStarCompletionAlphaInterface
import AristotleCandidates.CStarAlphaGNSBridge
import AristotleCandidates.CStarInductiveLimitFeasibility
import AristotleCandidates.FiniteCoordinateMapNormControl

namespace StabilizerHyperfinite.Manuscript

/-- Status marker only: no theorem claim is encoded by this declaration. -/
def regionalAlgebraTheoremStatus : String :=
  "conditional contract pending analytic model"

end StabilizerHyperfinite.Manuscript
