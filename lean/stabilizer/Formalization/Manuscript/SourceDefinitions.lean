/-!
# Manuscript source boundary

**Source basis:** `main.tex:1671-1679`.

This module intentionally introduces no replacement Lean definition for the
manuscript's infinite local symplectic-basis data. The project does not yet
contain a faithful model of that data. Downstream modules must state any
concrete model as an auxiliary assumption.

No gLU, refinement, or layer-coherence hypothesis is introduced here.
-/

namespace StabilizerHyperfinite.Manuscript

/-- Marker for modules governed by the manuscript-only source contract. -/
def sourceContractVersion : String := "main.tex:1671-1679, 1740-1752"

end StabilizerHyperfinite.Manuscript
