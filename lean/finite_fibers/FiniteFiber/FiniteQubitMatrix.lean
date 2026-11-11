import FiniteFiber.FinitePauli
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Operator-norm C-star structure for finite qubit matrices

This neutral scope exposes the operator-norm C-star structure on the finite
matrix algebras used throughout the finite-volume construction.  Tensor-chain
clients should open `FiniteFiber.FiniteQubitMatrix`, rather than depending on
the stabilizer-GNS namespace solely to obtain a norm.
-/

namespace FiniteFiber

open scoped ComplexOrder

namespace FiniteQubitMatrix

/-- The finite qubit matrix algebra carries its operator-norm C-star structure. -/
noncomputable scoped instance cStarAlgebra (n : ℕ) :
    CStarAlgebra (Matrix (QubitIndex n) (QubitIndex n) ℂ) :=
  CStarMatrix.instCStarAlgebra

end FiniteQubitMatrix

end FiniteFiber
