import Formalization.FiniteQubitPauliSelection
import Formalization.FinitePureMixedQubitState
import Formalization.PureCoordinateNotTracial

/-!
# Finite pure/mixed coordinate model

This module records the finite Pauli expectation formula and the checked
algebraic direct-limit traciality boundary.  It makes no GNS or factor claim.
-/

namespace StabilizerHyperfinite

open scoped Classical in
theorem qubitPureMixedState_finiteQubitPauliWord_eq_ite
    (pure : ℕ → Bool) (n : ℕ) (label : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure n (finiteQubitPauliWord n label) =
      if finiteQubitPauliSelectedZ pure n label then 1 else 0 := by
  rw [qubitPureMixedState_finiteQubitPauliWord_eq_selectedZIndicator]
  simp [finiteQubitPauliSelectedZIndicator]

theorem qubitPureMixedState_allMixed_isAlgebraicTracialState (n : ℕ) :
    IsAlgebraicTracialState (qubitPureMixedState (fun _ => false) n) := by
  rw [qubitPureMixedState_allMixed]
  exact qubitTensorTrace_isAlgebraicTracialState n

theorem qubitPureMixedState_succ_pure_not_isAlgebraicTracialState
    (pure : ℕ → Bool) (n : ℕ) (h_pure : pure n = true) :
    ¬ IsAlgebraicTracialState (qubitPureMixedState pure (n + 1)) :=
  qubitPureMixedState_succ_not_isAlgebraicTracialState pure n h_pure

theorem qubitPureMixedUHFState_tracial_boundary (pure : ℕ → Bool) :
    IsAlgebraicTracialState (qubitPureMixedUHFState pure) ↔
      ∀ n, pure n = false :=
  qubitPureMixedUHFState_isAlgebraicTracialState_iff pure

end StabilizerHyperfinite
