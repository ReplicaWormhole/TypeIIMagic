import AristotleCandidates.FiniteStabilizerProjector
import AristotleCandidates.FiniteDensityMatrix

/-!
# Traces of the finite stabilizer group-average projector on a qubit stage

Let `G` be a finite group and `U : G →* QubitTensorPower n` a multiplicative
map into the concrete finite qubit stage.  Assume the *conditional* hypothesis
that every nonidentity group element has vanishing normalized qubit trace,

    qubitTensorTrace n (U g) = 0   for `g ≠ 1`.

Then the group average `P = |G|⁻¹ • ∑ g, U g` satisfies

* `qubitTensorTrace n P = (|G| : ℂ)⁻¹`  (normalized trace), and
* `qubitTensorFullTrace n P = 2 ^ n * (|G| : ℂ)⁻¹`  (ordinary matrix trace).

The dimension factor `2 ^ n` appears explicitly; the exchange between the two
traces is made only through
`qubitTensorTrace_eq_smul_qubitTensorFullTrace`.

Everything here is conditional on the vanishing-trace hypothesis.  Nothing is
claimed about `U` being a Pauli realization, and no C⋆, von Neumann,
hyperfinite, GNS, factor, or rank statement is made.
-/

namespace AristotleCandidates

open StabilizerHyperfinite

section QubitStage

/-- Each finite qubit stage is a ring: it is a complex algebra, so additive
inverses are supplied by scalar multiplication by `-1`.  The underlying
semiring is the one already carried by the tower. -/
noncomputable local instance qubitTensorPowerRing (n : ℕ) : Ring (QubitTensorPower n) :=
  Algebra.semiringToRing ℂ

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-- The normalized finite-stage trace is unital. -/
theorem qubitTensorTrace_one (n : ℕ) :
    qubitTensorTrace n (1 : QubitTensorPower n) = 1 :=
  (qubitTensorTrace_isAlgebraicTracialState n).toIsAlgebraicState.map_one

/-- **Normalized trace of the finite stabilizer projector.**  If every
nonidentity element of the finite group `G` has vanishing normalized qubit
trace, then the group average has normalized trace `|G|⁻¹`. -/
theorem qubitTensorTrace_groupAverage (U : G →* QubitTensorPower n)
    (hU : ∀ g : G, g ≠ 1 → qubitTensorTrace n (U g) = 0) :
    qubitTensorTrace n (groupAverage U) = ((Fintype.card G : ℂ))⁻¹ :=
  groupAverage_trace U (qubitTensorTrace n) (qubitTensorTrace_one n) hU

/-- **Ordinary trace of the finite stabilizer projector.**  Under the same
vanishing-trace hypothesis, the ordinary (unnormalized) matrix trace of the
group average on the `n`-qubit stage is `2 ^ n * |G|⁻¹`, the dimension factor
being explicit. -/
theorem qubitTensorFullTrace_groupAverage (U : G →* QubitTensorPower n)
    (hU : ∀ g : G, g ≠ 1 → qubitTensorTrace n (U g) = 0) :
    qubitTensorFullTrace n (groupAverage U) =
      (2 : ℂ) ^ n * ((Fintype.card G : ℂ))⁻¹ := by
  have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have hnorm := qubitTensorTrace_groupAverage U hU
  rw [qubitTensorTrace_eq_smul_qubitTensorFullTrace] at hnorm
  field_simp at hnorm ⊢
  linear_combination hnorm

end QubitStage

end AristotleCandidates
