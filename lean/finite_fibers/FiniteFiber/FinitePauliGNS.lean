import FiniteFiber.FinitePauliStabilizer
import FiniteFiber.FiniteQubitMatrix
import FiniteFiber.GNSVector

/-!
# Finite stabilizer densities in their GNS representation

This finite-dimensional bridge applies the generic GNS-vector construction to
an actual `FinitePauliStabilizerData` density.  It proves stabilizer invariance
of the resulting GNS vector.  It does not construct the countable compatible
state or the regional GNS representation from the manuscript.

Clients that restate its GNS theorem target should open the
`FiniteFiber.FiniteQubitMatrix` and `MatrixOrder` scopes.  The older
`FinitePauliStabilizerData` scope remains available for compatibility.
-/

namespace FiniteFiber

open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace FinitePauliStabilizerData

variable {G : Type*} [Group G] {n : ℕ}

/- The finite matrix algebra carries the operator-norm C-star structure used by GNS. -/
noncomputable scoped instance matrixCStarAlgebra (n : ℕ) :
    CStarAlgebra (Matrix (QubitIndex n) (QubitIndex n) ℂ) :=
  CStarMatrix.instCStarAlgebra

open scoped FiniteFiber.FiniteQubitMatrix

/-- The finite stabilizer density is invariant under every represented stabilizer on the right. -/
theorem stabilizerDensity_mul_representation_right [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.stabilizerDensity * D.representation g = D.stabilizerDensity := by
  rw [D.stabilizerDensity_eq_trace_normalized_projector, smul_mul_assoc,
    D.stabilizerProjector_mul_representation_right]

/-- The finite stabilizer positive functional assigns expectation one to each stabilizer. -/
theorem stabilizerPositiveFunctional_representation_eq_one [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.stabilizerPositiveFunctional (D.representation g) = 1 := by
  change (D.stabilizerDensity * D.representation g).trace = 1
  rw [D.stabilizerDensity_mul_representation_right, D.stabilizerDensity_trace]

/-- Every represented stabilizer has zero squared deviation in its own finite state. -/
theorem stabilizerPositiveFunctional_representation_deviation_eq_zero [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.stabilizerPositiveFunctional
      (star (D.representation g - 1) * (D.representation g - 1)) = 0 := by
  change (D.stabilizerDensity *
    (star (D.representation g - 1) * (D.representation g - 1))).trace = 0
  have hright : D.stabilizerDensity * D.representation g = D.stabilizerDensity :=
    D.stabilizerDensity_mul_representation_right g
  have hself : star (D.representation g) = D.representation g :=
    (D.representation_isSelfAdjoint g).star_eq
  have hmatrix : D.stabilizerDensity *
      (star (D.representation g - 1) * (D.representation g - 1)) = 0 := by
    rw [star_sub, star_one, hself]
    calc
      D.stabilizerDensity *
          ((D.representation g - 1) * (D.representation g - 1)) =
          (D.stabilizerDensity * D.representation g) * D.representation g -
            D.stabilizerDensity * D.representation g -
            D.stabilizerDensity * D.representation g + D.stabilizerDensity := by
              noncomm_ring
      _ = 0 := by
        simp only [hright]
        abel
  rw [hmatrix]
  simp

/-- The canonical GNS vector associated to a finite stabilizer density. -/
noncomputable def stabilizerGNSVector [Fintype G]
    (D : FinitePauliStabilizerData G n) : D.stabilizerPositiveFunctional.GNS :=
  gnsCyclicVector (A := Matrix (QubitIndex n) (QubitIndex n) ℂ)
    D.stabilizerPositiveFunctional

/-- Every finite stabilizer fixes the canonical vector in the GNS representation of its density. -/
theorem gnsStarAlgHom_representation_fixes_gnsCyclicVector [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.stabilizerPositiveFunctional.gnsStarAlgHom (D.representation g)
      D.stabilizerGNSVector = D.stabilizerGNSVector := by
  change D.stabilizerPositiveFunctional.gnsStarAlgHom (D.representation g)
      (gnsCyclicVector (A := Matrix (QubitIndex n) (QubitIndex n) ℂ)
        D.stabilizerPositiveFunctional) =
        gnsCyclicVector (A := Matrix (QubitIndex n) (QubitIndex n) ℂ)
          D.stabilizerPositiveFunctional
  exact gnsStarAlgHom_apply_gnsCyclicVector_eq_of_deviation_eq_zero
    (A := Matrix (QubitIndex n) (QubitIndex n) ℂ)
    D.stabilizerPositiveFunctional (D.representation g)
      (D.stabilizerPositiveFunctional_representation_deviation_eq_zero g)

end FinitePauliStabilizerData

end FiniteFiber
