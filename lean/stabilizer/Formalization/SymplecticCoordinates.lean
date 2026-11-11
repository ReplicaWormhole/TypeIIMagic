import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Finite-word coordinate labels from an adapted symplectic basis

This module isolates the purely linear bridge used in the manuscript's
short-range argument.  An adapted Hamel basis identifies the lattice-label
space with finitely supported coordinate labels.  This is not yet a lift to a
Pauli star algebra: such a lift must also control the Pauli cocycle/phases.
-/

namespace StabilizerHyperfinite

/-- The field of two elements used for Pauli labels. -/
abbrev PauliBit := ZMod 2

/-- A finite-coordinate Pauli word has finitely supported X/Z label data. -/
abbrev PauliCoordinateLabels (I : Type*) := Sum I I →₀ PauliBit

variable {I V : Type*} [AddCommGroup V] [Module PauliBit V]

/-- A Hamel basis whose left and right summands are the chosen Z and X
coordinates.  The symplectic pairing conditions are additional data in the
stabilizer application; this structure records exactly the linear
finite-word consequence of that basis. -/
structure AdaptedPauliCoordinateBasis where
  z : I → V
  x : I → V
  basis : Module.Basis (Sum I I) PauliBit V
  basis_z : ∀ i, basis (Sum.inl i) = z i
  basis_x : ∀ i, basis (Sum.inr i) = x i

namespace AdaptedPauliCoordinateBasis

/-- The coordinate-label equivalence supplied by the adapted Hamel basis. -/
noncomputable def coordinateLabelEquiv (data : AdaptedPauliCoordinateBasis (I := I) (V := V)) :
    PauliCoordinateLabels I ≃ₗ[PauliBit] V :=
  data.basis.repr.symm

/-- A single Z-coordinate label maps to the selected Z basis vector. -/
theorem coordinateLabelEquiv_z
    (data : AdaptedPauliCoordinateBasis (I := I) (V := V)) (i : I) :
    data.coordinateLabelEquiv (Finsupp.single (Sum.inl i) 1) = data.z i := by
  change data.basis.repr.symm (Finsupp.single (Sum.inl i) 1) = data.z i
  calc
    data.basis.repr.symm (Finsupp.single (Sum.inl i) 1) =
        data.basis.repr.symm (data.basis.repr (data.basis (Sum.inl i))) := by
          rw [data.basis.repr_self]
    _ = data.basis (Sum.inl i) := data.basis.repr.symm_apply_apply _
    _ = data.z i := data.basis_z i

/-- A single X-coordinate label maps to the selected X basis vector. -/
theorem coordinateLabelEquiv_x
    (data : AdaptedPauliCoordinateBasis (I := I) (V := V)) (i : I) :
    data.coordinateLabelEquiv (Finsupp.single (Sum.inr i) 1) = data.x i := by
  change data.basis.repr.symm (Finsupp.single (Sum.inr i) 1) = data.x i
  calc
    data.basis.repr.symm (Finsupp.single (Sum.inr i) 1) =
        data.basis.repr.symm (data.basis.repr (data.basis (Sum.inr i))) := by
          rw [data.basis.repr_self]
    _ = data.basis (Sum.inr i) := data.basis.repr.symm_apply_apply _
    _ = data.x i := data.basis_x i

/-- Every lattice label has a finite coordinate-word representative. -/
theorem coordinateLabelEquiv_surjective
    (data : AdaptedPauliCoordinateBasis (I := I) (V := V)) :
    Function.Surjective data.coordinateLabelEquiv :=
  data.coordinateLabelEquiv.surjective

/-- The inverse coordinate map is exactly the finite-support coefficient
function of the selected Hamel basis. -/
theorem coordinateLabelEquiv_symm_apply
    (data : AdaptedPauliCoordinateBasis (I := I) (V := V)) (v : V) :
    data.coordinateLabelEquiv.symm v = data.basis.repr v :=
  rfl

end AdaptedPauliCoordinateBasis

end StabilizerHyperfinite
