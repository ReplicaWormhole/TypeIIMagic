import Formalization.FiniteTensorTrace
import Formalization.TensorMatrixEquiv

/-!
# A conditional finite coordinate factorization interface

Context: this file is *Lean infrastructure plus an explicitly labelled
auxiliary assumption*.  It formalizes only a finite algebraic analogue of the
type-I/core split: the factorization is **supplied as data**, namely as a
complex star-algebra equivalence

```
h_factorization : A ≃⋆ₐ[ℂ] (Matrix pure pure ℂ ⊗[ℂ] Matrix core core ℂ)
```

from the finite product model onto the algebra under study.  Everything proved
here is conditional on that hypothesis.

What is proved: the already-checked product tracial functional
`StabilizerHyperfinite.finiteTensorTrace` transports through the supplied
equivalence to an algebraic tracial state on `A`, and on elementary tensors it
is the product of the two normalized matrix traces.

What is **not** claimed: nothing here asserts the manuscript's von Neumann
algebra theorem.  There is no infinite spatial von Neumann tensor product, no
C⋆ or weak closure, no gLU or refinement data, no hyperfiniteness, no GNS
construction, and no normality statement.  Both factors are finite matrix
algebras, the tensor product is the purely algebraic one over `ℂ`, and the
existence of the factorization is an assumption, not a conclusion.
-/

namespace AristotleCandidates

open scoped TensorProduct
open StabilizerHyperfinite

variable {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
variable (pure core : Type*)
  [Fintype pure] [DecidableEq pure]
  [Fintype core] [DecidableEq core]

/-- The finite coordinate product model: a finite pure matrix factor tensored
algebraically over `ℂ` with a finite core matrix factor. -/
abbrev FiniteCoordinateModel : Type _ :=
  Matrix pure pure ℂ ⊗[ℂ] Matrix core core ℂ

/-- The functional induced on `A` by a supplied finite coordinate
factorization: the product normalized trace of the finite model, pulled back
along the assumed star-algebra equivalence. -/
noncomputable def finiteCoordinateTrace
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core) :
    A →ₗ[ℂ] ℂ :=
  pullback h_factorization (finiteTensorTrace pure core)

@[simp]
theorem finiteCoordinateTrace_apply
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core) (x : A) :
    finiteCoordinateTrace pure core h_factorization x =
      finiteTensorTrace pure core (h_factorization x) :=
  rfl

/-- Conditional on the supplied finite factorization, the transported product
trace is an algebraic tracial state on `A`. -/
theorem finiteCoordinateTrace_isAlgebraicTracialState [Nonempty pure] [Nonempty core]
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core) :
    IsAlgebraicTracialState (finiteCoordinateTrace pure core h_factorization) :=
  isAlgebraicTracialState_pullback h_factorization (finiteTensorTrace pure core)
    (finiteTensorTrace_isAlgebraicTracialState pure core)

/-- The elementary-tensor formula: on the element of `A` corresponding to
`a ⊗ₜ b`, the induced functional is the product of the normalized matrix trace
of the pure factor and the normalized matrix trace of the core factor. -/
theorem finiteCoordinateTrace_symm_tmul
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core)
    (a : Matrix pure pure ℂ) (b : Matrix core core ℂ) :
    finiteCoordinateTrace pure core h_factorization
        (h_factorization.symm (a ⊗ₜ[ℂ] b)) =
      normalizedMatrixTrace pure a * normalizedMatrixTrace core b := by
  rw [finiteCoordinateTrace_apply, StarAlgEquiv.apply_symm_apply,
    finiteTensorTrace_tmul]

/-- Adjoining the core unit does not change the value of the induced
functional on the pure factor. -/
theorem finiteCoordinateTrace_symm_tmul_one [Nonempty core]
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core)
    (a : Matrix pure pure ℂ) :
    finiteCoordinateTrace pure core h_factorization
        (h_factorization.symm (a ⊗ₜ[ℂ] (1 : Matrix core core ℂ))) =
      normalizedMatrixTrace pure a := by
  rw [finiteCoordinateTrace_symm_tmul, normalizedMatrixTrace_one, mul_one]

/-- Adjoining the pure unit does not change the value of the induced
functional on the core factor. -/
theorem finiteCoordinateTrace_symm_one_tmul [Nonempty pure]
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core)
    (b : Matrix core core ℂ) :
    finiteCoordinateTrace pure core h_factorization
        (h_factorization.symm ((1 : Matrix pure pure ℂ) ⊗ₜ[ℂ] b)) =
      normalizedMatrixTrace core b := by
  rw [finiteCoordinateTrace_symm_tmul, normalizedMatrixTrace_one, one_mul]

/-- **Conditional finite coordinate factorization theorem.**

If the algebra `A` is *assumed* to be star-isomorphic over `ℂ` to a finite pure
matrix factor tensored with a finite core matrix factor, then `A` carries an
algebraic tracial state whose value on elementary tensors is the product of the
two normalized matrix traces.

This is a statement about the supplied finite factorization
`h_factorization` only.  It asserts nothing about an infinite spatial von
Neumann tensor product, and it is not the manuscript's von Neumann algebra
theorem. -/
theorem exists_algebraicTracialState_of_finiteCoordinateFactorization
    [Nonempty pure] [Nonempty core]
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core) :
    ∃ tau : A →ₗ[ℂ] ℂ, IsAlgebraicTracialState tau ∧
      ∀ (a : Matrix pure pure ℂ) (b : Matrix core core ℂ),
        tau (h_factorization.symm (a ⊗ₜ[ℂ] b)) =
          normalizedMatrixTrace pure a * normalizedMatrixTrace core b :=
  ⟨finiteCoordinateTrace pure core h_factorization,
    finiteCoordinateTrace_isAlgebraicTracialState pure core h_factorization,
    finiteCoordinateTrace_symm_tmul pure core h_factorization⟩

/-!
## Compatibility with the matrix-amplification coordinates

The same finite model can be presented in amplified coordinates, as matrices
over the core factor.  The two descriptions of the product trace agree.
-/

/-- The finite type-I amplification trace built from the normalized trace of
the core factor coincides with the product trace of the two finite factors. -/
theorem finiteTypeITensorTrace_eq_finiteTensorTrace :
    finiteTypeITensorTrace pure (normalizedMatrixTrace core) =
      finiteTensorTrace pure core := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [finiteTypeITensorTrace_tmul pure (normalizedMatrixTrace core)
        (normalizedMatrixTrace_cyclic core) a b,
      finiteTensorTrace_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Amplified form of the induced functional: after composing the supplied
factorization with the canonical identification of the finite model with
matrices over the core factor, the induced functional is the normalized
matrix amplification of the core normalized trace. -/
theorem finiteCoordinateTrace_eq_matrixAmplificationInducedTrace
    (h_factorization : A ≃⋆ₐ[ℂ] FiniteCoordinateModel pure core) :
    finiteCoordinateTrace pure core h_factorization =
      matrixAmplificationInducedTrace pure
        (h_factorization.trans (matrixTensorStarAlgEquiv pure))
        (normalizedMatrixTrace core) := by
  ext x
  rw [finiteCoordinateTrace_apply, ← finiteTypeITensorTrace_eq_finiteTensorTrace]
  rfl

end AristotleCandidates
