import Mathlib

/-!
# Transporting a tracial functional through a star isomorphism

Blueprint: `blueprints/001-tensor-product-trace.tex`, targets TPT-001 and
TPT-002.  This file intentionally proves only the algebraic transport step.
It does not assert any unformalized fact about infinite von Neumann tensor
products, hyperfiniteness, normality, or factor type.
-/

namespace StabilizerHyperfinite

variable {A B : Type*}
  [Semiring A] [StarRing A] [Algebra ℂ A]
  [Semiring B] [StarRing B] [Algebra ℂ B]

/-- A complex-linear functional normalized at the unit and cyclic on products.

This is deliberately an algebraic interface: positivity, normality, and
faithfulness belong to the analytic layer and are not assumed here. -/
structure IsUnitalTracial (tau : A →ₗ[ℂ] ℂ) : Prop where
  map_one : tau 1 = 1
  cyclic : ∀ x y : A, tau (x * y) = tau (y * x)

/-- Algebraic positivity of a complex linear functional: its value on every
square is a nonnegative real number, embedded in `ℂ`.

For a C⋆-algebra this is the usual positivity condition for a functional.  We
keep the statement algebraic here so that trace transport is not tied to an
unavailable von Neumann-algebra API. -/
def IsPositiveFunctional (tau : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ x : A, ∃ r : ℝ, 0 ≤ r ∧ tau (star x * x) = (r : ℂ)

/-- A normalized algebraically positive complex-linear functional. -/
structure IsAlgebraicState (tau : A →ₗ[ℂ] ℂ) : Prop where
  map_one : tau 1 = 1
  positive : IsPositiveFunctional tau

/-- A state which is additionally cyclic on products.  In a C⋆-algebra this
is the algebraic part of a tracial state; normality is a separate topological
property and is deliberately not claimed here. -/
structure IsAlgebraicTracialState (tau : A →ₗ[ℂ] ℂ) : Prop extends
    IsAlgebraicState tau where
  cyclic : ∀ x y : A, tau (x * y) = tau (y * x)

/-- Pull a complex-linear functional back through a star-algebra equivalence. -/
def pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ) : A →ₗ[ℂ] ℂ where
  toFun x := tau (e x)
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp]
theorem pullback_apply (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ) (x : A) :
    pullback e tau x = tau (e x) :=
  rfl

/-- Pulling a functional back along an equivalence and then its inverse gives
the original functional. -/
theorem pullback_symm_pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ) :
    pullback e.symm (pullback e tau) = tau := by
  ext x
  simp [pullback_apply]

/-- Positivity is preserved by pullback along a star-algebra equivalence. -/
theorem isPositiveFunctional_pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ)
    (h_tau : IsPositiveFunctional tau) :
    IsPositiveFunctional (pullback e tau) := by
  intro x
  obtain ⟨r, hr_nonneg, hr_value⟩ := h_tau (e x)
  refine ⟨r, hr_nonneg, ?_⟩
  change tau (e (star x * x)) = (r : ℂ)
  calc
    tau (e (star x * x)) = tau (star (e x) * e x) := by
      congr 1
      calc
        e (star x * x) = e (star x) * e x := e.map_mul (star x) x
        _ = star (e x) * e x := by rw [map_star]
    _ = (r : ℂ) := hr_value

/-- Algebraic states pull back along star-algebra equivalences. -/
theorem isAlgebraicState_pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ)
    (h_tau : IsAlgebraicState tau) :
    IsAlgebraicState (pullback e tau) := by
  constructor
  · simpa using h_tau.map_one
  · exact isPositiveFunctional_pullback e tau h_tau.positive

/-- A unital tracial functional remains unital and tracial after transport
through a `StarAlgEquiv`.

This is the checked algebraic core used by the conditional tensor-product
trace theorem in the blueprint. -/
theorem isUnitalTracial_pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ)
    (h_tau : IsUnitalTracial tau) :
    IsUnitalTracial (pullback e tau) := by
  constructor
  · simpa using h_tau.map_one
  · intro x y
    change tau (e (x * y)) = tau (e (y * x))
    calc
      tau (e (x * y)) = tau (e x * e y) := congrArg tau (e.map_mul x y)
      _ = tau (e y * e x) := h_tau.cyclic (e x) (e y)
      _ = tau (e (y * x)) := (congrArg tau (e.map_mul y x)).symm

/-- An algebraic tracial state pulls back along a star-algebra equivalence.

This is the formal transport step used once a separately proved product-model
isomorphism supplies the target tracial state. -/
theorem isAlgebraicTracialState_pullback (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ)
    (h_tau : IsAlgebraicTracialState tau) :
    IsAlgebraicTracialState (pullback e tau) := by
  refine { toIsAlgebraicState := isAlgebraicState_pullback e tau h_tau.toIsAlgebraicState
           cyclic := ?_ }
  exact (isUnitalTracial_pullback e tau
    ⟨h_tau.map_one, h_tau.cyclic⟩).cyclic

/-- Algebraic traciality is reflected as well as preserved by a star-algebra
equivalence. -/
theorem isAlgebraicTracialState_pullback_iff
    (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ) :
    IsAlgebraicTracialState (pullback e tau) ↔ IsAlgebraicTracialState tau := by
  constructor
  · intro h
    have h_symm := isAlgebraicTracialState_pullback e.symm (pullback e tau) h
    rw [pullback_symm_pullback] at h_symm
    exact h_symm
  · exact isAlgebraicTracialState_pullback e tau

/-- A nontracial functional remains nontracial after pullback along a
star-algebra equivalence. -/
theorem not_isAlgebraicTracialState_pullback
    (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ)
    (h_tau : ¬ IsAlgebraicTracialState tau) :
    ¬ IsAlgebraicTracialState (pullback e tau) := by
  intro h
  exact h_tau (isAlgebraicTracialState_pullback_iff e tau |>.mp h)

/-- The data required to transport a product-model tracial state to a region
algebra.  In the target application, `model` denotes the von Neumann tensor
product of the pure and tracial factors.  The analytic construction of that
model and normality of the equivalence are separate obligations. -/
structure ProductModelTraceData (A : Type*) [Semiring A] [StarRing A]
    [Algebra ℂ A] where
  model : Type*
  modelSemiring : Semiring model
  modelStarRing : StarRing model
  modelAlgebra : Algebra ℂ model
  equivalence : A ≃⋆ₐ[ℂ] model
  trace : model →ₗ[ℂ] ℂ
  trace_is_algebraic_tracial_state : IsAlgebraicTracialState trace

attribute [instance] ProductModelTraceData.modelSemiring
  ProductModelTraceData.modelStarRing ProductModelTraceData.modelAlgebra

namespace ProductModelTraceData

variable {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]

/-- The tracial state induced on the region algebra by the product-model
factorization. -/
noncomputable def inducedTrace (data : ProductModelTraceData A) : A →ₗ[ℂ] ℂ :=
  pullback data.equivalence data.trace

/-- The induced trace is an algebraic tracial state. -/
theorem inducedTrace_isAlgebraicTracialState (data : ProductModelTraceData A) :
    IsAlgebraicTracialState data.inducedTrace :=
  isAlgebraicTracialState_pullback data.equivalence data.trace
    data.trace_is_algebraic_tracial_state

end ProductModelTraceData

end StabilizerHyperfinite
