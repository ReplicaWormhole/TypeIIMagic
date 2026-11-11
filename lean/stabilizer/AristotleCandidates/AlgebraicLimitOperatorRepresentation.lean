import Formalization.AlgebraicLimitStarHom
import Formalization.DyadicTensorTower
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operator representation of the algebraic quasi-local limit

This module is **infrastructure only**: it contains no manuscript claim.

Given

* a directed family `A : ι → Type*` of complex star algebras with compatible
  connecting star-algebra homomorphisms `f i j h : A i →⋆ₐ[ℂ] A j`, and
* a fixed complex Hilbert space `H` together with a family of *stage
  representations* `rho i : A i →⋆ₐ[ℂ] (H →L[ℂ] H)` that are compatible with
  the connecting maps,

we construct the induced star-algebra homomorphism

`algebraicLimitOperatorRep rho compat : DirectLimit A f →⋆ₐ[ℂ] (H →L[ℂ] H)`

from the *algebraic* direct limit into the bounded operators on `H`, and prove

* the finite-stage formula `... (of i x) = rho i x` (both as operators and
  applied to a vector);
* independence of the chosen representative of a limit element;
* uniqueness of a star-algebra map with the prescribed finite-stage values;
* injectivity of the induced limit representation as soon as every stage
  representation is injective (no separate finite-stage separation hypothesis
  is needed: compatibility already forces the connecting maps to be injective,
  and the explicit description of the direct-limit setoid reduces injectivity
  on the limit to injectivity at a single common stage).

The Hilbert space and the stage representations are always *supplied data*:
nothing here constructs an infinite tensor-product Hilbert space, a norm on
the algebraic limit, a C*-completion, or a weak closure.

The final section packages the dyadic specialization to
`StabilizerHyperfinite.QubitTensorPower` / `qubitTensorPowerMap` as a
*conditional* structure `QubitOperatorRepresentationData`: one has to hand in a
Hilbert space and a compatible family of finite-qubit-stage representations,
and one then obtains a representation of the algebraic UHF limit
`QubitUHFAlgebra`.
-/

namespace StabilizerHyperfinite

open scoped ComplexOrder

section General

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The star-algebra homomorphism from the algebraic direct limit into the
bounded operators on `H` induced by a compatible family of stage
representations.

Both the Hilbert space `H` and the stage representations `rho` are supplied
data; `compat` is the explicit compatibility hypothesis with the connecting
maps of the directed system. -/
noncomputable def algebraicLimitOperatorRep
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x) :
    DirectLimit A f →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  algebraicLimitStarAlgHom rho compat

/-- Finite-stage formula: on the image of a stage `i`, the induced limit
representation is the stage representation `rho i`. -/
@[simp]
theorem algebraicLimitOperatorRep_of
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (i : ι) (x : A i) :
    algebraicLimitOperatorRep rho compat
        (DirectLimit.Module.of ℂ ι A f i x) = rho i x :=
  algebraicLimitStarAlgHom_of rho compat i x

/-- Finite-stage formula, evaluated on a vector of the Hilbert space. -/
theorem algebraicLimitOperatorRep_of_apply
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (i : ι) (x : A i) (v : H) :
    algebraicLimitOperatorRep rho compat
        (DirectLimit.Module.of ℂ ι A f i x) v = rho i x v := by
  rw [algebraicLimitOperatorRep_of]

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
/-- Independence of representatives, in the raw form supplied by the
direct-limit setoid: two stage elements that agree after transport to a common
later stage have the same operator. -/
theorem algebraicLimitOperatorRep_stage_congr
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    {i j k : ι} (hik : i ≤ k) (hjk : j ≤ k) {x : A i} {y : A j}
    (hxy : f i k hik x = f j k hjk y) :
    rho i x = rho j y := by
  calc rho i x = rho k (f i k hik x) := (compat i k hik x).symm
    _ = rho k (f j k hjk y) := by rw [hxy]
    _ = rho j y := compat j k hjk y

/-- Independence of representatives: if two stage elements define the same
element of the algebraic direct limit, then their stage representations agree. -/
theorem algebraicLimitOperatorRep_congr_of_eq
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    {i j : ι} {x : A i} {y : A j}
    (hxy : (DirectLimit.Module.of ℂ ι A f i x : DirectLimit A f) =
      DirectLimit.Module.of ℂ ι A f j y) :
    rho i x = rho j y := by
  have := congrArg (algebraicLimitOperatorRep rho compat) hxy
  rwa [algebraicLimitOperatorRep_of, algebraicLimitOperatorRep_of] at this

/-- The induced limit representation is the unique star-algebra map into the
bounded operators with the prescribed finite-stage values. -/
theorem algebraicLimitOperatorRep_unique
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (pi : DirectLimit A f →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h_pi : ∀ i x, pi (DirectLimit.Module.of ℂ ι A f i x) = rho i x) :
    pi = algebraicLimitOperatorRep rho compat :=
  algebraicLimitStarAlgHom_unique rho compat pi h_pi

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
/-- If all stage representations are injective, then compatibility forces the
connecting maps of the directed system to be injective as well.  In particular
no extra finite-stage separation hypothesis has to be assumed for the
injectivity theorem below. -/
theorem connecting_injective_of_stage_rep_injective
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (h_inj : ∀ i, Function.Injective (rho i))
    (i j : ι) (h : i ≤ j) :
    Function.Injective (f i j h) := by
  intro x y hxy
  refine h_inj i ?_
  rw [← compat i j h x, ← compat i j h y, hxy]

/-- **Injectivity of the induced limit representation.**  If every stage
representation `rho i` is injective, then the induced representation of the
algebraic direct limit is injective. -/
theorem algebraicLimitOperatorRep_injective
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (h_inj : ∀ i, Function.Injective (rho i)) :
    Function.Injective (algebraicLimitOperatorRep rho compat) := by
  intro z w hzw
  induction z, w using DirectLimit.induction₂ with
  | _ i x y =>
    have hx : (⟦⟨i, x⟩⟧ : DirectLimit A f) =
        DirectLimit.Module.of ℂ ι A f i x := rfl
    have hy : (⟦⟨i, y⟩⟧ : DirectLimit A f) =
        DirectLimit.Module.of ℂ ι A f i y := rfl
    rw [hx, hy] at hzw ⊢
    rw [algebraicLimitOperatorRep_of, algebraicLimitOperatorRep_of] at hzw
    rw [h_inj i hzw]

/-- The induced limit representation is a star map: it intertwines the
direct-limit involution with the operator adjoint. -/
theorem algebraicLimitOperatorRep_star
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (z : DirectLimit A f) :
    algebraicLimitOperatorRep rho compat (star z) =
      star (algebraicLimitOperatorRep rho compat z) :=
  map_star _ z

/-- The induced limit representation is multiplicative. -/
theorem algebraicLimitOperatorRep_mul
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)
    (z w : DirectLimit A f) :
    algebraicLimitOperatorRep rho compat (z * w) =
      algebraicLimitOperatorRep rho compat z *
        algebraicLimitOperatorRep rho compat w :=
  map_mul _ z w

/-- The induced limit representation is unital. -/
theorem algebraicLimitOperatorRep_one
    (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x) :
    algebraicLimitOperatorRep rho compat 1 = 1 :=
  map_one _

end General

section Dyadic

/-- **Conditional** data for an operator representation of the algebraic
dyadic (UHF) limit `QubitUHFAlgebra`.

Nothing here constructs an infinite tensor-product Hilbert space: both the
Hilbert space `H` and the finite-stage representations `rho n` are supplied
input, subject only to the explicit compatibility condition `compat` with the
canonical inclusions `qubitTensorPowerMap`. -/
structure QubitOperatorRepresentationData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The supplied representation of the `n`-qubit stage algebra. -/
  rho : ∀ n : ℕ, QubitTensorPower n →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- Compatibility with the canonical finite-stage inclusions. -/
  compat : ∀ n m (h : n ≤ m) x, rho m (qubitTensorPowerMap n m h x) = rho n x

namespace QubitOperatorRepresentationData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (D : QubitOperatorRepresentationData H)

/-- The representation of the algebraic UHF limit induced by a compatible
family of finite-qubit-stage representations. -/
noncomputable def limitRep : QubitUHFAlgebra →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  algebraicLimitOperatorRep D.rho D.compat

/-- Finite-stage formula for the induced UHF representation. -/
@[simp]
theorem limitRep_of (n : ℕ) (x : QubitTensorPower n) :
    D.limitRep
        (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
      D.rho n x :=
  algebraicLimitOperatorRep_of D.rho D.compat n x

/-- Finite-stage formula for the induced UHF representation, evaluated on a
vector. -/
theorem limitRep_of_apply (n : ℕ) (x : QubitTensorPower n) (v : H) :
    D.limitRep
        (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) v =
      D.rho n x v := by
  rw [limitRep_of]

/-- Independence of representatives for the induced UHF representation. -/
theorem rho_congr_of_eq {n m : ℕ} {x : QubitTensorPower n} {y : QubitTensorPower m}
    (hxy :
      (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x :
        QubitUHFAlgebra) =
      DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap m y) :
    D.rho n x = D.rho m y :=
  algebraicLimitOperatorRep_congr_of_eq D.rho D.compat hxy

/-- Uniqueness of the induced UHF representation. -/
theorem limitRep_unique (pi : QubitUHFAlgebra →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h_pi : ∀ n x,
      pi (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
        D.rho n x) :
    pi = D.limitRep :=
  algebraicLimitOperatorRep_unique D.rho D.compat pi h_pi

/-- **Conditional faithfulness.**  If every supplied finite-qubit-stage
representation is injective, then the induced representation of the algebraic
UHF limit is injective. -/
theorem limitRep_injective (h_inj : ∀ n, Function.Injective (D.rho n)) :
    Function.Injective D.limitRep :=
  algebraicLimitOperatorRep_injective D.rho D.compat h_inj

end QubitOperatorRepresentationData

end Dyadic

end StabilizerHyperfinite
