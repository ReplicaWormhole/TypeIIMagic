import Formalization.AlgebraicInductiveTrace

/-!
# Star and positivity on an algebraic direct limit

Mathlib's directed algebraic direct limit supplies ring and module structure
but not a star structure.  This file constructs the star induced by compatible
stagewise star-algebra maps and uses it to transport positivity of a compatible
family of finite-stage traces.
-/

namespace StabilizerHyperfinite

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]

/-- The involution on a directed algebraic limit, defined on a representative
by taking its stagewise involution. -/
noncomputable def algebraicLimitStar : DirectLimit A f → DirectLimit A f :=
  DirectLimit.lift f
    (fun i x => (⟦⟨i, star x⟩⟧ : DirectLimit A f))
    (by
      intro i j h x
      calc
        (⟦⟨i, star x⟩⟧ : DirectLimit A f) =
            ⟦⟨j, f i j h (star x)⟩⟧ :=
          DirectLimit.eq_of_le ⟨i, star x⟩ j h
        _ = ⟦⟨j, star (f i j h x)⟩⟧ := by rw [map_star])

noncomputable instance : Star (DirectLimit A f) := ⟨algebraicLimitStar⟩

/-- The scalar action already supplied by the directed module limit is
compatible with multiplication, so the algebraic limit is a complex algebra. -/
noncomputable instance : Algebra ℂ (DirectLimit A f) :=
  Algebra.ofModule
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y =>
        change (c • (⟦⟨i, x⟩⟧ : DirectLimit A f)) * ⟦⟨i, y⟩⟧ =
          c • ((⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, y⟩⟧)
        rw [DirectLimit.smul_def, DirectLimit.mul_def, DirectLimit.mul_def,
          DirectLimit.smul_def]
        exact congrArg (fun z => (⟦⟨i, z⟩⟧ : DirectLimit A f)) (smul_mul_assoc c x y))
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y =>
        change (⟦⟨i, x⟩⟧ : DirectLimit A f) * (c • ⟦⟨i, y⟩⟧) =
          c • ((⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, y⟩⟧)
        rw [DirectLimit.smul_def, DirectLimit.mul_def, DirectLimit.mul_def,
          DirectLimit.smul_def]
        exact congrArg (fun z => (⟦⟨i, z⟩⟧ : DirectLimit A f)) (Algebra.mul_smul_comm c x y))

@[simp]
theorem star_of (i : ι) (x : A i) :
    star (DirectLimit.Module.of ℂ ι A f i x) =
      DirectLimit.Module.of ℂ ι A f i (star x) :=
  rfl

/-- The induced direct-limit star is involutive. -/
theorem algebraicLimit_star_star (z : DirectLimit A f) : star (star z) = z := by
  induction z using DirectLimit.induction with
  | _ i x =>
    change star (star (DirectLimit.Module.of ℂ ι A f i x)) =
      DirectLimit.Module.of ℂ ι A f i x
    rw [star_of, star_of, star_star]

/-- The induced direct-limit star reverses multiplication. -/
theorem algebraicLimit_star_mul (x y : DirectLimit A f) : star (x * y) = star y * star x := by
  induction x, y using DirectLimit.induction₂ with
  | _ i x y =>
    change star ((⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, y⟩⟧) =
      star (⟦⟨i, y⟩⟧ : DirectLimit A f) * star (⟦⟨i, x⟩⟧)
    rw [DirectLimit.mul_def]
    change star (DirectLimit.Module.of ℂ ι A f i (x * y)) =
      star (DirectLimit.Module.of ℂ ι A f i y) * star (DirectLimit.Module.of ℂ ι A f i x)
    rw [star_of, star_of, star_of]
    change (⟦⟨i, star (x * y)⟩⟧ : DirectLimit A f) =
      ⟦⟨i, star y⟩⟧ * ⟦⟨i, star x⟩⟧
    rw [DirectLimit.mul_def]
    exact congrArg (fun z => (⟦⟨i, z⟩⟧ : DirectLimit A f)) (star_mul x y)

/-- The induced direct-limit star preserves addition. -/
theorem algebraicLimit_star_add (x y : DirectLimit A f) : star (x + y) = star x + star y := by
  induction x, y using DirectLimit.induction₂ with
  | _ i x y =>
    change star ((⟦⟨i, x⟩⟧ : DirectLimit A f) + ⟦⟨i, y⟩⟧) =
      star (⟦⟨i, x⟩⟧ : DirectLimit A f) + star (⟦⟨i, y⟩⟧ : DirectLimit A f)
    rw [DirectLimit.add_def]
    change star (DirectLimit.Module.of ℂ ι A f i (x + y)) =
      star (DirectLimit.Module.of ℂ ι A f i x) + star (DirectLimit.Module.of ℂ ι A f i y)
    rw [star_of, star_of, star_of]
    change (⟦⟨i, star (x + y)⟩⟧ : DirectLimit A f) =
      ⟦⟨i, star x⟩⟧ + ⟦⟨i, star y⟩⟧
    rw [DirectLimit.add_def]
    exact congrArg (fun z => (⟦⟨i, z⟩⟧ : DirectLimit A f)) (star_add x y)

/-- The direct-limit involution is an involutive star operation. -/
noncomputable instance : InvolutiveStar (DirectLimit A f) where
  star_involutive := algebraicLimit_star_star

/-- The direct-limit involution preserves addition. -/
noncomputable instance : StarAddMonoid (DirectLimit A f) where
  star_add := algebraicLimit_star_add

/-- The direct-limit involution reverses multiplication. -/
noncomputable instance : StarMul (DirectLimit A f) where
  star_mul := algebraicLimit_star_mul

/-- Together with the existing semiring structure, the direct-limit star gives
a star ring. -/
noncomputable instance : StarRing (DirectLimit A f) where
  star_add := algebraicLimit_star_add

section StarModule

variable [∀ i, StarModule ℂ (A i)]

/-- The induced direct-limit involution is compatible with complex scalar
multiplication whenever each finite stage is a complex star module. -/
theorem algebraicLimit_star_smul (c : ℂ) (z : DirectLimit A f) :
    star (c • z) = star c • star z := by
  induction z using DirectLimit.induction with
  | _ i x =>
    change star (c • (⟦⟨i, x⟩⟧ : DirectLimit A f)) =
      star c • star (⟦⟨i, x⟩⟧ : DirectLimit A f)
    rw [DirectLimit.smul_def]
    change star (DirectLimit.Module.of ℂ ι A f i (c • x)) =
      star c • star (DirectLimit.Module.of ℂ ι A f i x)
    rw [star_of, star_of]
    change (⟦⟨i, star (c • x)⟩⟧ : DirectLimit A f) =
      star c • (⟦⟨i, star x⟩⟧ : DirectLimit A f)
    rw [DirectLimit.smul_def]
    exact congrArg (fun y => (⟦⟨i, y⟩⟧ : DirectLimit A f)) (star_smul c x)

/-- The algebraic direct limit of complex star modules is again a complex star
module. -/
noncomputable instance : StarModule ℂ (DirectLimit A f) where
  star_smul := algebraicLimit_star_smul

end StarModule

/-- A compatible system of positive stage functionals is positive on the
algebraic direct limit. -/
theorem algebraicLimitTrace_positive (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (h_positive : ∀ i, IsPositiveFunctional (tau i)) :
    IsPositiveFunctional (algebraicLimitTrace tau compatible) := by
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
    obtain ⟨r, hr_nonneg, hr_value⟩ := h_positive i x
    refine ⟨r, hr_nonneg, ?_⟩
    change algebraicLimitTrace tau compatible
        (star (⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, x⟩⟧) = (r : ℂ)
    change algebraicLimitTrace tau compatible
        (star (DirectLimit.Module.of ℂ ι A f i x) *
          DirectLimit.Module.of ℂ ι A f i x) = (r : ℂ)
    rw [star_of]
    change algebraicLimitTrace tau compatible
        ((⟦⟨i, star x⟩⟧ : DirectLimit A f) * ⟦⟨i, x⟩⟧) = (r : ℂ)
    rw [DirectLimit.mul_def]
    change algebraicLimitTrace tau compatible
        (DirectLimit.Module.of ℂ ι A f i (star x * x)) = (r : ℂ)
    rw [algebraicLimitTrace_of]
    exact hr_value

/-- Compatible algebraic states glue to an algebraic state on the directed
algebraic direct limit.  Cyclicity is not required. -/
theorem algebraicLimitTrace_isAlgebraicState (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (h_tau : ∀ i, IsAlgebraicState (tau i)) :
    IsAlgebraicState (algebraicLimitTrace tau compatible) := by
  refine ⟨?_, algebraicLimitTrace_positive tau compatible (fun i => (h_tau i).positive)⟩
  let i : ι := Classical.arbitrary ι
  change algebraicLimitTrace tau compatible (1 : DirectLimit A f) = 1
  rw [DirectLimit.one_def i]
  exact (h_tau i).map_one

/-- Compatible algebraic tracial states glue to an algebraic tracial state on
the directed algebraic direct limit. -/
theorem algebraicLimitTrace_isAlgebraicTracialState (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (h_tau : ∀ i, IsAlgebraicTracialState (tau i)) :
    IsAlgebraicTracialState (algebraicLimitTrace tau compatible) := by
  have h_unital_cyclic := algebraicLimitTrace_isUnitalCyclic tau compatible
    (fun i => ⟨(h_tau i).map_one, (h_tau i).cyclic⟩)
  exact
    { toIsAlgebraicState :=
        { map_one := h_unital_cyclic.map_one
          positive := algebraicLimitTrace_positive tau compatible (fun i => (h_tau i).positive) }
      cyclic := h_unital_cyclic.cyclic }

end StabilizerHyperfinite
