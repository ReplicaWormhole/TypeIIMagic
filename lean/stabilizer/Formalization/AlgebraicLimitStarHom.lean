import Formalization.AlgebraicStarDirectLimit

/-!
# Star-algebra maps out of an algebraic directed limit

Finite-word Pauli maps must be compatible with enlargement of their finite
supports before they can define a quasi-local map.  This module supplies the
algebraic part of that passage: a compatible family of finite-stage star
algebra homomorphisms induces a star algebra homomorphism from the directed
algebraic limit.
-/

namespace StabilizerHyperfinite

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]

variable {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]

/-- The canonical star-algebra map from one finite stage into its algebraic
direct limit. -/
noncomputable def algebraicLimitStageStarAlgHom (i : ι) :
    A i →⋆ₐ[ℂ] DirectLimit A f :=
  { DirectLimit.Ring.of A f i with
    commutes' := by
      intro c
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        DirectLimit.one_def i, DirectLimit.smul_def]
      rfl
    map_star' := by
      intro x
      exact (star_of i x).symm }

@[simp]
theorem algebraicLimitStageStarAlgHom_apply (i : ι) (x : A i) :
    algebraicLimitStageStarAlgHom (f := f) i x =
      DirectLimit.Module.of ℂ ι A f i x :=
  rfl

/-- The star-algebra map induced by compatible maps on a directed system of
finite stages. -/
noncomputable def algebraicLimitStarAlgHom
    (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (compatible : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x) :
    DirectLimit A f →⋆ₐ[ℂ] B :=
  let lift : DirectLimit A f →+* B :=
    DirectLimit.Ring.lift A f B (fun i => (g i).toRingHom) compatible
  { lift with
    commutes' := by
      intro c
      let i : ι := Classical.arbitrary ι
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        DirectLimit.one_def i, DirectLimit.smul_def]
      change lift (DirectLimit.Ring.of A f i (c • (1 : A i))) = c • (1 : B)
      rw [DirectLimit.Ring.lift_of]
      simpa only [Algebra.algebraMap_eq_smul_one] using (g i).commutes c
    map_star' := by
      intro z
      induction z using DirectLimit.induction with
      | _ i x =>
        change lift (star (DirectLimit.Module.of ℂ ι A f i x)) =
          star (lift (DirectLimit.Module.of ℂ ι A f i x))
        rw [star_of]
        change lift (DirectLimit.Ring.of A f i (star x)) =
          star (lift (DirectLimit.Ring.of A f i x))
        rw [DirectLimit.Ring.lift_of, DirectLimit.Ring.lift_of]
        exact (g i).map_star' x }

/-- The induced map has the prescribed value on every finite-stage element. -/
@[simp]
theorem algebraicLimitStarAlgHom_of
    (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (compatible : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)
    (i : ι) (x : A i) :
    algebraicLimitStarAlgHom g compatible (DirectLimit.Module.of ℂ ι A f i x) = g i x :=
  by
    change DirectLimit.Ring.lift A f B (fun i => (g i).toRingHom) compatible
      (DirectLimit.Ring.of A f i x) = g i x
    exact DirectLimit.Ring.lift_of _ _ _ _ _

/-- Compatible finite-stage star-algebra maps determine at most one
star-algebra map out of the algebraic direct limit. -/
theorem algebraicLimitStarAlgHom_unique
    (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (compatible : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)
    (phi : DirectLimit A f →⋆ₐ[ℂ] B)
    (h_phi : ∀ i x, phi (DirectLimit.Module.of ℂ ι A f i x) = g i x) :
    phi = algebraicLimitStarAlgHom g compatible := by
  apply StarAlgHom.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
    change phi (DirectLimit.Module.of ℂ ι A f i x) =
      algebraicLimitStarAlgHom g compatible (DirectLimit.Module.of ℂ ι A f i x)
    rw [algebraicLimitStarAlgHom_of]
    exact h_phi i x

section Equivalences

variable {D : ι → Type*}
variable [∀ i, Semiring (D i)] [∀ i, StarRing (D i)] [∀ i, Algebra ℂ (D i)]
variable {h : ∀ i j : ι, i ≤ j → D i →⋆ₐ[ℂ] D j}
variable [DirectedSystem D (h · · ·)]

/-- Compatible finite-stage star-algebra equivalences induce a star-algebra
equivalence of the corresponding algebraic directed limits. -/
noncomputable def algebraicLimitStarAlgEquiv
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (compatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x)) :
    DirectLimit A f ≃⋆ₐ[ℂ] DirectLimit D h := by
  let forwardStages : ∀ i, A i →⋆ₐ[ℂ] DirectLimit D h :=
    fun i => (algebraicLimitStageStarAlgHom (A := D) (f := h) i).comp (e i)
  have forwardCompatible : ∀ i j (le : i ≤ j) x,
      forwardStages j (f i j le x) = forwardStages i x := by
    intro i j le x
    change DirectLimit.Ring.of D h j (e j (f i j le x)) =
      DirectLimit.Ring.of D h i (e i x)
    rw [compatible]
    exact DirectLimit.Ring.of_f (G := D) (f := h) le (e i x)
  let forward : DirectLimit A f →⋆ₐ[ℂ] DirectLimit D h :=
    algebraicLimitStarAlgHom forwardStages forwardCompatible
  let backwardStages : ∀ i, D i →⋆ₐ[ℂ] DirectLimit A f :=
    fun i => (algebraicLimitStageStarAlgHom (A := A) (f := f) i).comp (e i).symm
  have backwardCompatible : ∀ i j (le : i ≤ j) x,
      backwardStages j (h i j le x) = backwardStages i x := by
    intro i j le x
    have h_inverse :
        (e j).symm (h i j le x) = f i j le ((e i).symm x) := by
      apply (e j).injective
      calc
        (e j) ((e j).symm (h i j le x)) = h i j le x :=
          (e j).apply_symm_apply _
        _ = h i j le ((e i) ((e i).symm x)) := by rw [(e i).apply_symm_apply]
        _ = (e j) (f i j le ((e i).symm x)) :=
          (compatible i j le ((e i).symm x)).symm
    change DirectLimit.Ring.of A f j ((e j).symm (h i j le x)) =
      DirectLimit.Ring.of A f i ((e i).symm x)
    rw [h_inverse]
    exact DirectLimit.Ring.of_f (G := A) (f := f) le ((e i).symm x)
  let backward : DirectLimit D h →⋆ₐ[ℂ] DirectLimit A f :=
    algebraicLimitStarAlgHom backwardStages backwardCompatible
  exact StarAlgEquiv.ofStarAlgHom forward backward
    (by
      intro z
      induction z using DirectLimit.induction with
      | _ i x =>
        change backward (forward (DirectLimit.Module.of ℂ ι A f i x)) =
          DirectLimit.Module.of ℂ ι A f i x
        simp [forward, backward, forwardStages, backwardStages,
          algebraicLimitStarAlgHom_of, algebraicLimitStageStarAlgHom_apply])
    (by
      intro z
      induction z using DirectLimit.induction with
      | _ i x =>
        change forward (backward (DirectLimit.Module.of ℂ ι D h i x)) =
          DirectLimit.Module.of ℂ ι D h i x
        simp [forward, backward, forwardStages, backwardStages,
          algebraicLimitStarAlgHom_of, algebraicLimitStageStarAlgHom_apply])

/-- The algebraic-limit equivalence induced by compatible finite-stage
equivalences has the prescribed value on every stage representative. -/
@[simp]
theorem algebraicLimitStarAlgEquiv_of
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (compatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (i : ι) (x : A i) :
    algebraicLimitStarAlgEquiv e compatible
      (DirectLimit.Module.of ℂ ι A f i x) =
        DirectLimit.Module.of ℂ ι D h i (e i x) :=
  rfl

end Equivalences

end StabilizerHyperfinite
