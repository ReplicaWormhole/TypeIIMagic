import AristotleCandidates.BoundedStateGNS

/-!
# The pre-GNS isometry induced by a compatible pair of states

For supplied data `D : StabilizerHyperfinite.BoundedStateGNS.Data` (two unital
complex C⋆ algebras, a supplied star-algebra equivalence between them, and
supplied positive unital functionals which are compatible along the
equivalence), this module constructs the induced map between Mathlib's *pre*-GNS
spaces

    D.sourceState.PreGNS → D.targetState.PreGNS,   `[a] ↦ [equivalence a]`,

using Mathlib's transparent `toPreGNS`/`ofPreGNS` linear equivalences rather
than any new quotient construction.  The map is shown to be complex linear and
to preserve the pre-GNS inner product exactly; the corresponding norm equality
and the packaging as a linear isometric equivalence follow.

Nothing beyond this is claimed: there is **no** product state, **no** spatial
tensor-product identification, **no** bicommutant, von Neumann algebra, trace or
weight, and **no** normality, faithfulness, semifiniteness, hyperfiniteness or
factor classification here.
-/

namespace StabilizerHyperfinite

namespace BoundedStateGNS

open scoped ComplexOrder InnerProductSpace

variable (D : Data)

/-! ### The pre-GNS spaces -/

/-- The pre-GNS (semi-)inner product space of the supplied source state, i.e.
Mathlib's `PositiveLinearMap.PreGNS`. -/
abbrev sourcePreGNS : Type _ := D.sourceState.PreGNS

/-- The pre-GNS (semi-)inner product space of the supplied target state, i.e.
Mathlib's `PositiveLinearMap.PreGNS`. -/
abbrev targetPreGNS : Type _ := D.targetState.PreGNS

/-! ### The induced linear map on pre-GNS spaces -/

/-- The linear map on pre-GNS spaces induced by the supplied star-algebra
equivalence: `[a] ↦ [equivalence a]`, written through Mathlib's transparent
`ofPreGNS`/`toPreGNS` linear equivalences. -/
def preGNSLinearEquiv : sourcePreGNS D ≃ₗ[ℂ] targetPreGNS D :=
  (D.sourceState.ofPreGNS).trans
    (D.equivalence.toAlgEquiv.toLinearEquiv.trans D.targetState.toPreGNS)

/-- The linear map on pre-GNS spaces induced by the supplied star-algebra
equivalence: `[a] ↦ [equivalence a]`. -/
def preGNSMap : sourcePreGNS D →ₗ[ℂ] targetPreGNS D :=
  (preGNSLinearEquiv D).toLinearMap

@[simp]
theorem preGNSMap_apply (x : sourcePreGNS D) :
    preGNSMap D x = D.targetState.toPreGNS (D.equivalence (D.sourceState.ofPreGNS x)) :=
  rfl

/-- On elements coming from the algebra, the induced map is exactly
`[a] ↦ [equivalence a]`. -/
@[simp]
theorem preGNSMap_toPreGNS (a : D.source) :
    preGNSMap D (D.sourceState.toPreGNS a) = D.targetState.toPreGNS (D.equivalence a) :=
  rfl

theorem ofPreGNS_preGNSMap (x : sourcePreGNS D) :
    D.targetState.ofPreGNS (preGNSMap D x) = D.equivalence (D.sourceState.ofPreGNS x) :=
  rfl

/-! ### Exact preservation of the pre-GNS inner product -/

/-- **The pre-GNS inner-product bridge.**  The induced map preserves the pre-GNS
inner product exactly. -/
theorem preGNSMap_inner (x y : sourcePreGNS D) :
    ⟪preGNSMap D x, preGNSMap D y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_inner_def,
    ofPreGNS_preGNSMap, ofPreGNS_preGNSMap, ← map_star D.equivalence, ← map_mul D.equivalence,
    ← state_compat D]

/-- The induced map preserves the pre-GNS norm. -/
theorem preGNSMap_norm (x : sourcePreGNS D) : ‖preGNSMap D x‖ = ‖x‖ := by
  have h := preGNSMap_inner D x x
  rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def]
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_inner_def] at h
  rw [h]

/-- The induced map, packaged as a linear isometry of pre-GNS spaces. -/
def preGNSIsometry : sourcePreGNS D →ₗᵢ[ℂ] targetPreGNS D where
  toLinearMap := preGNSMap D
  norm_map' := preGNSMap_norm D

@[simp]
theorem preGNSIsometry_apply (x : sourcePreGNS D) :
    preGNSIsometry D x = preGNSMap D x := rfl

/-! ### Bijectivity and the isometric equivalence -/

/-- The linear map on pre-GNS spaces induced by the inverse equivalence. -/
def preGNSMapSymm : targetPreGNS D →ₗ[ℂ] sourcePreGNS D :=
  (preGNSLinearEquiv D).symm.toLinearMap

@[simp]
theorem preGNSMapSymm_apply (y : targetPreGNS D) :
    preGNSMapSymm D y = D.sourceState.toPreGNS (D.equivalence.symm (D.targetState.ofPreGNS y)) :=
  rfl

@[simp]
theorem preGNSMapSymm_preGNSMap (x : sourcePreGNS D) :
    preGNSMapSymm D (preGNSMap D x) = x := by
  simp only [preGNSMapSymm_apply, preGNSMap_apply, PositiveLinearMap.ofPreGNS_toPreGNS,
    StarAlgEquiv.symm_apply_apply]
  rfl

@[simp]
theorem preGNSMap_preGNSMapSymm (y : targetPreGNS D) :
    preGNSMap D (preGNSMapSymm D y) = y := by
  simp only [preGNSMapSymm_apply, preGNSMap_apply, PositiveLinearMap.ofPreGNS_toPreGNS,
    StarAlgEquiv.apply_symm_apply]
  rfl

theorem preGNSMap_bijective : Function.Bijective (preGNSMap D) :=
  ⟨Function.LeftInverse.injective (preGNSMapSymm_preGNSMap D),
    Function.RightInverse.surjective (preGNSMap_preGNSMapSymm D)⟩

/-- The induced map, packaged as a linear isometric equivalence between the two
pre-GNS spaces. -/
def preGNSIsometryEquiv : sourcePreGNS D ≃ₗᵢ[ℂ] targetPreGNS D where
  toFun := preGNSMap D
  invFun := preGNSMapSymm D
  left_inv := preGNSMapSymm_preGNSMap D
  right_inv := preGNSMap_preGNSMapSymm D
  map_add' := map_add (preGNSMap D)
  map_smul' := map_smul (preGNSMap D)
  norm_map' := preGNSMap_norm D

@[simp]
theorem preGNSIsometryEquiv_apply (x : sourcePreGNS D) :
    preGNSIsometryEquiv D x = preGNSMap D x := rfl

@[simp]
theorem preGNSIsometryEquiv_symm_apply (y : targetPreGNS D) :
    (preGNSIsometryEquiv D).symm y = preGNSMapSymm D y := rfl

/-- The isometric equivalence preserves the pre-GNS inner product. -/
theorem preGNSIsometryEquiv_inner (x y : sourcePreGNS D) :
    ⟪preGNSIsometryEquiv D x, preGNSIsometryEquiv D y⟫_ℂ = ⟪x, y⟫_ℂ :=
  preGNSMap_inner D x y

/-- Summary of the pre-GNS step: the induced map is additive, complex homogeneous,
preserves the pre-GNS inner product exactly, preserves the pre-GNS norm, and is
bijective. -/
theorem preGNS_package :
    (∀ x y : sourcePreGNS D, preGNSMap D (x + y) = preGNSMap D x + preGNSMap D y) ∧
      (∀ (r : ℂ) (x : sourcePreGNS D), preGNSMap D (r • x) = r • preGNSMap D x) ∧
      (∀ x y : sourcePreGNS D, ⟪preGNSMap D x, preGNSMap D y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ x : sourcePreGNS D, ‖preGNSMap D x‖ = ‖x‖) ∧
      Function.Bijective (preGNSMap D) :=
  ⟨map_add (preGNSMap D), map_smul (preGNSMap D), preGNSMap_inner D, preGNSMap_norm D,
    preGNSMap_bijective D⟩

/-! ### The induced map on the GNS completions -/

/-- The induced continuous linear map between the GNS Hilbert spaces, obtained by
completing the pre-GNS isometry. -/
noncomputable def gnsMap : sourceGNS D →L[ℂ] targetGNS D :=
  (preGNSIsometry D).toContinuousLinearMap.completion

@[simp]
theorem gnsMap_coe (x : sourcePreGNS D) :
    gnsMap D (x : sourceGNS D) = ((preGNSMap D x : targetPreGNS D) : targetGNS D) := by
  simp [gnsMap, ContinuousLinearMap.completion]

/-- The induced map on the GNS completions preserves the norm. -/
theorem gnsMap_norm (x : sourceGNS D) : ‖gnsMap D x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    rw [gnsMap_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
      preGNSMap_norm]

/-- The induced map on the GNS completions, packaged as a linear isometry of
Hilbert spaces. -/
noncomputable def gnsIsometry : sourceGNS D →ₗᵢ[ℂ] targetGNS D where
  toLinearMap := (gnsMap D).toLinearMap
  norm_map' := gnsMap_norm D

@[simp]
theorem gnsIsometry_apply (x : sourceGNS D) : gnsIsometry D x = gnsMap D x := rfl

/-- The induced map on the GNS completions preserves the inner product. -/
theorem gnsMap_inner (x y : sourceGNS D) :
    ⟪gnsMap D x, gnsMap D y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (gnsIsometry D).inner_map_map x y

end BoundedStateGNS

end StabilizerHyperfinite
