import AristotleCandidates.PreGNSIsometry

/-!
# The GNS unitary and the intertwining identity

For supplied data `D : StabilizerHyperfinite.BoundedStateGNS.Data` (two unital
complex C⋆ algebras, a supplied star-algebra equivalence between them, and
supplied positive unital functionals compatible along the equivalence), the
module `AristotleCandidates.PreGNSIsometry` produced

* the pre-GNS linear isometric equivalence `preGNSIsometryEquiv D`, and
* its completion `gnsMap D : sourceGNS D →L[ℂ] targetGNS D`, a linear isometry
  of the GNS Hilbert spaces.

Here we complete the inverse pre-GNS map as well, show that the two completed
maps are mutually inverse (by density, using
`UniformSpace.Completion.induction_on`), and package the result as a complex
linear isometric equivalence

    gnsUnitary D : sourceGNS D ≃ₗᵢ[ℂ] targetGNS D

between the two GNS Hilbert spaces (a unitary in the linear-isometric sense).

We then prove the intertwining identity, for every `a : D.source` and every GNS
vector `x : sourceGNS D`,

    gnsUnitary D (sourceGNSRepresentation D a x)
      = targetGNSRepresentation D (D.equivalence a) (gnsUnitary D x),

first on the dense image of the pre-GNS space and then on the whole completion
by continuity, together with its operator-level and inverse-direction forms.

Nothing beyond this is claimed: there is **no** product state, **no** spatial
tensor-product identification, **no** bicommutant, von Neumann algebra, trace or
weight, and **no** normality, faithfulness, semifiniteness, hyperfiniteness or
factor classification here.
-/

namespace StabilizerHyperfinite

namespace BoundedStateGNS

open scoped ComplexOrder InnerProductSpace

variable (D : Data)

/-! ### The completed inverse map -/

/-- The inverse pre-GNS map, packaged as a linear isometry
`targetPreGNS D →ₗᵢ[ℂ] sourcePreGNS D`. -/
def preGNSIsometrySymm : targetPreGNS D →ₗᵢ[ℂ] sourcePreGNS D :=
  (preGNSIsometryEquiv D).symm.toLinearIsometry

@[simp]
theorem preGNSIsometrySymm_apply (y : targetPreGNS D) :
    preGNSIsometrySymm D y = preGNSMapSymm D y := rfl

/-- The completion of the inverse pre-GNS isometry: a continuous linear map
between the GNS Hilbert spaces in the direction `targetGNS D → sourceGNS D`. -/
noncomputable def gnsMapSymm : targetGNS D →L[ℂ] sourceGNS D :=
  (preGNSIsometrySymm D).toContinuousLinearMap.completion

@[simp]
theorem gnsMapSymm_coe (y : targetPreGNS D) :
    gnsMapSymm D (y : targetGNS D) = ((preGNSMapSymm D y : sourcePreGNS D) : sourceGNS D) := by
  simp [gnsMapSymm, ContinuousLinearMap.completion]

/-- The completed inverse map is norm preserving. -/
theorem gnsMapSymm_norm (y : targetGNS D) : ‖gnsMapSymm D y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih b =>
    rw [gnsMapSymm_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
      ← preGNSMap_norm D (preGNSMapSymm D b), preGNSMap_preGNSMapSymm]

/-! ### The two completed maps are mutually inverse -/

@[simp]
theorem gnsMapSymm_gnsMap (x : sourceGNS D) : gnsMapSymm D (gnsMap D x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a => rw [gnsMap_coe, gnsMapSymm_coe, preGNSMapSymm_preGNSMap]

@[simp]
theorem gnsMap_gnsMapSymm (y : targetGNS D) : gnsMap D (gnsMapSymm D y) = y := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih b => rw [gnsMapSymm_coe, gnsMap_coe, preGNSMap_preGNSMapSymm]

theorem gnsMap_bijective : Function.Bijective (gnsMap D) :=
  ⟨Function.LeftInverse.injective (gnsMapSymm_gnsMap D),
    Function.RightInverse.surjective (gnsMap_gnsMapSymm D)⟩

/-! ### The GNS unitary -/

/-- **The GNS unitary.**  The completion of the pre-GNS isometry, packaged as a
complex linear isometric equivalence between the two GNS Hilbert spaces. -/
noncomputable def gnsUnitary : sourceGNS D ≃ₗᵢ[ℂ] targetGNS D where
  toFun := gnsMap D
  invFun := gnsMapSymm D
  left_inv := gnsMapSymm_gnsMap D
  right_inv := gnsMap_gnsMapSymm D
  map_add' := map_add (gnsMap D)
  map_smul' := map_smul (gnsMap D)
  norm_map' := gnsMap_norm D

@[simp]
theorem gnsUnitary_apply (x : sourceGNS D) : gnsUnitary D x = gnsMap D x := rfl

@[simp]
theorem gnsUnitary_symm_apply (y : targetGNS D) : (gnsUnitary D).symm y = gnsMapSymm D y := rfl

@[simp]
theorem gnsUnitary_coe (x : sourcePreGNS D) :
    gnsUnitary D (x : sourceGNS D) = ((preGNSMap D x : targetPreGNS D) : targetGNS D) :=
  gnsMap_coe D x

/-- The GNS unitary preserves the inner product of the GNS Hilbert spaces. -/
theorem gnsUnitary_inner (x y : sourceGNS D) :
    ⟪gnsUnitary D x, gnsUnitary D y⟫_ℂ = ⟪x, y⟫_ℂ :=
  gnsMap_inner D x y

/-- The GNS unitary preserves norms. -/
theorem gnsUnitary_norm (x : sourceGNS D) : ‖gnsUnitary D x‖ = ‖x‖ :=
  gnsMap_norm D x

/-! ### The intertwining identity -/

/-- The intertwining identity on the dense image of the pre-GNS space. -/
theorem gnsUnitary_intertwines_coe (a : D.source) (x : sourcePreGNS D) :
    gnsUnitary D (sourceGNSRepresentation D a (x : sourceGNS D)) =
      targetGNSRepresentation D (D.equivalence a) (gnsUnitary D (x : sourceGNS D)) := by
  simp [sourceGNSRepresentation, targetGNSRepresentation, preGNSMap,
    preGNSLinearEquiv, map_mul]

/-- **The intertwining identity.**  The GNS unitary carries the source GNS
representation of `a` to the target GNS representation of `D.equivalence a`. -/
theorem gnsUnitary_intertwines (a : D.source) (x : sourceGNS D) :
    gnsUnitary D (sourceGNSRepresentation D a x) =
      targetGNSRepresentation D (D.equivalence a) (gnsUnitary D x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => exact gnsUnitary_intertwines_coe D a x

/-- The intertwining identity, read in the inverse direction. -/
theorem gnsUnitary_symm_intertwines (a : D.source) (y : targetGNS D) :
    (gnsUnitary D).symm (targetGNSRepresentation D (D.equivalence a) y) =
      sourceGNSRepresentation D a ((gnsUnitary D).symm y) := by
  have h := gnsUnitary_intertwines D a ((gnsUnitary D).symm y)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [← h, LinearIsometryEquiv.symm_apply_apply]

/-- The intertwining identity at the level of bounded operators: conjugation by
the GNS unitary carries the source GNS representation to the target GNS
representation along the supplied equivalence. -/
theorem gnsUnitary_conj_representation (a : D.source) :
    (targetGNSRepresentation D (D.equivalence a) : targetGNS D → targetGNS D) =
      gnsUnitary D ∘ (sourceGNSRepresentation D a : sourceGNS D → sourceGNS D) ∘
        (gnsUnitary D).symm := by
  funext y
  simp only [Function.comp_apply]
  rw [gnsUnitary_intertwines D a ((gnsUnitary D).symm y), LinearIsometryEquiv.apply_symm_apply]

/-- Summary of the completion-level GNS step: the completed map is a linear
isometric equivalence of the GNS Hilbert spaces, it preserves inner products,
and it intertwines the two GNS representations along the supplied
equivalence. -/
theorem gnsUnitary_package :
    (∀ x : sourceGNS D, (gnsUnitary D).symm (gnsUnitary D x) = x) ∧
      (∀ y : targetGNS D, gnsUnitary D ((gnsUnitary D).symm y) = y) ∧
      (∀ x y : sourceGNS D, ⟪gnsUnitary D x, gnsUnitary D y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ x : sourceGNS D, ‖gnsUnitary D x‖ = ‖x‖) ∧
      (∀ (a : D.source) (x : sourceGNS D),
        gnsUnitary D (sourceGNSRepresentation D a x) =
          targetGNSRepresentation D (D.equivalence a) (gnsUnitary D x)) :=
  ⟨(gnsUnitary D).symm_apply_apply, (gnsUnitary D).apply_symm_apply, gnsUnitary_inner D,
    gnsUnitary_norm D, gnsUnitary_intertwines D⟩

end BoundedStateGNS

end StabilizerHyperfinite
