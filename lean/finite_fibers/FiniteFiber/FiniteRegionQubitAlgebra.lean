import FiniteFiber.FiniteTensorMatrixChain

/-!
# Finite-region qubit local algebras

For a site type `Site` with decidable equality and a finite region
`F : Finset Site`, the computational basis of the region is `↥F → Fin 2` and
the local algebra is the complex matrix algebra on that basis.

For a finite inclusion `F ⊆ F'`, restriction to `F` and to `F' \ F` gives a
canonical coordinate equivalence

`(↥F' → Fin 2) ≃ (↥F → Fin 2) × (↥(F' \ F) → Fin 2)`.

Transporting the generic Kronecker inclusion `A ↦ A ⊗ 1` through it produces
the physical local inclusion `A_F → A_F'`.  This file proves only the explicit
coordinate formula, injectivity, and operator-norm preservation.  It does not
yet realize Pauli or stabilizer words as matrices, prove compatibility of
successive inclusions, or construct a colimit, norm closure, state, or GNS
representation.
-/

namespace FiniteFiber

open scoped ComplexOrder Kronecker

variable {Site : Type*} [DecidableEq Site]

/-- The computational basis of a finite region: bit assignments on its sites. -/
abbrev finiteRegionBasis (F : Finset Site) := ↥F → Fin 2

/-- The local matrix algebra of a finite region. -/
abbrev finiteRegionQubitAlgebra (F : Finset Site) :=
  Matrix (finiteRegionBasis F) (finiteRegionBasis F) ℂ

namespace FiniteRegionQubitMatrix

/-- The finite-region matrix algebra carries its operator-norm C-star structure. -/
noncomputable scoped instance cStarAlgebra (F : Finset Site) :
    CStarAlgebra (finiteRegionQubitAlgebra F) :=
  CStarMatrix.instCStarAlgebra

end FiniteRegionQubitMatrix

open scoped FiniteFiber.FiniteRegionQubitMatrix

/--
The coordinate equivalence splitting a bit configuration on `F'` into its
restrictions to `F` and to `F' \ F`, for a finite inclusion `F ⊆ F'`.
-/
noncomputable def finiteRegionSplitEquiv
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionBasis F' ≃
      finiteRegionBasis F × finiteRegionBasis (F' \ F) := by
  classical
  refine
    { toFun := fun f =>
        (fun x => f ⟨x.val, hFF' x.property⟩,
          fun x => f ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)
      invFun := fun p => fun x =>
        if hx : x.val ∈ F then p.1 ⟨x.val, hx⟩
        else p.2 ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    funext x
    by_cases hx : x.val ∈ F
    · simp [hx]
    · simp [hx]
  · intro p
    obtain ⟨g, h⟩ := p
    ext x
    · have hx : x.val ∈ F := x.property
      simp [hx]
    · have hx : x.val ∉ F := (Finset.mem_sdiff.mp x.property).2
      simp [hx]

/--
The physical local inclusion `A ↦ A ⊗ 1` from the local algebra of `F` into
the local algebra of `F'`, for a finite inclusion `F ⊆ F'`.
-/
noncomputable def finiteRegionEmbed
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionQubitAlgebra F →⋆ₐ[ℂ] finiteRegionQubitAlgebra F' :=
  coordinateEmbedRight (finiteRegionBasis F) (finiteRegionBasis (F' \ F))
    (finiteRegionBasis F') (finiteRegionSplitEquiv F F' hFF')

/-- The local inclusion is literally the reindexed Kronecker product with the identity. -/
theorem finiteRegionEmbed_apply
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    finiteRegionEmbed F F' hFF' A =
      Matrix.reindex (finiteRegionSplitEquiv F F' hFF').symm
        (finiteRegionSplitEquiv F F' hFF').symm
        (A ⊗ₖ (1 : finiteRegionQubitAlgebra (F' \ F))) :=
  coordinateEmbedRight_apply _ _ _ _ _

/-- The local inclusion is injective. -/
theorem finiteRegionEmbed_injective
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    Function.Injective (finiteRegionEmbed F F' hFF') := by
  letI : Nonempty (finiteRegionBasis (F' \ F)) := ⟨fun _ => 0⟩
  exact coordinateEmbedRight_injective (finiteRegionBasis F)
    (finiteRegionBasis (F' \ F)) (finiteRegionBasis F')
    (finiteRegionSplitEquiv F F' hFF')

/-- The local inclusion preserves the operator norm. -/
theorem finiteRegionEmbed_norm
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    ‖finiteRegionEmbed F F' hFF' A‖ = ‖A‖ :=
  NonUnitalStarAlgHom.norm_map (finiteRegionEmbed F F' hFF')
    (finiteRegionEmbed_injective F F' hFF') A

end FiniteFiber
