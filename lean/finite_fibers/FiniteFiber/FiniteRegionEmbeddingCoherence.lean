import FiniteFiber.FiniteRegionQubitAlgebra

/-!
# Coherence of the finite-region matrix embeddings

For finite regions `F ⊆ F' ⊆ F''` of a site type `Site`, the file
`FiniteFiber.FiniteRegionQubitAlgebra` constructs the local inclusions
`finiteRegionEmbed F F' hFF' : A_F →⋆ₐ[ℂ] A_{F'}` as the reindexed Kronecker
inclusion `A ↦ A ⊗ 1` along the coordinate split
`(↥F' → Fin 2) ≃ (↥F → Fin 2) × (↥(F' \ F) → Fin 2)`.

This file proves the directed-system coherence identity

`finiteRegionEmbed F' F'' hF'F'' (finiteRegionEmbed F F' hFF' A)
  = finiteRegionEmbed F F'' (hFF'.trans hF'F'') A`

for every matrix `A`, directly from those coordinate definitions (no abstract
coherence axiom is introduced).  The proof goes through an explicit entrywise
formula, `finiteRegionEmbed_apply_entry`, which is the additional explicit
equivalence lemma needed to compare the three different coordinate splits:
the matrix entry of `finiteRegionEmbed F F' hFF' A` at a pair of bit
configurations `f, g` on `F'` is `A` evaluated at their restrictions to `F`
when `f` and `g` agree on all sites of `F'` outside `F`, and `0` otherwise.

The composed inclusion `F ⊆ F''` is written `hFF'.trans hF'F''`, since
`HasSubset.Subset.trans` takes `F ⊆ F'` and then `F' ⊆ F''`.

Subset proofs enter only as arguments of `Subtype.mk`, so proof irrelevance is
handled definitionally; the statement is therefore an exact equality of
star-algebra maps applied to an arbitrary matrix, with no weakening.
-/

namespace FiniteFiber

open scoped ComplexOrder Kronecker

open scoped FiniteFiber.FiniteRegionQubitMatrix

variable {Site : Type*} [DecidableEq Site]

/-- Restriction of a bit configuration on `F'` to the subregion `F ⊆ F'`. -/
def finiteRegionRestrict (F F' : Finset Site) (hFF' : F ⊆ F')
    (f : finiteRegionBasis F') : finiteRegionBasis F :=
  fun x => f ⟨x.val, hFF' x.property⟩

omit [DecidableEq Site] in
/-- Restricting along `F ⊆ F' ⊆ F''` in two steps is restricting in one step. -/
theorem finiteRegionRestrict_trans (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') (f : finiteRegionBasis F'') :
    finiteRegionRestrict F F' hFF' (finiteRegionRestrict F' F'' hF'F'' f) =
      finiteRegionRestrict F F'' (hFF'.trans hF'F'') f :=
  rfl

/-- The first component of the coordinate split is the restriction map. -/
theorem finiteRegionSplitEquiv_fst (F F' : Finset Site) (hFF' : F ⊆ F')
    (f : finiteRegionBasis F') :
    (finiteRegionSplitEquiv F F' hFF' f).1 = finiteRegionRestrict F F' hFF' f :=
  rfl

/--
The explicit entrywise formula for the finite-region inclusion: it is the
matrix which is `A` on the `F`-coordinates and diagonal on the complementary
coordinates of `F'`.
-/
theorem finiteRegionEmbed_apply_entry (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) (f g : finiteRegionBasis F') :
    finiteRegionEmbed F F' hFF' A f g =
      if (∀ x : ↥F', x.val ∉ F → f x = g x) then
        A (finiteRegionRestrict F F' hFF' f) (finiteRegionRestrict F F' hFF' g)
      else 0 := by
  classical
  rw [finiteRegionEmbed_apply]
  have hkron :
      (Matrix.reindex (finiteRegionSplitEquiv F F' hFF').symm
          (finiteRegionSplitEquiv F F' hFF').symm
          (A ⊗ₖ (1 : finiteRegionQubitAlgebra (F' \ F)))) f g =
        A (finiteRegionRestrict F F' hFF' f) (finiteRegionRestrict F F' hFF' g) *
          (1 : finiteRegionQubitAlgebra (F' \ F))
            (finiteRegionSplitEquiv F F' hFF' f).2
            (finiteRegionSplitEquiv F F' hFF' g).2 := rfl
  rw [hkron, Matrix.one_apply]
  have hiff :
      ((finiteRegionSplitEquiv F F' hFF' f).2 =
          (finiteRegionSplitEquiv F F' hFF' g).2) ↔
        (∀ x : ↥F', x.val ∉ F → f x = g x) := by
    constructor
    · intro h x hx
      have hx' : x.val ∈ F' \ F := Finset.mem_sdiff.mpr ⟨x.property, hx⟩
      have := congrFun h ⟨x.val, hx'⟩
      simpa [finiteRegionSplitEquiv] using this
    · intro h
      funext x
      have hx : x.val ∉ F := (Finset.mem_sdiff.mp x.property).2
      have := h ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩ hx
      simpa [finiteRegionSplitEquiv] using this
  by_cases hc : (∀ x : ↥F', x.val ∉ F → f x = g x)
  · rw [if_pos hc, if_pos (hiff.mpr hc), mul_one]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h)), mul_zero]

/--
**Coherence of the finite-region embeddings.**  For finite regions
`F ⊆ F' ⊆ F''`, embedding a matrix from `F` into `F'` and then into `F''`
agrees with embedding it directly from `F` into `F''`.
-/
theorem finiteRegionEmbed_trans (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'')
    (A : finiteRegionQubitAlgebra F) :
    finiteRegionEmbed F' F'' hF'F'' (finiteRegionEmbed F F' hFF' A) =
      finiteRegionEmbed F F'' (hFF'.trans hF'F'') A := by
  classical
  ext f g
  rw [finiteRegionEmbed_apply_entry F' F'' hF'F'',
    finiteRegionEmbed_apply_entry F F' hFF',
    finiteRegionEmbed_apply_entry F F'' (hFF'.trans hF'F'')]
  by_cases hc : (∀ x : ↥F'', x.val ∉ F → f x = g x)
  · have h1 : ∀ x : ↥F'', x.val ∉ F' → f x = g x := fun x hx =>
      hc x (fun hxF => hx (hFF' hxF))
    have h2 : ∀ x : ↥F', x.val ∉ F →
        finiteRegionRestrict F' F'' hF'F'' f x =
          finiteRegionRestrict F' F'' hF'F'' g x := fun x hx =>
      hc ⟨x.val, hF'F'' x.property⟩ hx
    rw [if_pos h1, if_pos h2, if_pos hc, finiteRegionRestrict_trans,
      finiteRegionRestrict_trans]
  · have hnot : ¬ ((∀ x : ↥F'', x.val ∉ F' → f x = g x) ∧
        ∀ x : ↥F', x.val ∉ F →
          finiteRegionRestrict F' F'' hF'F'' f x =
            finiteRegionRestrict F' F'' hF'F'' g x) := by
      rintro ⟨h1, h2⟩
      refine hc ?_
      intro x hx
      by_cases hxF' : x.val ∈ F'
      · have := h2 ⟨x.val, hxF'⟩ hx
        simpa [finiteRegionRestrict] using this
      · exact h1 x hxF'
    rw [if_neg hc]
    by_cases h1 : (∀ x : ↥F'', x.val ∉ F' → f x = g x)
    · rw [if_pos h1, if_neg (fun h2 => hnot ⟨h1, h2⟩)]
    · rw [if_neg h1]

/-- The composed form of the coherence identity, as an equality of star-algebra maps. -/
theorem finiteRegionEmbed_comp (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') :
    (finiteRegionEmbed F' F'' hF'F'').comp (finiteRegionEmbed F F' hFF') =
      finiteRegionEmbed F F'' (hFF'.trans hF'F'') :=
  StarAlgHom.ext fun A => finiteRegionEmbed_trans F F' F'' hFF' hF'F'' A

end FiniteFiber

