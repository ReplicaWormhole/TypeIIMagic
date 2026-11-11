import AristotleCandidates.CStarAlphaGNSBridge

/-!
# A normal von Neumann extension interface over the P26 C⋆/GNS bridge

**Context declaration.** Source basis: `main.tex:1970-2004`.

The manuscript passage proposes to pass from the C⋆/GNS level identification to
the von Neumann level and to transport normal functionals along the resulting
map.  This module packages exactly that step **as an interface**: every von
Neumann object is *supplied*, and only purely formal transport statements are
proved.

## Supplied data (`NormalExtensionData`)

* `bridge` — the P26 datum `CStarAlphaGNSBridge.AlphaGNSData`, which already
  provides the two C⋆ completions, the C⋆ equivalence `alphaCStar`, the two GNS
  Hilbert spaces, the GNS representations, the GNS unitary and the conjugation
  star-algebra equivalence `gnsConj`.  Nothing about GNS is re-proved here.
* `SourceVN`, `TargetVN` — **supplied** complex star algebras standing for the
  supplied von Neumann closures, together with **supplied** injective
  star-algebra representations `sourceRepresentation`, `targetRepresentation`
  onto operators on the respective GNS Hilbert spaces.  They are *not*
  constructed: no weak closure, bicommutant, or von Neumann bicommutant theorem
  is used.
* `sourceRep`, `targetRep` (with `sourceRep_spec`, `targetRep_spec`) — the
  supplied lifts of the two GNS representations through those representations,
  i.e. the assumption that the represented algebras contain the GNS images.
* `normalExtension` — a **supplied** star-algebra equivalence
  `SourceVN ≃⋆ₐ[ℂ] TargetVN` together with `normalExtension_extends`: the
  supplied assumption that, at the level of represented operators, it extends
  the P26 C⋆/GNS-level conjugation `gnsConj`.
* `IsNormalSourceFunctional`, `IsNormalTargetFunctional` — **supplied**
  predicates singling out the normal linear functionals on the two represented
  algebras, and `normal_pullback`, the supplied assumption that the extension is
  normal in the sense that pullback along it carries supplied normal target
  functionals to supplied normal source functionals.

## Checked consequences

All of the following are formal consequences of the supplied data:

* `NormalExtensionData.normalExtension_sourceRep`: the extension carries the
  lifted source GNS representative of `a` to the lifted target GNS
  representative of `alphaCStar a`.  This uses injectivity of the supplied
  target representation together with the P26 identity
  `gnsConj_sourceGNSRepresentation`.
* `NormalExtensionData.image_sourceRepRange`,
  `represented_image_sourceRepRange`: transport of the represented range, both
  inside `TargetVN` and after representing as operators on the target GNS space.
* `NormalExtensionData.image_centralizer`,
  `image_centralizer_centralizer`, `commute_iff`: transport of the purely
  **algebraic** `Set.centralizer` commutant and bicommutant computed inside the
  supplied represented algebras.
* `NormalExtensionData.pullback`: pullback of functionals along the supplied
  extension, with `pullback_apply`, `pullback_sourceRep`, `pullback_one`,
  `pullback_normal` (transport of the supplied normality predicate),
  `pullback_injective`, and the round-trip identities with the pushforward along
  the inverse.

## What is *not* claimed

Nothing here constructs a von Neumann closure or a normal extension, and nothing
asserts quasi-equivalence, a spatial (or any) tensor product, hyperfiniteness,
factor type, or the existence of a trace or weight.  The commutants below are
the algebraic `Set.centralizer` ones.  No gLU, refinement, or layer-coherence
hypothesis appears.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace AristotleCandidates

namespace NormalVonNeumannExtensionInterface

open StabilizerHyperfinite
open AristotleCandidates.CStarAlphaGNSBridge

open scoped ComplexOrder InnerProductSpace

/-! ## The supplied data -/

/-- **Supplied** von Neumann level data over a P26 C⋆/GNS bridge.

Every field is an input: the two represented algebras with their supplied
injective operator representations, the lifts of the two GNS representations,
the star-algebra equivalence `normalExtension` extending the P26 conjugation
`gnsConj` at the level of represented operators, and the two normality
predicates together with the assumption that pullback along the extension
preserves the supplied normality. -/
structure NormalExtensionData where
  /-- The supplied P26 C⋆/GNS bridge datum. -/
  bridge : AlphaGNSData
  /-- The supplied represented (von Neumann) algebra on the source side. -/
  SourceVN : Type*
  /-- The supplied represented (von Neumann) algebra on the target side. -/
  TargetVN : Type*
  [sourceRing : Ring SourceVN]
  [sourceStarRing : StarRing SourceVN]
  [sourceAlgebra : Algebra ℂ SourceVN]
  [sourceStarModule : StarModule ℂ SourceVN]
  [targetRing : Ring TargetVN]
  [targetStarRing : StarRing TargetVN]
  [targetAlgebra : Algebra ℂ TargetVN]
  [targetStarModule : StarModule ℂ TargetVN]
  /-- The supplied representation of the source algebra by operators on the
  source GNS space. -/
  sourceRepresentation : SourceVN →⋆ₐ[ℂ] (bridge.sourceGNS →L[ℂ] bridge.sourceGNS)
  /-- The supplied source representation is injective (the algebra is a
  represented algebra of operators). -/
  sourceRepresentation_injective : Function.Injective sourceRepresentation
  /-- The supplied representation of the target algebra by operators on the
  target GNS space. -/
  targetRepresentation : TargetVN →⋆ₐ[ℂ] (bridge.targetGNS →L[ℂ] bridge.targetGNS)
  /-- The supplied target representation is injective. -/
  targetRepresentation_injective : Function.Injective targetRepresentation
  /-- The supplied lift of the source GNS representation into `SourceVN`. -/
  sourceRep : bridge.SourceCStar → SourceVN
  /-- The lift represents the source GNS representation. -/
  sourceRep_spec : ∀ a : bridge.SourceCStar,
    sourceRepresentation (sourceRep a) = bridge.sourceGNSRepresentation a
  /-- The supplied lift of the target GNS representation into `TargetVN`. -/
  targetRep : bridge.TargetCStar → TargetVN
  /-- The lift represents the target GNS representation. -/
  targetRep_spec : ∀ b : bridge.TargetCStar,
    targetRepresentation (targetRep b) = bridge.targetGNSRepresentation b
  /-- The supplied star-algebra equivalence of the two represented algebras. -/
  normalExtension : SourceVN ≃⋆ₐ[ℂ] TargetVN
  /-- **The supplied extension property**: on represented GNS elements the
  extension agrees with the P26 C⋆/GNS-level conjugation `gnsConj`. -/
  normalExtension_extends : ∀ a : bridge.SourceCStar,
    targetRepresentation (normalExtension (sourceRep a)) =
      bridge.gnsConj (bridge.sourceGNSRepresentation a)
  /-- The supplied predicate singling out normal functionals on `SourceVN`. -/
  IsNormalSourceFunctional : (SourceVN →ₗ[ℂ] ℂ) → Prop
  /-- The supplied predicate singling out normal functionals on `TargetVN`. -/
  IsNormalTargetFunctional : (TargetVN →ₗ[ℂ] ℂ) → Prop
  /-- **Supplied normality of the extension**: pullback along the extension
  carries supplied normal target functionals to supplied normal source
  functionals. -/
  normal_pullback : ∀ (psi : TargetVN →ₗ[ℂ] ℂ) (phi : SourceVN →ₗ[ℂ] ℂ),
    (∀ T : SourceVN, phi T = psi (normalExtension T)) →
      IsNormalTargetFunctional psi → IsNormalSourceFunctional phi

attribute [instance] NormalExtensionData.sourceRing NormalExtensionData.sourceStarRing
  NormalExtensionData.sourceAlgebra NormalExtensionData.sourceStarModule
  NormalExtensionData.targetRing NormalExtensionData.targetStarRing
  NormalExtensionData.targetAlgebra NormalExtensionData.targetStarModule

namespace NormalExtensionData

variable (N : NormalExtensionData)

/-- The supplied C⋆-level equivalence, inherited from P26/P25. -/
abbrev alphaCStar : N.bridge.SourceCStar ≃⋆ₐ[ℂ] N.bridge.TargetCStar :=
  N.bridge.alphaCStar

/-! ## Transport of the represented ranges -/

/-- **The extension formula on represented elements.**  The supplied extension
carries the lifted source GNS representative of `a` to the lifted target GNS
representative of `alphaCStar a`.  Only the supplied extension property,
injectivity of the supplied target representation, and the P26 identity
`gnsConj_sourceGNSRepresentation` are used. -/
theorem normalExtension_sourceRep (a : N.bridge.SourceCStar) :
    N.normalExtension (N.sourceRep a) = N.targetRep (N.alphaCStar a) := by
  refine N.targetRepresentation_injective ?_
  rw [N.normalExtension_extends a, N.targetRep_spec,
    N.bridge.gnsConj_sourceGNSRepresentation a]

/-- **Transport of the represented range inside the supplied algebras.** -/
theorem image_sourceRepRange :
    N.normalExtension '' Set.range N.sourceRep = Set.range N.targetRep := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨N.alphaCStar a, (N.normalExtension_sourceRep a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨N.sourceRep (N.alphaCStar.symm b), ⟨_, rfl⟩, ?_⟩
    rw [N.normalExtension_sourceRep, StarAlgEquiv.apply_symm_apply]

/-- **Transport of the represented range, read on operators.**  Representing the
image of the lifted source GNS elements yields exactly the range of the target
GNS representation. -/
theorem represented_image_sourceRepRange :
    (fun T => N.targetRepresentation (N.normalExtension T)) '' Set.range N.sourceRep =
      Set.range N.bridge.targetGNSRepresentation := by
  ext S
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨N.alphaCStar a, by
      rw [← N.targetRep_spec, ← N.normalExtension_sourceRep a]⟩
  · rintro ⟨b, rfl⟩
    refine ⟨N.sourceRep (N.alphaCStar.symm b), ⟨_, rfl⟩, ?_⟩
    show N.targetRepresentation (N.normalExtension (N.sourceRep (N.alphaCStar.symm b))) = _
    rw [N.normalExtension_sourceRep, N.targetRep_spec, StarAlgEquiv.apply_symm_apply]

/-- The range of the source lift is represented by the range of the source GNS
representation. -/
theorem represented_sourceRepRange :
    N.sourceRepresentation '' Set.range N.sourceRep =
      Set.range N.bridge.sourceGNSRepresentation := by
  ext S
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (N.sourceRep_spec a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨N.sourceRep a, ⟨a, rfl⟩, N.sourceRep_spec a⟩

/-! ## Transport of the algebraic centralizers -/

theorem coe_normalExtension_toMulEquiv :
    ⇑N.normalExtension.toMulEquiv = ⇑N.normalExtension := rfl

/-- **Transport of the algebraic centralizer (commutant)** computed inside the
supplied represented algebras. -/
theorem image_centralizer :
    N.normalExtension '' (Set.range N.sourceRep).centralizer =
      (Set.range N.targetRep).centralizer := by
  rw [← N.image_sourceRepRange, ← coe_normalExtension_toMulEquiv]
  exact BoundedStateGNS.image_centralizer_of_mulEquiv N.normalExtension.toMulEquiv _

/-- **Transport of the algebraic bicentralizer** computed inside the supplied
represented algebras. -/
theorem image_centralizer_centralizer :
    N.normalExtension '' (Set.range N.sourceRep).centralizer.centralizer =
      (Set.range N.targetRep).centralizer.centralizer := by
  rw [← N.image_centralizer, ← coe_normalExtension_toMulEquiv]
  exact BoundedStateGNS.image_centralizer_of_mulEquiv N.normalExtension.toMulEquiv _

/-- Commutation with all lifted source GNS elements transports to commutation
with all lifted target GNS elements. -/
theorem commute_iff (T : N.SourceVN) :
    (∀ a : N.bridge.SourceCStar, Commute T (N.sourceRep a)) ↔
      ∀ b : N.bridge.TargetCStar, Commute (N.normalExtension T) (N.targetRep b) := by
  constructor
  · intro hT b
    have h := congrArg N.normalExtension (hT (N.alphaCStar.symm b))
    rw [map_mul, map_mul, N.normalExtension_sourceRep,
      StarAlgEquiv.apply_symm_apply] at h
    exact h
  · intro hT a
    have h := hT (N.alphaCStar a)
    rw [← N.normalExtension_sourceRep a] at h
    have h' := congrArg N.normalExtension.symm h
    rwa [map_mul, map_mul, StarAlgEquiv.symm_apply_apply,
      StarAlgEquiv.symm_apply_apply] at h'

/-! ## Pullback of supplied normal functionals -/

/-- **Pullback of a functional** along the supplied extension. -/
noncomputable def pullback (psi : N.TargetVN →ₗ[ℂ] ℂ) : N.SourceVN →ₗ[ℂ] ℂ :=
  psi ∘ₗ N.normalExtension.toAlgEquiv.toLinearMap

/-- **Pushforward of a functional** along the inverse of the supplied
extension. -/
noncomputable def pushforward (phi : N.SourceVN →ₗ[ℂ] ℂ) : N.TargetVN →ₗ[ℂ] ℂ :=
  phi ∘ₗ N.normalExtension.symm.toAlgEquiv.toLinearMap

@[simp] theorem pullback_apply (psi : N.TargetVN →ₗ[ℂ] ℂ) (T : N.SourceVN) :
    N.pullback psi T = psi (N.normalExtension T) := rfl

@[simp] theorem pushforward_apply (phi : N.SourceVN →ₗ[ℂ] ℂ) (T : N.TargetVN) :
    N.pushforward phi T = phi (N.normalExtension.symm T) := rfl

/-- **Pullback of a supplied normal functional is a supplied normal
functional.** -/
theorem pullback_normal (psi : N.TargetVN →ₗ[ℂ] ℂ) (h : N.IsNormalTargetFunctional psi) :
    N.IsNormalSourceFunctional (N.pullback psi) :=
  N.normal_pullback psi _ (fun _ => rfl) h

/-- The pullback of a functional is computed on lifted GNS elements through the
C⋆-level equivalence `alphaCStar`. -/
theorem pullback_sourceRep (psi : N.TargetVN →ₗ[ℂ] ℂ) (a : N.bridge.SourceCStar) :
    N.pullback psi (N.sourceRep a) = psi (N.targetRep (N.alphaCStar a)) := by
  rw [pullback_apply, N.normalExtension_sourceRep]

/-- Pullback preserves unitality. -/
theorem pullback_one (psi : N.TargetVN →ₗ[ℂ] ℂ) (h : psi 1 = 1) : N.pullback psi 1 = 1 := by
  rw [pullback_apply, map_one, h]

/-- Pullback along the supplied extension is injective. -/
theorem pullback_injective : Function.Injective N.pullback := by
  intro psi psi' h
  ext T
  have h' := LinearMap.congr_fun h (N.normalExtension.symm T)
  simpa using h'

theorem pushforward_pullback (psi : N.TargetVN →ₗ[ℂ] ℂ) :
    N.pushforward (N.pullback psi) = psi := by
  ext T; simp

theorem pullback_pushforward (phi : N.SourceVN →ₗ[ℂ] ℂ) :
    N.pullback (N.pushforward phi) = phi := by
  ext T; simp

end NormalExtensionData

/-! ## The packaged interface theorem -/

/-- **The P27 interface theorem.**  For supplied represented algebras, a
supplied star-algebra equivalence between them extending the P26 C⋆/GNS-level
conjugation, and supplied normality predicates with the supplied normality of
the extension, one obtains formally:

* the represented-element formula and the transport of represented ranges, both
  inside the supplied algebras and after representing as operators;
* transport of the algebraic centralizer and bicentralizer computed inside the
  represented algebras; and
* pullback of supplied normal functionals, preserving the supplied normality
  predicate and unitality, injective, with pushforward along the inverse as a
  two-sided inverse.

Everything is conditional on the supplied data.  No von Neumann closure or
normal extension is constructed, and no quasi-equivalence, tensor product,
hyperfiniteness, factor type, trace or weight is claimed. -/
theorem normal_extension_interface_package (N : NormalExtensionData) :
    (∀ a : N.bridge.SourceCStar,
        N.normalExtension (N.sourceRep a) = N.targetRep (N.alphaCStar a)) ∧
      N.normalExtension '' Set.range N.sourceRep = Set.range N.targetRep ∧
      (fun T => N.targetRepresentation (N.normalExtension T)) '' Set.range N.sourceRep =
        Set.range N.bridge.targetGNSRepresentation ∧
      N.normalExtension '' (Set.range N.sourceRep).centralizer =
        (Set.range N.targetRep).centralizer ∧
      N.normalExtension '' (Set.range N.sourceRep).centralizer.centralizer =
        (Set.range N.targetRep).centralizer.centralizer ∧
      (∀ psi : N.TargetVN →ₗ[ℂ] ℂ, N.IsNormalTargetFunctional psi →
        N.IsNormalSourceFunctional (N.pullback psi)) ∧
      (∀ (psi : N.TargetVN →ₗ[ℂ] ℂ) (a : N.bridge.SourceCStar),
        N.pullback psi (N.sourceRep a) = psi (N.targetRep (N.alphaCStar a))) ∧
      Function.Injective N.pullback :=
  ⟨N.normalExtension_sourceRep, N.image_sourceRepRange, N.represented_image_sourceRepRange,
    N.image_centralizer, N.image_centralizer_centralizer, N.pullback_normal,
    N.pullback_sourceRep, N.pullback_injective⟩

/-! ## A sanity instance

The interface is not vacuous: over the P26 `trivialAlphaGNSData` we may take
both represented algebras to be the full bounded-operator algebras of the two
GNS spaces, represented by the identity, with the supplied extension the P26
conjugation `gnsConjStarAlgEquiv` and both normality predicates trivially true.
This is a consistency check on the bundle, not a model of the manuscript's
regional algebras. -/

/-- A one-stage instance of `NormalExtensionData`, showing all fields can be met
simultaneously. -/
noncomputable def trivialNormalExtensionData : NormalExtensionData where
  bridge := trivialAlphaGNSData
  SourceVN := trivialAlphaGNSData.sourceGNS →L[ℂ] trivialAlphaGNSData.sourceGNS
  TargetVN := trivialAlphaGNSData.targetGNS →L[ℂ] trivialAlphaGNSData.targetGNS
  sourceRepresentation := StarAlgHom.id ℂ _
  sourceRepresentation_injective := fun _ _ h => h
  targetRepresentation := StarAlgHom.id ℂ _
  targetRepresentation_injective := fun _ _ h => h
  sourceRep := trivialAlphaGNSData.sourceGNSRepresentation
  sourceRep_spec := fun _ => rfl
  targetRep := trivialAlphaGNSData.targetGNSRepresentation
  targetRep_spec := fun _ => rfl
  normalExtension := trivialAlphaGNSData.gnsConjStarAlgEquiv
  normalExtension_extends := fun _ => rfl
  IsNormalSourceFunctional := fun _ => True
  IsNormalTargetFunctional := fun _ => True
  normal_pullback := fun _ _ _ _ => trivial

end NormalVonNeumannExtensionInterface

end AristotleCandidates
