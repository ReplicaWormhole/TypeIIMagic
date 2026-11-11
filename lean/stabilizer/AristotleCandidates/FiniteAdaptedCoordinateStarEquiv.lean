import Formalization.PhaseCorrectedWordBasisEquiv
import Formalization.SymplecticCoordinates

/-!
# The finite adapted-coordinate Pauli star equivalence

Context declaration: source basis `main.tex:1671-1679` (the local/adapted
symplectic basis with finite support) and `main.tex:1915-1920` (the *proposed*
star isomorphism from a Pauli algebra to a regional algebra).  This module
formalizes only the finite-stage, purely algebraic step of that proposal.

## What is supplied and what is derived

Everything is **supplied input**, bundled in `FiniteAdaptedCoordinateStarData`:

* finite adapted coordinate data, i.e. a finite index type `I` together with an
  `AdaptedPauliCoordinateBasis` identifying finitely supported X/Z coordinate
  labels with the source label group `V`;
* a source Pauli-word star system in `A` and a target Pauli-word star system in
  `B`, each with its chosen multiplier and involution phases;
* the source Pauli words form a complex linear basis of `A` (`wordBasis`) and
  the target Pauli words form a complex linear basis of `B` (`targetBasis`);
* an additive label map `labelMap : V →+ W` and an explicit phase correction
  `phase : V → ℂ`;
* the two *exact* compatibility equations for that phase — the multiplier
  equation `mulCompatible` and the involution equation `starCompatible`,
  both stated in the finite coordinate labels; and
* a complex-linear equivalence `linearMap : A ≃ₗ[ℂ] B` which is unital and
  whose value on every source Pauli word is the phase-corrected target word.

From this data — and from nothing else — `starEquiv` is *constructed* through
`StabilizerHyperfinite.phaseCorrectedStarAlgEquivOfBasis`.  It is not a field
of the structure.  Its explicit Pauli-word formula (`starEquiv_word`), the
formulas on the adapted coordinate labels (`starEquiv_coordinateWord`,
`starEquiv_zWord`, `starEquiv_xWord`), the inverse formulas and uniqueness from
the word formula are proved.

## What is *not* claimed

The two compatibility equations are genuine auxiliary assumptions.  They are
**not** consequences of symplecticity of the coordinate map: a symplectic form
controls commutators of Pauli words, whereas the equations above compare the
chosen multiplier and involution conventions of the two word systems.  No gLU
condition, refinement scheme, layer-coherence hypothesis, C⋆-norm, completion,
continuity, normality or von Neumann statement is used or claimed anywhere in
this file; the content is finite-stage algebra only.
-/

namespace StabilizerHyperfinite

namespace FiniteAdaptedCoordinate

open PauliWordStarSystem

section

variable (I V W A B : Type*)
variable [AddCommGroup V] [Module PauliBit V] [AddCommGroup W]
variable [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- The supplied finite adapted-coordinate data for one stage of the proposed
Pauli/regional star isomorphism.

All fields are inputs.  In particular the multiplier equation `mulCompatible`
and the involution equation `starCompatible` are assumptions about the chosen
phase, not consequences of the adapted symplectic coordinates. -/
structure FiniteAdaptedCoordinateStarData where
  /-- The coordinate index set is finite. -/
  [indexFinite : Finite I]
  /-- The finite adapted X/Z coordinate basis of the source label group. -/
  coordinates : AdaptedPauliCoordinateBasis (I := I) (V := V)
  /-- The source Pauli-word star system, labelled by `V`. -/
  source : PauliWordStarSystem V A
  /-- The target Pauli-word star system, labelled by `W`. -/
  target : PauliWordStarSystem W B
  /-- The source Pauli words form a complex linear basis of `A`. -/
  wordBasis : Module.Basis V ℂ A
  /-- That basis is the source Pauli-word family. -/
  wordBasis_apply : ∀ v, wordBasis v = source.word v
  /-- The target Pauli words form a complex linear basis of `B`. -/
  targetBasis : Module.Basis W ℂ B
  /-- That basis is the target Pauli-word family. -/
  targetBasis_apply : ∀ w, targetBasis w = target.word w
  /-- The supplied additive label map on coordinate labels. -/
  labelMap : V →+ W
  /-- The supplied explicit phase correction. -/
  phase : V → ℂ
  /-- The exact multiplier equation for the supplied phase. -/
  mulCompatible : MultiplicationCompatibleBetween source target labelMap phase
  /-- The exact involution equation for the supplied phase. -/
  starCompatible : StarCompatibleBetween source target labelMap phase
  /-- The supplied complex-linear equivalence of the two finite algebras. -/
  linearMap : A ≃ₗ[ℂ] B
  /-- It is unital. -/
  linearMap_one : linearMap 1 = 1
  /-- Its value on each source Pauli word is the phase-corrected target word. -/
  linearMap_word : ∀ v, linearMap (source.word v) =
    correctedWordBetween target labelMap phase v

end

namespace FiniteAdaptedCoordinateStarData

section

variable {I V W A B : Type*}
variable [AddCommGroup V] [Module PauliBit V] [AddCommGroup W]
variable [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
variable (D : FiniteAdaptedCoordinateStarData I V W A B)

/-- **The finite-stage star-algebra equivalence.**  It is *constructed* from
the supplied word, basis and phase data through
`phaseCorrectedStarAlgEquivOfBasis`; it is not an assumed `StarAlgEquiv`. -/
noncomputable def starEquiv : A ≃⋆ₐ[ℂ] B :=
  phaseCorrectedStarAlgEquivOfBasis D.source D.target D.labelMap D.phase
    D.mulCompatible D.starCompatible D.linearMap D.wordBasis D.wordBasis_apply
    D.linearMap_one D.linearMap_word

/-- The constructed equivalence has the supplied linear map as its underlying
function. -/
@[simp]
theorem starEquiv_apply (x : A) : D.starEquiv x = D.linearMap x := rfl

/-- **The explicit Pauli-word formula.**  On each source Pauli word the
finite-stage equivalence is the phase-corrected target Pauli word. -/
theorem starEquiv_word (v : V) :
    D.starEquiv (D.source.word v) = D.phase v • D.target.word (D.labelMap v) :=
  D.linearMap_word v

/-- The Pauli-word formula written with the phase-corrected target word. -/
theorem starEquiv_correctedWord (v : V) :
    D.starEquiv (D.source.word v) =
      correctedWordBetween D.target D.labelMap D.phase v :=
  D.linearMap_word v

/-- The Pauli-word formula in the two word bases. -/
theorem starEquiv_wordBasis (v : V) :
    D.starEquiv (D.wordBasis v) = D.phase v • D.targetBasis (D.labelMap v) := by
  rw [D.wordBasis_apply, D.targetBasis_apply, starEquiv_word]

/-- **The adapted-coordinate formula.**  On the source Pauli word labelled by a
finitely supported X/Z coordinate word, the equivalence is the phase-corrected
target word of the corresponding label. -/
theorem starEquiv_coordinateWord (c : PauliCoordinateLabels I) :
    D.starEquiv (D.source.word (D.coordinates.coordinateLabelEquiv c)) =
      D.phase (D.coordinates.coordinateLabelEquiv c) •
        D.target.word (D.labelMap (D.coordinates.coordinateLabelEquiv c)) :=
  D.starEquiv_word _

/-- The formula on the Pauli word of a single adapted Z coordinate. -/
theorem starEquiv_zWord (i : I) :
    D.starEquiv (D.source.word (D.coordinates.z i)) =
      D.phase (D.coordinates.z i) • D.target.word (D.labelMap (D.coordinates.z i)) :=
  D.starEquiv_word _

/-- The formula on the Pauli word of a single adapted X coordinate. -/
theorem starEquiv_xWord (i : I) :
    D.starEquiv (D.source.word (D.coordinates.x i)) =
      D.phase (D.coordinates.x i) • D.target.word (D.labelMap (D.coordinates.x i)) :=
  D.starEquiv_word _

/-- The formula on the Pauli word of a single adapted Z coordinate, written
through the coordinate-label equivalence. -/
theorem starEquiv_zCoordinate (i : I) :
    D.starEquiv
        (D.source.word (D.coordinates.coordinateLabelEquiv (Finsupp.single (Sum.inl i) 1))) =
      D.phase (D.coordinates.z i) • D.target.word (D.labelMap (D.coordinates.z i)) := by
  rw [D.coordinates.coordinateLabelEquiv_z i]
  exact D.starEquiv_word _

/-- The formula on the Pauli word of a single adapted X coordinate, written
through the coordinate-label equivalence. -/
theorem starEquiv_xCoordinate (i : I) :
    D.starEquiv
        (D.source.word (D.coordinates.coordinateLabelEquiv (Finsupp.single (Sum.inr i) 1))) =
      D.phase (D.coordinates.x i) • D.target.word (D.labelMap (D.coordinates.x i)) := by
  rw [D.coordinates.coordinateLabelEquiv_x i]
  exact D.starEquiv_word _

/-- **The inverse word formula.**  The inverse equivalence sends the
phase-corrected target word back to the source Pauli word. -/
theorem starEquiv_symm_correctedWord (v : V) :
    D.starEquiv.symm (D.phase v • D.target.word (D.labelMap v)) = D.source.word v := by
  rw [← D.starEquiv_word v, StarAlgEquiv.symm_apply_apply]

/-- If the phase is nonvanishing, the inverse equivalence recovers each source
Pauli word from the corresponding target Pauli word. -/
theorem starEquiv_symm_targetWord (h_phase : ∀ v, D.phase v ≠ 0) (v : V) :
    D.starEquiv.symm (D.target.word (D.labelMap v)) = (D.phase v)⁻¹ • D.source.word v := by
  have h := D.starEquiv_symm_correctedWord v
  rw [map_smul] at h
  rw [← h, smul_smul, inv_mul_cancel₀ (h_phase v), one_smul]

/-- **Uniqueness.**  A star-algebra equivalence with the same Pauli-word
formula is the constructed one. -/
theorem starEquiv_unique (psi : A ≃⋆ₐ[ℂ] B)
    (h_psi : ∀ v, psi (D.source.word v) = D.phase v • D.target.word (D.labelMap v)) :
    psi = D.starEquiv := by
  have h_lin : psi.toAlgEquiv.toLinearMap = D.starEquiv.toAlgEquiv.toLinearMap := by
    apply D.wordBasis.ext
    intro v
    show psi (D.wordBasis v) = D.starEquiv (D.wordBasis v)
    rw [D.wordBasis_apply, h_psi v, D.starEquiv_word]
  apply StarAlgEquiv.ext
  intro x
  exact congrArg (fun f => f x) (congrArg (fun f : A →ₗ[ℂ] B => (f : A → B)) h_lin)

/-- With a nonvanishing phase, the supplied label map is injective: two source
words with the same target label would give a dependent pair in the image
basis. -/
theorem labelMap_injective (h_phase : ∀ v, D.phase v ≠ 0) :
    Function.Injective D.labelMap := by
  intro v₁ v₂ h
  by_contra h_ne
  set c : Module.Basis V ℂ B := D.wordBasis.map D.linearMap with hc
  have hcv : ∀ v, c v = D.phase v • D.targetBasis (D.labelMap v) := by
    intro v
    show D.linearMap (D.wordBasis v) = _
    rw [D.wordBasis_apply, D.targetBasis_apply, D.linearMap_word v]
    rfl
  have h_eq : c v₁ = (D.phase v₁ * (D.phase v₂)⁻¹) • c v₂ := by
    rw [hcv, hcv, h, smul_smul, mul_assoc, inv_mul_cancel₀ (h_phase v₂), mul_one]
  have h_repr := congrArg c.repr h_eq
  rw [c.repr_self, map_smul, c.repr_self] at h_repr
  have := congrArg (fun f : V →₀ ℂ => f v₁) h_repr
  simp [h_ne] at this

/-- The supplied label map is surjective: the target Pauli words in its image
already span the target algebra.  (No phase hypothesis is needed here.) -/
theorem labelMap_surjective : Function.Surjective D.labelMap := by
  intro w
  set c : Module.Basis V ℂ B := D.wordBasis.map D.linearMap with hc
  have hcv : ∀ v, c v = D.phase v • D.targetBasis (D.labelMap v) := by
    intro v
    show D.linearMap (D.wordBasis v) = _
    rw [D.wordBasis_apply, D.targetBasis_apply, D.linearMap_word v]
    rfl
  have h_le : Submodule.span ℂ (Set.range c) ≤
      Submodule.span ℂ (D.targetBasis '' Set.range D.labelMap) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [hcv v]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨D.labelMap v, ⟨v, rfl⟩, rfl⟩)
  have h_mem : D.targetBasis w ∈ Submodule.span ℂ (D.targetBasis '' Set.range D.labelMap) := by
    apply h_le
    rw [c.span_eq]
    exact Submodule.mem_top
  rw [Module.Basis.mem_span_image] at h_mem
  have hw : w ∈ (D.targetBasis.repr (D.targetBasis w)).support := by
    rw [D.targetBasis.repr_self]
    simp
  exact h_mem hw

/-- With a nonvanishing phase the supplied label map is bijective. -/
theorem labelMap_bijective (h_phase : ∀ v, D.phase v ≠ 0) :
    Function.Bijective D.labelMap :=
  ⟨D.labelMap_injective h_phase, D.labelMap_surjective⟩

end

end FiniteAdaptedCoordinateStarData

/-!
### A sanity instance

The bundle is not vacuous: the one-dimensional example with empty coordinate
index, trivial label groups and `A = B = ℂ` satisfies every field
simultaneously.  This is a consistency check on the interface, not a model of
the manuscript's regional algebras.
-/

/-- A trivial instance of the finite adapted-coordinate data, witnessing that
all hypotheses can be met at once. -/
noncomputable def trivialData :
    FiniteAdaptedCoordinateStarData Empty PUnit PUnit ℂ ℂ where
  coordinates :=
    { z := fun i => i.elim
      x := fun i => i.elim
      basis := Module.Basis.empty PUnit
      basis_z := fun i => i.elim
      basis_x := fun i => i.elim }
  source :=
    { word := fun _ => 1
      multiplier := fun _ _ => 1
      word_mul := by intro v w; simp
      star_multiplier := fun _ => 1
      word_star := by intro v; simp }
  target :=
    { word := fun _ => 1
      multiplier := fun _ _ => 1
      word_mul := by intro v w; simp
      star_multiplier := fun _ => 1
      word_star := by intro v; simp }
  wordBasis := Module.Basis.singleton PUnit ℂ
  wordBasis_apply := by intro v; simp
  targetBasis := Module.Basis.singleton PUnit ℂ
  targetBasis_apply := by intro w; simp
  labelMap := 0
  phase := fun _ => 1
  mulCompatible := by intro v w; simp
  starCompatible := by intro v; simp
  linearMap := LinearEquiv.refl ℂ ℂ
  linearMap_one := rfl
  linearMap_word := by
    intro v
    show (1 : ℂ) = PauliWordStarSystem.correctedWordBetween _ _ _ v
    simp [PauliWordStarSystem.correctedWordBetween]

end FiniteAdaptedCoordinate

end StabilizerHyperfinite
