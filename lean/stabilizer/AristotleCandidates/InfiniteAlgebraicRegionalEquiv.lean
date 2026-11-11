import Formalization.AlgebraicLimitStarHom
import Formalization.PhaseCorrectedWordBasisEquiv

/-!
# The infinite algebraic regional equivalence interface

Context declaration: source basis `main.tex:1915-1924`, where a map
`alpha : P_I → A_Γ` from an infinite Pauli algebra to a regional algebra is
*proposed*.  This module formalizes only the algebraic direct-limit step of
that proposal.

## What is supplied and what is derived

Everything needed for `alpha` is **supplied input**, bundled in the structure
`RegionalLimitData`:

* an index type of finite stages, directed and nonempty;
* a directed system `Source` of finite source Pauli/star algebras over `ℂ`
  with its connecting star-algebra maps `sourceConnecting`;
* a directed system `Target` of finite target regional/star algebras over `ℂ`
  with its connecting star-algebra maps `targetConnecting`;
* a family `stageEquiv i : Source i ≃⋆ₐ[ℂ] Target i` of finite-stage complex
  star-algebra equivalences; and
* the *exact* compatibility `stageEquiv_connecting` of those equivalences with
  every connecting map of the two systems.

From this data — and from nothing else — `RegionalLimitData.alpha` is defined
as the induced star-algebra equivalence of the two algebraic direct limits, via
`StabilizerHyperfinite.algebraicLimitStarAlgEquiv`.  Its value on every
finite-stage representative (`alpha_of`), the corresponding formulas for the
inverse (`alpha_symm_of`), and uniqueness from the finite-stage formulas
(`alpha_unique`, `alpha_hom_unique`, `alpha_symm_unique`) are proved.

For convenience, `stageEquivOfWordData` exposes a constructor of a single
finite-stage equivalence out of finite Pauli-word basis and phase data through
`StabilizerHyperfinite.phaseCorrectedStarAlgEquivOfBasis`, and `ofWordData`
assembles a `RegionalLimitData` from stagewise word data.  All cocycle
(multiplication/involution) equations, the basis equation, unitality and the
word-image equation remain explicit hypotheses, as does the compatibility with
the connecting maps.

## What is *not* claimed

The hypotheses above are genuine auxiliary assumptions.  They are **not**
obtained merely from the manuscript's adapted symplectic basis or from its
finite-support condition: an adapted symplectic basis controls commutators of
Pauli words, not a chosen multiplier convention, and a finite-support condition
does not by itself produce finite-stage star-algebra equivalences, let alone
their coherence with the connecting maps.  No gLU condition, refinement scheme
or layer-coherence hypothesis is used anywhere in this file.

The content of this file is purely algebraic.  In particular none of the
following analytic or operator-algebraic steps is formalized or claimed here:

1. any C⋆-norm estimate, boundedness or continuity of `alpha`;
2. the extension of `alpha` to the C⋆-completions of the two algebraic limits;
3. normality of any extension, or existence of a normal extension to weak
   closures;
4. any identification with a spatial (or any other) tensor product;
5. any von Neumann bicommutant statement;
6. quasi-equivalence of representations, or unitary implementability;
7. hyperfiniteness of any resulting von Neumann algebra;
8. any factor type classification; and
9. the existence, faithfulness, normality or semifiniteness of a trace or
   weight.
-/

namespace StabilizerHyperfinite

namespace InfiniteAlgebraicRegionalEquiv

/-- The supplied data for the infinite **algebraic** regional equivalence: two
directed systems of finite complex star algebras, a family of finite-stage
star-algebra equivalences between them, and the exact compatibility of that
family with every connecting map.

All fields are inputs.  Nothing in this structure is derived from an adapted
symplectic basis or from a finite-support condition. -/
structure RegionalLimitData where
  /-- The index type of finite stages. -/
  Index : Type*
  [indexPreorder : Preorder Index]
  [indexDirected : IsDirectedOrder Index]
  [indexNonempty : Nonempty Index]
  /-- The finite source Pauli/star algebras. -/
  Source : Index → Type*
  /-- The finite target regional/star algebras. -/
  Target : Index → Type*
  [sourceSemiring : ∀ i, Semiring (Source i)]
  [sourceStar : ∀ i, StarRing (Source i)]
  [sourceAlgebra : ∀ i, Algebra ℂ (Source i)]
  [targetSemiring : ∀ i, Semiring (Target i)]
  [targetStar : ∀ i, StarRing (Target i)]
  [targetAlgebra : ∀ i, Algebra ℂ (Target i)]
  /-- The supplied connecting star-algebra maps of the source system. -/
  sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j
  /-- The supplied connecting star-algebra maps of the target system. -/
  targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j
  [sourceDirected : DirectedSystem Source (fun i j le => sourceConnecting i j le)]
  [targetDirected : DirectedSystem Target (fun i j le => targetConnecting i j le)]
  /-- The supplied finite-stage complex star-algebra equivalences. -/
  stageEquiv : ∀ i, Source i ≃⋆ₐ[ℂ] Target i
  /-- Exact compatibility of the finite-stage equivalences with every
  connecting map of the two systems. -/
  stageEquiv_connecting : ∀ (i j : Index) (le : i ≤ j) (x : Source i),
    stageEquiv j (sourceConnecting i j le x) = targetConnecting i j le (stageEquiv i x)

attribute [instance] RegionalLimitData.indexPreorder RegionalLimitData.indexDirected
  RegionalLimitData.indexNonempty RegionalLimitData.sourceSemiring
  RegionalLimitData.sourceStar RegionalLimitData.sourceAlgebra
  RegionalLimitData.targetSemiring RegionalLimitData.targetStar
  RegionalLimitData.targetAlgebra RegionalLimitData.sourceDirected
  RegionalLimitData.targetDirected

namespace RegionalLimitData

variable (D : RegionalLimitData)

/-- The algebraic direct limit of the source system; the algebraic model of
`P_I`. -/
abbrev SourceLimit : Type _ :=
  DirectLimit D.Source (fun i j le => D.sourceConnecting i j le)

/-- The algebraic direct limit of the target system; the algebraic model of
`A_Γ`. -/
abbrev TargetLimit : Type _ :=
  DirectLimit D.Target (fun i j le => D.targetConnecting i j le)

/-- The canonical map of a finite source stage into the source limit. -/
noncomputable abbrev sourceOf (i : D.Index) (x : D.Source i) : D.SourceLimit :=
  DirectLimit.Module.of ℂ D.Index D.Source (fun i j le => D.sourceConnecting i j le) i x

/-- The canonical map of a finite target stage into the target limit. -/
noncomputable abbrev targetOf (i : D.Index) (y : D.Target i) : D.TargetLimit :=
  DirectLimit.Module.of ℂ D.Index D.Target (fun i j le => D.targetConnecting i j le) i y

/-- **The infinite algebraic regional equivalence `alpha`.**

This is *not* a construction of the manuscript's regional map: it is the
star-algebra equivalence of algebraic direct limits induced by the supplied,
exactly compatible finite-stage equivalences `D.stageEquiv`. -/
noncomputable def alpha : D.SourceLimit ≃⋆ₐ[ℂ] D.TargetLimit :=
  algebraicLimitStarAlgEquiv
    (A := D.Source) (f := fun i j le => D.sourceConnecting i j le)
    (D := D.Target) (h := fun i j le => D.targetConnecting i j le)
    D.stageEquiv D.stageEquiv_connecting

/-- **Finite-stage formula.**  On the image of a finite stage, `alpha` is the
supplied finite-stage equivalence. -/
@[simp]
theorem alpha_of (i : D.Index) (x : D.Source i) :
    D.alpha (D.sourceOf i x) = D.targetOf i (D.stageEquiv i x) :=
  rfl

/-- The finite-stage formulas determine at most one star-algebra *homomorphism*
out of the source limit. -/
theorem alpha_hom_unique (psi : D.SourceLimit →⋆ₐ[ℂ] D.TargetLimit)
    (h_psi : ∀ (i : D.Index) (x : D.Source i),
      psi (D.sourceOf i x) = D.targetOf i (D.stageEquiv i x)) :
    ∀ z, psi z = D.alpha z := by
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
    change psi (D.sourceOf i x) = D.alpha (D.sourceOf i x)
    rw [alpha_of, h_psi]

/-- **Uniqueness.**  A star-algebra equivalence of the two algebraic limits
satisfying the finite-stage formulas is `alpha`. -/
theorem alpha_unique (psi : D.SourceLimit ≃⋆ₐ[ℂ] D.TargetLimit)
    (h_psi : ∀ (i : D.Index) (x : D.Source i),
      psi (D.sourceOf i x) = D.targetOf i (D.stageEquiv i x)) :
    psi = D.alpha := by
  apply StarAlgEquiv.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
    change psi (D.sourceOf i x) = D.alpha (D.sourceOf i x)
    rw [alpha_of, h_psi]

/-- **Inverse-stage formula.**  On the image of a finite target stage, the
inverse of `alpha` is the inverse of the supplied finite-stage equivalence. -/
@[simp]
theorem alpha_symm_of (i : D.Index) (y : D.Target i) :
    D.alpha.symm (D.targetOf i y) = D.sourceOf i ((D.stageEquiv i).symm y) := by
  have h_forward : D.alpha (D.sourceOf i ((D.stageEquiv i).symm y)) = D.targetOf i y := by
    rw [alpha_of, (D.stageEquiv i).apply_symm_apply]
  rw [← h_forward, StarAlgEquiv.symm_apply_apply]

/-- The inverse-stage formula in the other direction: `alpha.symm` undoes the
finite-stage equivalence. -/
theorem alpha_symm_of_stageEquiv (i : D.Index) (x : D.Source i) :
    D.alpha.symm (D.targetOf i (D.stageEquiv i x)) = D.sourceOf i x := by
  rw [alpha_symm_of, (D.stageEquiv i).symm_apply_apply]

/-- **Uniqueness of the inverse.**  A star-algebra equivalence of the two
algebraic limits satisfying the inverse-stage formulas is `alpha.symm`. -/
theorem alpha_symm_unique (chi : D.TargetLimit ≃⋆ₐ[ℂ] D.SourceLimit)
    (h_chi : ∀ (i : D.Index) (y : D.Target i),
      chi (D.targetOf i y) = D.sourceOf i ((D.stageEquiv i).symm y)) :
    chi = D.alpha.symm := by
  apply StarAlgEquiv.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i y =>
    change chi (D.targetOf i y) = D.alpha.symm (D.targetOf i y)
    rw [alpha_symm_of, h_chi]

/-- The inverse finite-stage equivalences are themselves exactly compatible
with the connecting maps.  (A consequence of the supplied compatibility, not an
extra assumption.) -/
theorem stageEquiv_symm_connecting (i j : D.Index) (le : i ≤ j) (y : D.Target i) :
    (D.stageEquiv j).symm (D.targetConnecting i j le y) =
      D.sourceConnecting i j le ((D.stageEquiv i).symm y) := by
  have h := D.stageEquiv_connecting i j le ((D.stageEquiv i).symm y)
  rw [(D.stageEquiv i).apply_symm_apply] at h
  exact (D.stageEquiv j).symm_apply_eq.mpr h.symm

end RegionalLimitData

/-!
### Finite-stage equivalences from Pauli-word basis and phase data

The following optional constructor produces one finite-stage star-algebra
equivalence from word/phase data.  Every cocycle, basis, unitality and
word-image hypothesis is explicit; none of them is derived from a symplectic
condition.
-/

section WordBasis

variable {V W A B : Type*}
variable [AddCommGroup V] [AddCommGroup W]
variable [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- A finite-stage star-algebra equivalence built from supplied Pauli-word
basis and phase data, through `phaseCorrectedStarAlgEquivOfBasis`. -/
noncomputable def stageEquivOfWordData
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (labelMap : V →+ W) (phase : V → ℂ)
    (h_mul : PauliWordStarSystem.MultiplicationCompatibleBetween
      source target labelMap phase)
    (h_star : PauliWordStarSystem.StarCompatibleBetween source target labelMap phase)
    (map : A ≃ₗ[ℂ] B) (basis : Module.Basis V ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : map 1 = 1)
    (h_word : ∀ v, map (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap phase v) :
    A ≃⋆ₐ[ℂ] B :=
  phaseCorrectedStarAlgEquivOfBasis source target labelMap phase h_mul h_star
    map basis h_basis h_one h_word

@[simp]
theorem stageEquivOfWordData_apply
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (labelMap : V →+ W) (phase : V → ℂ)
    (h_mul : PauliWordStarSystem.MultiplicationCompatibleBetween
      source target labelMap phase)
    (h_star : PauliWordStarSystem.StarCompatibleBetween source target labelMap phase)
    (map : A ≃ₗ[ℂ] B) (basis : Module.Basis V ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : map 1 = 1)
    (h_word : ∀ v, map (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap phase v)
    (x : A) :
    stageEquivOfWordData source target labelMap phase h_mul h_star map basis
      h_basis h_one h_word x = map x :=
  rfl

/-- On a source Pauli word the constructed finite-stage equivalence is the
phase-corrected target word. -/
theorem stageEquivOfWordData_word
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (labelMap : V →+ W) (phase : V → ℂ)
    (h_mul : PauliWordStarSystem.MultiplicationCompatibleBetween
      source target labelMap phase)
    (h_star : PauliWordStarSystem.StarCompatibleBetween source target labelMap phase)
    (map : A ≃ₗ[ℂ] B) (basis : Module.Basis V ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : map 1 = 1)
    (h_word : ∀ v, map (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap phase v)
    (v : V) :
    stageEquivOfWordData source target labelMap phase h_mul h_star map basis
      h_basis h_one h_word (source.word v) = phase v • target.word (labelMap v) :=
  h_word v

end WordBasis

/-- Assembling `RegionalLimitData` from stagewise Pauli-word data.  The two
directed systems, all cocycle and basis hypotheses, and the compatibility
`h_compat` of the stagewise linear maps with the connecting maps are supplied
explicitly. -/
noncomputable def ofWordData
    {Index : Type*} [Preorder Index] [IsDirectedOrder Index] [Nonempty Index]
    {Source Target : Index → Type*}
    [∀ i, Semiring (Source i)] [∀ i, StarRing (Source i)] [∀ i, Algebra ℂ (Source i)]
    [∀ i, StarModule ℂ (Source i)]
    [∀ i, Semiring (Target i)] [∀ i, StarRing (Target i)] [∀ i, Algebra ℂ (Target i)]
    [∀ i, StarModule ℂ (Target i)]
    (sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j)
    (targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j)
    [DirectedSystem Source (fun i j le => sourceConnecting i j le)]
    [DirectedSystem Target (fun i j le => targetConnecting i j le)]
    {SourceLabel TargetLabel : Index → Type*}
    [∀ i, AddCommGroup (SourceLabel i)] [∀ i, AddCommGroup (TargetLabel i)]
    (sourceWords : ∀ i, PauliWordStarSystem (SourceLabel i) (Source i))
    (targetWords : ∀ i, PauliWordStarSystem (TargetLabel i) (Target i))
    (labelMap : ∀ i, SourceLabel i →+ TargetLabel i)
    (phase : ∀ i, SourceLabel i → ℂ)
    (h_mul : ∀ i, PauliWordStarSystem.MultiplicationCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (h_star : ∀ i, PauliWordStarSystem.StarCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (map : ∀ i, Source i ≃ₗ[ℂ] Target i)
    (basis : ∀ i, Module.Basis (SourceLabel i) ℂ (Source i))
    (h_basis : ∀ i v, basis i v = (sourceWords i).word v)
    (h_one : ∀ i, map i 1 = 1)
    (h_word : ∀ i v, map i ((sourceWords i).word v) =
      PauliWordStarSystem.correctedWordBetween (targetWords i) (labelMap i) (phase i) v)
    (h_compat : ∀ (i j : Index) (le : i ≤ j) (x : Source i),
      map j (sourceConnecting i j le x) = targetConnecting i j le (map i x)) :
    RegionalLimitData where
  Index := Index
  Source := Source
  Target := Target
  sourceConnecting := sourceConnecting
  targetConnecting := targetConnecting
  stageEquiv := fun i =>
    stageEquivOfWordData (sourceWords i) (targetWords i) (labelMap i) (phase i)
      (h_mul i) (h_star i) (map i) (basis i) (h_basis i) (h_one i) (h_word i)
  stageEquiv_connecting := h_compat

/-!
### A sanity instance

The interface is not vacuous: the one-stage system with source and target both
`ℂ`, identity connecting maps and the identity stage equivalence satisfies every
field.  This is a consistency check on the bundle, not a model of the
manuscript's regional algebras.
-/

/-- A one-stage instance of `RegionalLimitData`, showing all fields can be met
simultaneously. -/
noncomputable def trivialData : RegionalLimitData where
  Index := Unit
  Source := fun _ => ℂ
  Target := fun _ => ℂ
  sourceConnecting := fun _ _ _ => StarAlgHom.id ℂ ℂ
  targetConnecting := fun _ _ _ => StarAlgHom.id ℂ ℂ
  sourceDirected := ⟨by intros; rfl, by intros; rfl⟩
  targetDirected := ⟨by intros; rfl, by intros; rfl⟩
  stageEquiv := fun _ => StarAlgEquiv.refl
  stageEquiv_connecting := fun _ _ _ _ => rfl

end InfiniteAlgebraicRegionalEquiv

end StabilizerHyperfinite
