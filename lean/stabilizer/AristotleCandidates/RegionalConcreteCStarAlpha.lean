import AristotleCandidates.LocalHyperbolicConcreteRepresentations

/-!
# P55D — the regional concrete C⋆ `alpha`

**Context declaration.**  Source basis: `main.tex:1915-1920` (the extension of
the algebraic coordinate isomorphism to the C⋆-completions).  All analytic
content below is proved; nothing is supplied as data.

## Plan alignment

* Package `P55D`, lane `H`; predecessors `P53`
  (`AristotleCandidates.LocalHyperbolicAlgebraicAlpha`) and `P55C`
  (`AristotleCandidates.LocalHyperbolicConcreteRepresentations`), together with
  the checked concrete completion module
  `AristotleCandidates.ConcreteCStarCompletion`
  (`Formalization.ConcreteCStarCompletion`), all imported through P55C.
* Gate discharged: extend the constructed algebraic `alpha` of P53 *uniquely*
  between the constructed source and regional concrete C⋆ closures of P55C,
  with the dense stage formulas, the inverse formulas, isometry, surjectivity
  and uniqueness.
* Forbidden downstream claims, none of which is made here: no product-state
  equality, no GNS tensor split, no identification with a state-dependent
  represented von Neumann algebra, no factor classification, no trivial-centre
  theorem and no trace or weight conclusion.

## What is constructed

For every P55C representation datum `R : A.SourceConcreteRep`:

1. `regionalEmbedding`, the canonical embedding of the algebraic source limit
   into the regional concrete C⋆-algebra through the algebraic `alpha`; it is
   proved injective, isometric for the P55C pulled-back pre-C⋆ norm, and of
   dense range.
2. `cstarAlpha : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar`, **constructed by
   density** from `Formalization.ConcreteCStarCompletion.extendStarAlgEquiv`.
   It is never a field of a structure.
3. Its formula on every source stage image (`cstarAlpha_sourceEmbedding_of`)
   and on every stage Pauli word (`cstarAlpha_sourceEmbedding_word`), the
   corresponding inverse formulas on every target stage image
   (`cstarAlpha_symm_targetEmbedding_of`,
   `cstarAlpha_symm_targetEmbedding_word`), isometry
   (`isometry_cstarAlpha`), surjectivity (`cstarAlpha_surjective`) and
   uniqueness among continuous star-algebra equivalences satisfying either the
   dense formula (`existsUnique_cstarAlpha`) or the stage word formula
   (`cstarAlpha_unique_word`).
4. The transparency lemma `coe_cstarAlpha`: since P55C *constructs* the
   regional representation by transporting the source representation through
   the algebraic `alpha`, the two closed operator ranges coincide as closed
   operator algebras and the completed `alpha` is implemented by the identity
   on operators.  This records exactly what the P55C model gives and claims
   nothing about represented von Neumann algebras.
5. The branch-uniform packaging `A.SourceConcreteCStar`,
   `A.TargetConcreteCStar` and `A.regionalCStarAlpha`, obtained from the P55C
   branch datum `A.branchSourceRep`, with the finite and infinite branch
   operator formulas.

## Auxiliary assumptions

None beyond the explicit `AlphaData` hypotheses of P53 and the finite/infinite
coordinate branch already constructed in P55C: `A.branchSourceRep` is the P55C
case split on `Finite I` versus `Infinite I`, and no representation,
faithfulness, boundedness, closure, density or extension premise is added here.
-/

namespace StabilizerHyperfinite

namespace LocalHyperbolicAlpha

namespace AlphaData

open Formalization.ConcreteCStarCompletion

variable {L I : Type*} [LinearOrder I] {A : AlphaData L I}

/-! ## 1. Word-wise rigidity of linear maps out of the algebraic source limit -/

/-- Two complex-linear maps out of the algebraic source direct limit which agree
on the image of every stage Pauli word are equal.  This is the algebraic
rigidity used for the word form of the uniqueness theorem. -/
theorem sourceLimit_linear_ext {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (A : AlphaData L I) (f g : A.SourceLimit →ₗ[ℂ] X)
    (h : ∀ (n : ℕ) (v : A.SourceLabel n),
      f (A.sourceOf n (pauliWord (A.sourceForm n) v)) =
        g (A.sourceOf n (pauliWord (A.sourceForm n) v))) :
    ∀ z, f z = g z := by
  intro z
  induction z using DirectLimit.induction with
  | _ n x =>
    show f (A.sourceOf n x) = g (A.sourceOf n x)
    exact pauliAlgebra_linear_ext (A.sourceForm n)
      (f.comp (DirectLimit.Module.of ℂ A.directedFamily.limitData.Index
        A.directedFamily.limitData.Source A.directedFamily.limitData.sourceConnecting n))
      (g.comp (DirectLimit.Module.of ℂ A.directedFamily.limitData.Index
        A.directedFamily.limitData.Source A.directedFamily.limitData.sourceConnecting n))
      (fun v => h n v) x

namespace SourceConcreteRep

variable (R : A.SourceConcreteRep)

/-! ## 2. The regional embedding of the algebraic source limit -/

/-- The canonical embedding of the algebraic source limit into the **regional**
concrete C⋆-algebra: the P55C regional embedding precomposed with the P53
algebraic `alpha`. -/
noncomputable def regionalEmbedding : A.SourceLimit →⋆ₐ[ℂ] R.targetCStar :=
  R.targetEmbedding.comp (StarAlgHomClass.toStarAlgHom A.alpha)

@[simp] theorem regionalEmbedding_apply (z : A.SourceLimit) :
    R.regionalEmbedding z = R.targetEmbedding (A.alpha z) := rfl

/-- As an operator, the regional embedding of a source element is its source
representation: the algebraic `alpha` is implemented by the identity on
operators. -/
@[simp] theorem coe_regionalEmbedding (z : A.SourceLimit) :
    (R.regionalEmbedding z : UHFGNS →L[ℂ] UHFGNS) = R.rep z := by
  simp [regionalEmbedding]

theorem regionalEmbedding_injective : Function.Injective R.regionalEmbedding :=
  R.targetEmbedding_injective.comp (EquivLike.injective A.alpha)

/-- The regional embedding has dense range, because the algebraic `alpha` is
surjective onto the algebraic regional limit. -/
theorem regionalEmbedding_denseRange : DenseRange R.regionalEmbedding := by
  have h : Set.range ⇑R.regionalEmbedding = Set.range ⇑R.targetEmbedding := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨A.alpha z, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨A.alpha.symm y, by simp⟩
  rw [DenseRange, h]
  exact R.targetEmbedding_denseRange

/-! ## 3. Isometry of the two dense embeddings for the pulled-back norm -/

/-- The canonical source embedding is isometric for the P55C pulled-back
pre-C⋆ norm on the algebraic source limit. -/
theorem isometry_sourceEmbedding :
    letI := R.sourceNormedRing
    Isometry R.sourceEmbedding := by
  letI := R.sourceNormedRing
  exact AddMonoidHomClass.isometry_of_norm _ (fun _ => rfl)

/-- The regional embedding is isometric for the same pulled-back norm; this is
the **compatibility identity on the dense algebraic ranges** that powers the
extension. -/
theorem isometry_regionalEmbedding :
    letI := R.sourceNormedRing
    Isometry R.regionalEmbedding := by
  letI := R.sourceNormedRing
  refine AddMonoidHomClass.isometry_of_norm _ (fun z => ?_)
  show ‖(R.regionalEmbedding z : UHFGNS →L[ℂ] UHFGNS)‖ = ‖R.rep z‖
  rw [coe_regionalEmbedding]

/-- Norm form of the dense compatibility identity: the source and regional
embeddings of an algebraic element have the same norm. -/
theorem norm_regionalEmbedding_eq (z : A.SourceLimit) :
    ‖R.regionalEmbedding z‖ = ‖R.sourceEmbedding z‖ := by
  show ‖(R.regionalEmbedding z : UHFGNS →L[ℂ] UHFGNS)‖ =
    ‖(R.sourceEmbedding z : UHFGNS →L[ℂ] UHFGNS)‖
  rw [coe_regionalEmbedding, R.coe_sourceEmbedding]

/-! ## 4. The completed regional C⋆ `alpha`, constructed by density -/

/-- **The regional concrete C⋆ `alpha`.**  It is *constructed*, by extending the
P53 algebraic `alpha` along the two dense isometric embeddings of P55C; it is
not accepted as data. -/
noncomputable def cstarAlpha : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar :=
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  extendStarAlgEquiv R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    R.isometry_regionalEmbedding R.regionalEmbedding_denseRange

/-- **The dense formula.**  On the concrete image of an algebraic source element
the completed `alpha` is the regional embedding of its algebraic `alpha`. -/
@[simp] theorem cstarAlpha_sourceEmbedding (z : A.SourceLimit) :
    R.cstarAlpha (R.sourceEmbedding z) = R.targetEmbedding (A.alpha z) := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact extendStarAlgEquiv_apply R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    R.isometry_regionalEmbedding R.regionalEmbedding_denseRange z

/-- Operator form of the dense formula. -/
theorem coe_cstarAlpha_sourceEmbedding (z : A.SourceLimit) :
    (R.cstarAlpha (R.sourceEmbedding z) : UHFGNS →L[ℂ] UHFGNS) = R.rep z := by
  rw [cstarAlpha_sourceEmbedding, R.coe_targetEmbedding, R.targetRep_alpha]

theorem continuous_cstarAlpha : Continuous R.cstarAlpha := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact continuous_extendStarAlgEquiv R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    R.isometry_regionalEmbedding R.regionalEmbedding_denseRange

/-- **The completed `alpha` is isometric.** -/
theorem isometry_cstarAlpha : Isometry R.cstarAlpha := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact isometry_extendStarAlgEquiv R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    R.isometry_regionalEmbedding R.regionalEmbedding_denseRange

theorem norm_cstarAlpha (T : R.sourceCStar) : ‖R.cstarAlpha T‖ = ‖T‖ :=
  (R.isometry_cstarAlpha).norm_map_of_map_zero (map_zero _) T

/-- **Surjectivity of the completed `alpha`.** -/
theorem cstarAlpha_surjective : Function.Surjective R.cstarAlpha :=
  EquivLike.surjective R.cstarAlpha

theorem cstarAlpha_injective : Function.Injective R.cstarAlpha :=
  EquivLike.injective R.cstarAlpha

theorem cstarAlpha_bijective : Function.Bijective R.cstarAlpha :=
  ⟨R.cstarAlpha_injective, R.cstarAlpha_surjective⟩

/-! ## 5. The stage formulas -/

/-- **The source stage formula.**  On the concrete image of any element of the
stage-`n` twisted Pauli algebra, the completed `alpha` is the regional
embedding of the algebraic `alpha` of that stage element. -/
theorem cstarAlpha_sourceEmbedding_of (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    R.cstarAlpha (R.sourceEmbedding (A.sourceOf n x)) =
      R.targetEmbedding (A.alpha (A.sourceOf n x)) :=
  R.cstarAlpha_sourceEmbedding _

/-- **The source stage Pauli-word formula.**  On the concrete image of a
stage-`n` Pauli word the completed `alpha` is the concrete image of the
phase-calibrated regional Pauli word of the image label. -/
theorem cstarAlpha_sourceEmbedding_word (n : ℕ) (v : A.SourceLabel n) :
    R.cstarAlpha (R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
      R.targetEmbedding
        (A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v))) := by
  rw [R.cstarAlpha_sourceEmbedding, A.alpha_word n v]

/-- **The inverse formula.**  On the concrete image of an algebraic regional
element, the inverse of the completed `alpha` is the source embedding of the
algebraic `alpha.symm`. -/
@[simp] theorem cstarAlpha_symm_targetEmbedding (y : A.TargetLimit) :
    R.cstarAlpha.symm (R.targetEmbedding y) = R.sourceEmbedding (A.alpha.symm y) := by
  refine R.cstarAlpha_injective ?_
  rw [StarAlgEquiv.apply_symm_apply, R.cstarAlpha_sourceEmbedding,
    StarAlgEquiv.apply_symm_apply]

/-- **The target stage inverse formula.** -/
theorem cstarAlpha_symm_targetEmbedding_of (n : ℕ) (y : pauliAlgebra (A.targetForm n)) :
    R.cstarAlpha.symm (R.targetEmbedding (A.targetOf n y)) =
      R.sourceEmbedding (A.alpha.symm (A.targetOf n y)) :=
  R.cstarAlpha_symm_targetEmbedding _

/-- **The target stage Pauli-word inverse formula.**  The inverse of the
completed `alpha` recovers each source Pauli word, up to the calibration phase,
from the regional Pauli word of its image label. -/
theorem cstarAlpha_symm_targetEmbedding_word (n : ℕ) (v : A.SourceLabel n) :
    R.cstarAlpha.symm
        (R.targetEmbedding (A.targetOf n (pauliWord (A.targetForm n) (A.stageLabelMap n v)))) =
      (A.phase n v)⁻¹ • R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v)) := by
  rw [R.cstarAlpha_symm_targetEmbedding, A.alpha_symm_word n v, map_smul]

/-- Operator form of the inverse formula. -/
theorem coe_cstarAlpha_symm_targetEmbedding (y : A.TargetLimit) :
    (R.cstarAlpha.symm (R.targetEmbedding y) : UHFGNS →L[ℂ] UHFGNS) = R.targetRep y := by
  rw [cstarAlpha_symm_targetEmbedding, R.coe_sourceEmbedding]
  rfl

/-- The inverse of the completed `alpha` is isometric as well. -/
theorem isometry_cstarAlpha_symm : Isometry R.cstarAlpha.symm :=
  AddMonoidHomClass.isometry_of_norm _ (fun T => by
    conv_rhs => rw [← StarAlgEquiv.apply_symm_apply R.cstarAlpha T]
    rw [R.norm_cstarAlpha])

theorem continuous_cstarAlpha_symm : Continuous R.cstarAlpha.symm :=
  R.isometry_cstarAlpha_symm.continuous

/-- **Transparency of the P55C model.**  Because P55C *constructs* the regional
representation by transporting the source representation through the algebraic
`alpha`, the two closed operator ranges are the same closed operator algebra and
the completed `alpha` is implemented by the identity map on operators.  This is
a statement about the constructed operator ranges only: no represented von
Neumann algebra, state, or tensor factorization is involved. -/
theorem coe_cstarAlpha (T : R.sourceCStar) :
    (R.cstarAlpha T : UHFGNS →L[ℂ] UHFGNS) = (T : UHFGNS →L[ℂ] UHFGNS) := by
  have hfun : (fun T : R.sourceCStar => (R.cstarAlpha T : UHFGNS →L[ℂ] UHFGNS)) =
      fun T : R.sourceCStar => (T : UHFGNS →L[ℂ] UHFGNS) := by
    refine Continuous.ext_on R.sourceEmbedding_denseRange
      (continuous_subtype_val.comp R.continuous_cstarAlpha) continuous_subtype_val ?_
    rintro _ ⟨z, rfl⟩
    exact R.coe_cstarAlpha_sourceEmbedding z
  exact congrFun hfun T

/-! ## 6. Uniqueness -/

/-- **Uniqueness from the dense formula.**  There is exactly one continuous
star-algebra equivalence of the two concrete C⋆-algebras which implements the
algebraic `alpha` on the dense algebraic ranges. -/
theorem existsUnique_cstarAlpha :
    ∃! e : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar,
      Continuous e ∧ ∀ z : A.SourceLimit, e (R.sourceEmbedding z) = R.targetEmbedding (A.alpha z) := by
  refine ⟨R.cstarAlpha, ⟨R.continuous_cstarAlpha, R.cstarAlpha_sourceEmbedding⟩, ?_⟩
  rintro e ⟨hcont, hemb⟩
  refine DFunLike.coe_injective ?_
  refine Continuous.ext_on R.sourceEmbedding_denseRange hcont R.continuous_cstarAlpha ?_
  rintro _ ⟨z, rfl⟩
  show e (R.sourceEmbedding z) = R.cstarAlpha (R.sourceEmbedding z)
  rw [hemb z, R.cstarAlpha_sourceEmbedding]

/-- Any continuous star-algebra equivalence implementing the algebraic `alpha`
on the dense algebraic ranges is the constructed one. -/
theorem cstarAlpha_unique (e : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar) (hcont : Continuous e)
    (hemb : ∀ z : A.SourceLimit, e (R.sourceEmbedding z) = R.targetEmbedding (A.alpha z)) :
    e = R.cstarAlpha :=
  (R.existsUnique_cstarAlpha).unique ⟨hcont, hemb⟩
    ⟨R.continuous_cstarAlpha, R.cstarAlpha_sourceEmbedding⟩

/-- **Uniqueness from the stage word formula.**  A continuous star-algebra
equivalence obeying the phase-calibrated Pauli-word formula on the concrete
image of every stage word is the constructed regional C⋆ `alpha`. -/
theorem cstarAlpha_unique_word (e : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar) (hcont : Continuous e)
    (hword : ∀ (n : ℕ) (v : A.SourceLabel n),
      e (R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
        R.targetEmbedding
          (A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v)))) :
    e = R.cstarAlpha := by
  refine R.cstarAlpha_unique e hcont ?_
  have hlin :
      ∀ z : A.SourceLimit,
        (e.toAlgEquiv.toLinearMap.comp
            (R.sourceEmbedding.toAlgHom.toLinearMap : A.SourceLimit →ₗ[ℂ] R.sourceCStar)) z =
          (R.regionalEmbedding.toAlgHom.toLinearMap : A.SourceLimit →ₗ[ℂ] R.targetCStar) z := by
    refine sourceLimit_linear_ext A _ _ (fun n v => ?_)
    show e (R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
      R.regionalEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))
    rw [hword n v, regionalEmbedding_apply, A.alpha_word n v]
  intro z
  exact hlin z

/-- **Existence and uniqueness in stage word form.** -/
theorem existsUnique_cstarAlpha_word :
    ∃! e : R.sourceCStar ≃⋆ₐ[ℂ] R.targetCStar,
      Continuous e ∧ ∀ (n : ℕ) (v : A.SourceLabel n),
        e (R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
          R.targetEmbedding
            (A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v))) := by
  refine ⟨R.cstarAlpha, ⟨R.continuous_cstarAlpha, R.cstarAlpha_sourceEmbedding_word⟩, ?_⟩
  rintro e ⟨hcont, hword⟩
  exact R.cstarAlpha_unique_word e hcont hword

end SourceConcreteRep

/-! ## 7. The branch-uniform regional C⋆ `alpha` -/

variable (A)

/-- The source concrete C⋆-algebra of the branch datum of P55C. -/
noncomputable abbrev SourceConcreteCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS) :=
  (A.branchSourceRep).sourceCStar

/-- The regional concrete C⋆-algebra of the branch datum of P55C. -/
noncomputable abbrev TargetConcreteCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS) :=
  (A.branchSourceRep).targetCStar

/-- The canonical dense embedding of the algebraic source limit. -/
noncomputable abbrev sourceCStarEmbedding : A.SourceLimit →⋆ₐ[ℂ] A.SourceConcreteCStar :=
  (A.branchSourceRep).sourceEmbedding

/-- The canonical dense embedding of the algebraic regional limit. -/
noncomputable abbrev targetCStarEmbedding : A.TargetLimit →⋆ₐ[ℂ] A.TargetConcreteCStar :=
  (A.branchSourceRep).targetEmbedding

/-- **The regional concrete C⋆ `alpha`.**  The unique continuous extension of
the P53 algebraic `alpha` between the P55C concrete C⋆ closures. -/
noncomputable def regionalCStarAlpha : A.SourceConcreteCStar ≃⋆ₐ[ℂ] A.TargetConcreteCStar :=
  (A.branchSourceRep).cstarAlpha

@[simp] theorem regionalCStarAlpha_sourceEmbedding (z : A.SourceLimit) :
    A.regionalCStarAlpha (A.sourceCStarEmbedding z) = A.targetCStarEmbedding (A.alpha z) :=
  (A.branchSourceRep).cstarAlpha_sourceEmbedding z

theorem regionalCStarAlpha_stage (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.regionalCStarAlpha (A.sourceCStarEmbedding (A.sourceOf n x)) =
      A.targetCStarEmbedding (A.alpha (A.sourceOf n x)) :=
  (A.branchSourceRep).cstarAlpha_sourceEmbedding_of n x

theorem regionalCStarAlpha_word (n : ℕ) (v : A.SourceLabel n) :
    A.regionalCStarAlpha (A.sourceCStarEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
      A.targetCStarEmbedding
        (A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v))) :=
  (A.branchSourceRep).cstarAlpha_sourceEmbedding_word n v

@[simp] theorem regionalCStarAlpha_symm_targetEmbedding (y : A.TargetLimit) :
    A.regionalCStarAlpha.symm (A.targetCStarEmbedding y) =
      A.sourceCStarEmbedding (A.alpha.symm y) :=
  (A.branchSourceRep).cstarAlpha_symm_targetEmbedding y

theorem regionalCStarAlpha_symm_stage (n : ℕ) (y : pauliAlgebra (A.targetForm n)) :
    A.regionalCStarAlpha.symm (A.targetCStarEmbedding (A.targetOf n y)) =
      A.sourceCStarEmbedding (A.alpha.symm (A.targetOf n y)) :=
  (A.branchSourceRep).cstarAlpha_symm_targetEmbedding_of n y

theorem regionalCStarAlpha_symm_word (n : ℕ) (v : A.SourceLabel n) :
    A.regionalCStarAlpha.symm
        (A.targetCStarEmbedding
          (A.targetOf n (pauliWord (A.targetForm n) (A.stageLabelMap n v)))) =
      (A.phase n v)⁻¹ •
        A.sourceCStarEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v)) :=
  (A.branchSourceRep).cstarAlpha_symm_targetEmbedding_word n v

theorem isometry_regionalCStarAlpha : Isometry A.regionalCStarAlpha :=
  (A.branchSourceRep).isometry_cstarAlpha

theorem regionalCStarAlpha_surjective : Function.Surjective A.regionalCStarAlpha :=
  (A.branchSourceRep).cstarAlpha_surjective

theorem regionalCStarAlpha_injective : Function.Injective A.regionalCStarAlpha :=
  (A.branchSourceRep).cstarAlpha_injective

theorem continuous_regionalCStarAlpha : Continuous A.regionalCStarAlpha :=
  (A.branchSourceRep).continuous_cstarAlpha

/-- The completed regional `alpha` is implemented by the identity on operators,
the two P55C closures being the same closed operator algebra. -/
theorem coe_regionalCStarAlpha (T : A.SourceConcreteCStar) :
    (A.regionalCStarAlpha T : UHFGNS →L[ℂ] UHFGNS) = (T : UHFGNS →L[ℂ] UHFGNS) :=
  (A.branchSourceRep).coe_cstarAlpha T

/-- **Uniqueness of the regional concrete C⋆ `alpha`.** -/
theorem existsUnique_regionalCStarAlpha :
    ∃! e : A.SourceConcreteCStar ≃⋆ₐ[ℂ] A.TargetConcreteCStar,
      Continuous e ∧ ∀ z : A.SourceLimit,
        e (A.sourceCStarEmbedding z) = A.targetCStarEmbedding (A.alpha z) :=
  (A.branchSourceRep).existsUnique_cstarAlpha

/-- **Uniqueness in stage word form.** -/
theorem existsUnique_regionalCStarAlpha_word :
    ∃! e : A.SourceConcreteCStar ≃⋆ₐ[ℂ] A.TargetConcreteCStar,
      Continuous e ∧ ∀ (n : ℕ) (v : A.SourceLabel n),
        e (A.sourceCStarEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
          A.targetCStarEmbedding
            (A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v))) :=
  (A.branchSourceRep).existsUnique_cstarAlpha_word

/-! ### The two coordinate branches -/

/-- **Infinite branch operator formula.**  When the coordinate index type is
infinite, the completed `alpha` acts on the concrete image of an algebraic
source element by the P54 UHF representation of its P55B dyadic image. -/
theorem coe_regionalCStarAlpha_infinite [Infinite I] (z : A.SourceLimit) :
    (A.regionalCStarAlpha (A.sourceCStarEmbedding z) : UHFGNS →L[ℂ] UHFGNS) =
      uhfRep (A.sourceUHFEquiv z) := by
  show ((A.branchSourceRep).cstarAlpha ((A.branchSourceRep).sourceEmbedding z) :
      UHFGNS →L[ℂ] UHFGNS) = uhfRep (A.sourceUHFEquiv z)
  rw [A.branchSourceRep_infinite]
  exact (A.infiniteSourceRep).coe_cstarAlpha_sourceEmbedding z

/-- **Finite branch operator formula.**  When the coordinate index type is
finite, the completed `alpha` acts on the concrete image of an algebraic source
element by the P54 terminal finite-stage matrix representation of its P55B
image. -/
theorem coe_regionalCStarAlpha_finite [Finite I] (z : A.SourceLimit) :
    (A.regionalCStarAlpha (A.sourceCStarEmbedding z) : UHFGNS →L[ℂ] UHFGNS) =
      uhfStageRep (Nat.card I) (A.sourceFiniteEquiv z) := by
  show ((A.branchSourceRep).cstarAlpha ((A.branchSourceRep).sourceEmbedding z) :
      UHFGNS →L[ℂ] UHFGNS) = uhfStageRep (Nat.card I) (A.sourceFiniteEquiv z)
  rw [A.branchSourceRep_finite]
  exact (A.finiteSourceRep).coe_cstarAlpha_sourceEmbedding z

end AlphaData

/-! ## 8. Non-vacuity -/

/-- **Non-vacuity.**  For the tautological P53 data the regional concrete C⋆
`alpha` exists, is isometric and surjective, and is the unique continuous
star-algebra equivalence implementing the algebraic `alpha` densely. -/
theorem standardAlphaData_regionalCStarAlpha :
    Isometry standardAlphaData.regionalCStarAlpha ∧
      Function.Surjective standardAlphaData.regionalCStarAlpha ∧
      (∀ z, standardAlphaData.regionalCStarAlpha (standardAlphaData.sourceCStarEmbedding z) =
        standardAlphaData.targetCStarEmbedding (standardAlphaData.alpha z)) :=
  ⟨AlphaData.isometry_regionalCStarAlpha _, AlphaData.regionalCStarAlpha_surjective _,
    AlphaData.regionalCStarAlpha_sourceEmbedding _⟩

end LocalHyperbolicAlpha

end StabilizerHyperfinite
