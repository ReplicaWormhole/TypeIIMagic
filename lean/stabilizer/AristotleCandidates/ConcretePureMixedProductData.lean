import AristotleCandidates.ProductGNSTensorFactorization

/-!
# P59A — the concrete pure/mixed product datum

**Context declaration.**  Source basis: `main.tex:1925-1967`.

## Plan alignment

* Package `P59A`, lane `H`; predecessors `P55D`
  (`AristotleCandidates.RegionalConcreteCStarAlpha`) and `P56R`
  (`AristotleCandidates.RegionalProductStateIdentity`), both integrated and
  locally audited, together with the *structure* `ProductGNSData` of `P57`
  (`AristotleCandidates.ProductGNSTensorFactorization`), which is used only as
  the target interface.
* Gate discharged: construct the concrete coordinate pure/mixed C⋆ product
  datum required by P57 from the P52/P53/P55D coordinate model, instead of
  introducing an arbitrary `ProductGNSData` at the regional-factor stage.
* Forbidden downstream claims, none of which is made here: no completed
  infinite tensor-product Hilbert space, no pure or mixed factor
  classification, no regional factor theorem, no trace or weight theorem, and
  no new factor/normality premise.

## Auxiliary assumptions

None beyond the P52/P53/P55D coordinate-model data already carried by
`AlphaData` and `SourceConcreteRep`.  Classical decidability is used locally to
split a finitely supported coordinate word along the selected set
`A.family.selected`.  No tensor-product, state, density, factor, weak-closure,
normality, trace or weight premise is supplied.  There is no `axiom`, `sorry`,
`admit`, `opaque`, `unsafe` or `implemented_by` declaration in this file.

## Classification of the results

**(1) Checked infrastructure developed in this packet.**

* §1–§4: the pure/mixed coordinate label calculus
  (`AlphaData.IsPureLabel`, `AlphaData.IsMixedLabel`, `AlphaData.pureFilter`,
  `AlphaData.mixedFilter`, `AlphaData.pureFilter_add_mixedFilter`), the
  vanishing of the `Z`/`X` pairing across the split
  (`AlphaData.coordPairing_pure_mixed`, `AlphaData.coordPairing_mixed_pure`),
  and the resulting multiplicativity of the manuscript's product expectation
  (`AlphaData.productExpectation_add`).
* §5: the direct-limit stage compatibility `AlphaData.sourceOf_connecting` and
  the concrete stage embedding `SourceConcreteRep.stageEmb`,
  `SourceConcreteRep.wordElt` with its product, involution and reindexing
  formulas.
* §5b: `positiveOfStarSq`, the *proved* conversion of a functional which is
  nonnegative on the elements `star s * s` into a Mathlib `PositiveLinearMap`
  for the pinned concrete C⋆-order `CStarAlgebra.spectralOrder`.
* §6: the generic coordinate C⋆-subalgebra `SourceConcreteRep.labelSpanAlg`,
  `SourceConcreteRep.labelCStarAlg` attached to any class of coordinate labels
  closed under `0` and `+`, with its closed-set induction principle
  `SourceConcreteRep.labelCStarAlg_subset_of_closed`.

**(2) The P59A gate, in the intended form.**

* `SourceConcreteRep.pureCStar` and `SourceConcreteRep.mixedCStar`, the actual
  pure and mixed coordinate quasi-local C⋆-algebras of the selected set
  `A.family.selected` and of its complement, with their unital
  star-homomorphisms `SourceConcreteRep.pureEmbedding`,
  `SourceConcreteRep.mixedEmbedding` into the P55D concrete source
  C⋆-algebra.
* Commutation: `SourceConcreteRep.wordElt_commute`,
  `SourceConcreteRep.pureCStar_mixedCStar_commute`,
  `SourceConcreteRep.pureEmbedding_mixedEmbedding_commute`.
* Dense product span: `SourceConcreteRep.dense_productSpan`.
* The two marginal states: `SourceConcreteRep.pureMarginal`,
  `SourceConcreteRep.mixedMarginal`, with unitality
  (`SourceConcreteRep.pureMarginal_one`,
  `SourceConcreteRep.mixedMarginal_one`), nonnegativity on squares
  (`SourceConcreteRep.pureMarginal_starSq_nonneg`,
  `SourceConcreteRep.mixedMarginal_starSq_nonneg`) and their positive-linear-map
  forms `SourceConcreteRep.purePositiveState`,
  `SourceConcreteRep.mixedPositiveState`.
* Product-state factorization: `SourceConcreteRep.totalStateCLM_wordElt_mul`
  (on Pauli words) and `SourceConcreteRep.totalStateCLM_mul` (on the whole
  factors).
* Contractivity: `SourceConcreteRep.norm_totalStateCLM_le`, from P56R's proved
  norm bound.
* `SourceConcreteRep.concreteProductGNSData` and
  `AlphaData.concreteProductGNSData`: the exported `ProductGNSData`, with **no**
  additional assumption or premise argument, together with the identification
  lemmas `..._Pure`, `..._Mixed`, `..._Total`, `..._pureEmb`, `..._mixedEmb`,
  `..._totalState_apply`, `..._totalState_regional` and
  `..._totalState_wordElt`.

**(3) Conditional statements.**  None.  Every exported declaration depends only
on the P52/P53/P55C/P55D coordinate model and on P56R's proved state.

**(4) Source / Mathlib obstructions still open.**  Pinned Mathlib does not
declare the C⋆-order as a global instance, so the order used for
`PositiveLinearMap` is pinned explicitly to `CStarAlgebra.spectralOrder` and the
conversion from P56R's nonnegativity on squares is proved here rather than
imported.  Nothing about the GNS tensor split, the factors, their type, or a
trace or weight is claimed in this file.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

open scoped ComplexOrder

namespace StabilizerHyperfinite

namespace LocalHyperbolicAlpha

open CoherentLocalHyperbolic

namespace AlphaData

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

/-! ## 1. Pure and mixed coordinate labels

The manuscript's coordinate split is by the selected set `P = A.family.selected`
of `main.tex:1671-1679`: the coordinates in `P` carry the pure factor
`|0⟩⟨0|`, the coordinates outside `P` carry the maximally mixed factor `1/2`.
On finitely supported coordinate words this is the splitting of the support of
a word into its selected and unselected sites. -/

/-- A coordinate Pauli word is **pure** when every coordinate it touches is
selected. -/
def IsPureLabel (c : PauliCoordinateLabels I) : Prop :=
  ∀ p : I ⊕ I, c p ≠ 0 → site p ∈ A.family.selected

/-- A coordinate Pauli word is **mixed** when no coordinate it touches is
selected. -/
def IsMixedLabel (c : PauliCoordinateLabels I) : Prop :=
  ∀ p : I ⊕ I, c p ≠ 0 → site p ∉ A.family.selected

theorem isPureLabel_zero : A.IsPureLabel 0 := by
  intro p hp; simp at hp

theorem isMixedLabel_zero : A.IsMixedLabel 0 := by
  intro p hp; simp at hp

theorem isPureLabel_add {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsPureLabel d) : A.IsPureLabel (c + d) := by
  intro p hp
  rw [Finsupp.add_apply] at hp
  by_cases h : c p = 0
  · exact hd p (by simpa [h] using hp)
  · exact hc p h

theorem isMixedLabel_add {c d : PauliCoordinateLabels I} (hc : A.IsMixedLabel c)
    (hd : A.IsMixedLabel d) : A.IsMixedLabel (c + d) := by
  intro p hp
  rw [Finsupp.add_apply] at hp
  by_cases h : c p = 0
  · exact hd p (by simpa [h] using hp)
  · exact hc p h

open Classical in
/-- The **pure part** of a coordinate Pauli word: its restriction to the
selected coordinates. -/
noncomputable def pureFilter (c : PauliCoordinateLabels I) : PauliCoordinateLabels I :=
  Finsupp.filter (fun p : I ⊕ I => site p ∈ A.family.selected) c

open Classical in
/-- The **mixed part** of a coordinate Pauli word: its restriction to the
unselected coordinates. -/
noncomputable def mixedFilter (c : PauliCoordinateLabels I) : PauliCoordinateLabels I :=
  Finsupp.filter (fun p : I ⊕ I => site p ∉ A.family.selected) c

open Classical in
theorem pureFilter_apply (c : PauliCoordinateLabels I) (p : I ⊕ I) :
    A.pureFilter c p = if site p ∈ A.family.selected then c p else 0 := by
  rw [pureFilter, Finsupp.filter_apply]

open Classical in
theorem mixedFilter_apply (c : PauliCoordinateLabels I) (p : I ⊕ I) :
    A.mixedFilter c p = if site p ∈ A.family.selected then 0 else c p := by
  rw [mixedFilter, Finsupp.filter_apply]
  by_cases h : site p ∈ A.family.selected <;> simp [h]

theorem isPureLabel_pureFilter (c : PauliCoordinateLabels I) :
    A.IsPureLabel (A.pureFilter c) := by
  intro p hp
  by_contra h
  rw [A.pureFilter_apply, if_neg h] at hp
  exact hp rfl

theorem isMixedLabel_mixedFilter (c : PauliCoordinateLabels I) :
    A.IsMixedLabel (A.mixedFilter c) := by
  intro p hp h
  rw [A.mixedFilter_apply, if_pos h] at hp
  exact hp rfl

theorem pureFilter_add_mixedFilter (c : PauliCoordinateLabels I) :
    A.pureFilter c + A.mixedFilter c = c := by
  ext p
  rw [Finsupp.add_apply, A.pureFilter_apply, A.mixedFilter_apply]
  by_cases h : site p ∈ A.family.selected <;> simp [h]

theorem pureFilter_ne_zero {c : PauliCoordinateLabels I} {p : I ⊕ I}
    (hp : A.pureFilter c p ≠ 0) : c p ≠ 0 := by
  rw [A.pureFilter_apply] at hp
  by_cases h : site p ∈ A.family.selected
  · rwa [if_pos h] at hp
  · rw [if_neg h] at hp; exact absurd rfl hp

theorem mixedFilter_ne_zero {c : PauliCoordinateLabels I} {p : I ⊕ I}
    (hp : A.mixedFilter c p ≠ 0) : c p ≠ 0 := by
  rw [A.mixedFilter_apply] at hp
  by_cases h : site p ∈ A.family.selected
  · rw [if_pos h] at hp; exact absurd rfl hp
  · rwa [if_neg h] at hp

/-- A pure and a mixed word never touch the same coordinate. -/
theorem pure_mixed_disjoint {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsMixedLabel d) (p : I ⊕ I) : c p = 0 ∨ d p = 0 := by
  by_cases h : c p = 0
  · exact Or.inl h
  · exact Or.inr (by
      by_contra hdp
      exact hd p hdp (hc p h))

/-! ## 2. The `Z`/`X` pairing vanishes between a pure and a mixed word -/

theorem coordPairing_pure_mixed {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsMixedLabel d) : (coordPairing I).form c d = 0 := by
  show (c.sum fun p a => a * Sum.elim (fun i => d (Sum.inr i)) (fun _ => (0 : PauliBit)) p) = 0
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rcases p with i | i
  · have hci : c (Sum.inl i) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hi : i ∈ A.family.selected := hc (Sum.inl i) hci
    have hdi : d (Sum.inr i) = 0 := by
      by_contra hne
      exact hd (Sum.inr i) hne hi
    simp [hdi]
  · simp

theorem coordPairing_mixed_pure {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsMixedLabel d) : (coordPairing I).form d c = 0 := by
  show (d.sum fun p a => a * Sum.elim (fun i => c (Sum.inr i)) (fun _ => (0 : PauliBit)) p) = 0
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rcases p with i | i
  · have hdi : d (Sum.inl i) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hi : i ∉ A.family.selected := hd (Sum.inl i) hdi
    have hci : c (Sum.inr i) = 0 := by
      by_contra hne
      exact hi (hc (Sum.inr i) hne)
    simp [hci]
  · simp

/-! ## 3. Multiplicativity of the product expectation across the split -/

theorem mem_allowedLabels_add_iff {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsMixedLabel d) :
    c + d ∈ A.allowedLabels ↔ c ∈ A.allowedLabels ∧ d ∈ A.allowedLabels := by
  have hval : ∀ p : I ⊕ I, (c + d) p = 0 ↔ (c p = 0 ∧ d p = 0) := by
    intro p
    rcases A.pure_mixed_disjoint hc hd p with h | h <;> simp [Finsupp.add_apply, h]
  constructor
  · intro h
    obtain ⟨hx, hz⟩ := (A.mem_allowedLabels_iff _).mp h
    constructor
    · refine (A.mem_allowedLabels_iff c).mpr ⟨fun i => ((hval _).mp (hx i)).1, fun i hi => ?_⟩
      refine hz i ?_
      intro h0
      exact hi ((hval _).mp h0).1
    · refine (A.mem_allowedLabels_iff d).mpr ⟨fun i => ((hval _).mp (hx i)).2, fun i hi => ?_⟩
      refine hz i ?_
      intro h0
      exact hi ((hval _).mp h0).2
  · rintro ⟨h1, h2⟩
    obtain ⟨hx1, hz1⟩ := (A.mem_allowedLabels_iff c).mp h1
    obtain ⟨hx2, hz2⟩ := (A.mem_allowedLabels_iff d).mp h2
    refine (A.mem_allowedLabels_iff _).mpr ⟨fun i => (hval _).mpr ⟨hx1 i, hx2 i⟩, fun i hi => ?_⟩
    by_cases h0 : c (Sum.inl i) = 0
    · refine hz2 i ?_
      intro hd0
      exact hi ((hval _).mpr ⟨h0, hd0⟩)
    · exact hz1 i h0

/-- **The product expectation factorizes across the pure/mixed coordinate
split.**  This is the manuscript's `ω = ω_pure ⊗ ω_mixed` checked on Pauli
words (`main.tex:1925-1935`). -/
theorem productExpectation_add {c d : PauliCoordinateLabels I} (hc : A.IsPureLabel c)
    (hd : A.IsMixedLabel d) :
    A.productExpectation (c + d) = A.productExpectation c * A.productExpectation d := by
  classical
  rw [A.productExpectation_eq_indicator, A.productExpectation_eq_indicator,
    A.productExpectation_eq_indicator]
  by_cases h1 : c ∈ A.allowedLabels <;> by_cases h2 : d ∈ A.allowedLabels <;>
    simp [A.mem_allowedLabels_add_iff hc hd, h1, h2]

/-! ## 4. The pure/mixed split of a stage label -/

theorem pureFilter_mem_sourceLabel {n : ℕ} {c : PauliCoordinateLabels I}
    (hc : c ∈ A.SourceLabel n) : A.pureFilter c ∈ A.SourceLabel n := by
  rw [CoherentLocalHyperbolic.LocalHyperbolicFamily.mem_sourceLabels_iff] at hc ⊢
  intro p hp
  exact hc p (Finsupp.mem_support_iff.mpr (A.pureFilter_ne_zero (Finsupp.mem_support_iff.mp hp)))

theorem mixedFilter_mem_sourceLabel {n : ℕ} {c : PauliCoordinateLabels I}
    (hc : c ∈ A.SourceLabel n) : A.mixedFilter c ∈ A.SourceLabel n := by
  rw [CoherentLocalHyperbolic.LocalHyperbolicFamily.mem_sourceLabels_iff] at hc ⊢
  intro p hp
  exact hc p (Finsupp.mem_support_iff.mpr (A.mixedFilter_ne_zero (Finsupp.mem_support_iff.mp hp)))

/-- The pure part of a stage-`n` coordinate label. -/
noncomputable def pureStageLabel (n : ℕ) (v : A.SourceLabel n) : A.SourceLabel n :=
  ⟨A.pureFilter (v : PauliCoordinateLabels I), A.pureFilter_mem_sourceLabel v.2⟩

/-- The mixed part of a stage-`n` coordinate label. -/
noncomputable def mixedStageLabel (n : ℕ) (v : A.SourceLabel n) : A.SourceLabel n :=
  ⟨A.mixedFilter (v : PauliCoordinateLabels I), A.mixedFilter_mem_sourceLabel v.2⟩

@[simp] theorem pureStageLabel_coe (n : ℕ) (v : A.SourceLabel n) :
    ((A.pureStageLabel n v : A.SourceLabel n) : PauliCoordinateLabels I) =
      A.pureFilter (v : PauliCoordinateLabels I) := rfl

@[simp] theorem mixedStageLabel_coe (n : ℕ) (v : A.SourceLabel n) :
    ((A.mixedStageLabel n v : A.SourceLabel n) : PauliCoordinateLabels I) =
      A.mixedFilter (v : PauliCoordinateLabels I) := rfl

theorem pureStageLabel_add_mixedStageLabel (n : ℕ) (v : A.SourceLabel n) :
    A.pureStageLabel n v + A.mixedStageLabel n v = v :=
  Subtype.ext (by
    show A.pureFilter (v : PauliCoordinateLabels I) + A.mixedFilter (v : PauliCoordinateLabels I)
      = (v : PauliCoordinateLabels I)
    exact A.pureFilter_add_mixedFilter _)

/-! ## 5. The stage embedding into the concrete C⋆-model -/

/-- The compatibility of the stage maps into the algebraic limit with the
connecting maps of the directed system. -/
theorem sourceOf_connecting {n m : ℕ} (h : n ≤ m) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceOf m (A.sourceConnecting n m h x) = A.sourceOf n x :=
  DirectLimit.Module.of_f

end AlphaData

/-! ## 5b. From nonnegativity on squares to a Mathlib `PositiveLinearMap`

P56R proves unitality and nonnegativity on the elements `star T * T`.  Mathlib's
`ProductGNSData` interface instead expects a `PositiveLinearMap` for a
`PartialOrder`/`StarOrderedRing` structure.  The conversion is performed here
against the *pinned concrete C⋆-order* `CStarAlgebra.spectralOrder`, whose
`StarOrderedRing` law `CStarAlgebra.spectralOrderedRing` describes the positive
cone as the additive closure of the elements `star s * s`.  Nothing is
assumed. -/

section PositiveConversion

variable {C : Type*} [CStarAlgebra C]

/-- **The conversion theorem.**  For the pinned C⋆-order, a linear functional
which is nonnegative on every `star s * s` is nonnegative on the whole positive
cone. -/
theorem nonneg_of_starSq (g : C →ₗ[ℂ] ℂ) (h : ∀ s : C, 0 ≤ g (star s * s)) {p : C}
    (hp : p ∈ AddSubmonoid.closure (Set.range fun s : C => star s * s)) : 0 ≤ g p := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact h s
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact add_nonneg hx hy

/-- **The conversion.**  A linear functional on a C⋆-algebra which is
nonnegative on every `star s * s` is a Mathlib `PositiveLinearMap` for the
pinned concrete C⋆-order. -/
noncomputable def positiveOfStarSq (g : C →ₗ[ℂ] ℂ) (h : ∀ s : C, 0 ≤ g (star s * s)) :
    letI := CStarAlgebra.spectralOrder C
    C →ₚ[ℂ] ℂ :=
  letI := CStarAlgebra.spectralOrder C
  letI := CStarAlgebra.spectralOrderedRing C
  { toLinearMap := g
    monotone' := by
      intro a b hab
      obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff a b).mp hab
      show g a ≤ g (a + p)
      rw [map_add]
      exact le_add_of_nonneg_right (nonneg_of_starSq g h hp) }

@[simp] theorem positiveOfStarSq_apply (g : C →ₗ[ℂ] ℂ) (h : ∀ s : C, 0 ≤ g (star s * s))
    (x : C) : positiveOfStarSq g h x = g x := rfl

end PositiveConversion

namespace AlphaData

namespace SourceConcreteRep

variable {L I : Type*} [LinearOrder I] {A : AlphaData L I} (R : A.SourceConcreteRep)

/-- The stage-`n` embedding of the finite twisted Pauli algebra into the
concrete source C⋆-algebra of P55C/P55D. -/
noncomputable def stageEmb (n : ℕ) :
    pauliAlgebra (A.sourceForm n) →⋆ₐ[ℂ] R.sourceCStar :=
  R.sourceEmbedding.comp (A.stageStarHom n)

@[simp] theorem stageEmb_apply (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    R.stageEmb n x = R.sourceEmbedding (A.sourceOf n x) := rfl

/-- The concrete operator of a stage-`n` coordinate Pauli word. -/
noncomputable def wordElt (n : ℕ) (v : A.SourceLabel n) : R.sourceCStar :=
  R.stageEmb n (pauliWord (A.sourceForm n) v)

theorem wordElt_def (n : ℕ) (v : A.SourceLabel n) :
    R.wordElt n v = R.sourceEmbedding (A.sourceOf n (pauliWord (A.sourceForm n) v)) := rfl

theorem stageEmb_connecting {n m : ℕ} (h : n ≤ m) (x : pauliAlgebra (A.sourceForm n)) :
    R.stageEmb m (A.sourceConnecting n m h x) = R.stageEmb n x := by
  simp only [stageEmb_apply, A.sourceOf_connecting h x]

/-- A stage word may be reindexed at any later stage. -/
theorem wordElt_incl {n m : ℕ} (h : n ≤ m) (v : A.SourceLabel n) :
    R.wordElt m (A.sourceIncl h v) = R.wordElt n v := by
  rw [wordElt, wordElt, ← A.sourceConnecting_word n m h v, R.stageEmb_connecting]

@[simp] theorem wordElt_zero (n : ℕ) : R.wordElt n 0 = 1 := by
  rw [wordElt, pauliWord_zero, map_one]

theorem wordElt_mul {n : ℕ} (v w : A.SourceLabel n) :
    R.wordElt n v * R.wordElt n w =
      pauliSign ((A.sourceForm n).form v w) • R.wordElt n (v + w) := by
  rw [wordElt, wordElt, wordElt, ← map_mul, pauliWord_mul, map_smul]

theorem wordElt_star {n : ℕ} (v : A.SourceLabel n) :
    star (R.wordElt n v) = pauliSign ((A.sourceForm n).form v v) • R.wordElt n v := by
  rw [wordElt, ← map_star, pauliWord_star, pauli_neg_eq_self, map_smul]

/-! ## 6. Coordinate C⋆-subalgebras attached to a class of labels -/

section GenericSpan

variable (Q : PauliCoordinateLabels I → Prop)

/-- The set of concrete stage Pauli words whose coordinate label satisfies
`Q`. -/
def labelWordSet : Set R.sourceCStar :=
  {T | ∃ (n : ℕ) (v : A.SourceLabel n),
    Q (v : PauliCoordinateLabels I) ∧ T = R.wordElt n v}

theorem wordElt_mem_labelWordSet {n : ℕ} {v : A.SourceLabel n}
    (hv : Q (v : PauliCoordinateLabels I)) : R.wordElt n v ∈ R.labelWordSet Q :=
  ⟨n, v, hv, rfl⟩

variable {Q}

theorem one_mem_labelWordSet (hQ0 : Q 0) : (1 : R.sourceCStar) ∈ R.labelWordSet Q := by
  refine ⟨0, 0, ?_, (R.wordElt_zero 0).symm⟩
  simpa using hQ0

/-- Two stage words may always be compared at a common stage. -/
theorem exists_common_stage {n m : ℕ} (v : A.SourceLabel n) (w : A.SourceLabel m) :
    ∃ (k : ℕ) (v' w' : A.SourceLabel k),
      (v' : PauliCoordinateLabels I) = (v : PauliCoordinateLabels I) ∧
        (w' : PauliCoordinateLabels I) = (w : PauliCoordinateLabels I) ∧
          R.wordElt k v' = R.wordElt n v ∧ R.wordElt k w' = R.wordElt m w :=
  ⟨max n m, A.sourceIncl (le_max_left n m) v, A.sourceIncl (le_max_right n m) w, rfl, rfl,
    R.wordElt_incl _ v, R.wordElt_incl _ w⟩

theorem mul_mem_labelSpan (hQadd : ∀ c d, Q c → Q d → Q (c + d))
    {S T : R.sourceCStar} (hS : S ∈ R.labelWordSet Q) (hT : T ∈ R.labelWordSet Q) :
    S * T ∈ Submodule.span ℂ (R.labelWordSet Q) := by
  obtain ⟨n, v, hv, rfl⟩ := hS
  obtain ⟨m, w, hw, rfl⟩ := hT
  obtain ⟨k, v', w', hv', hw', hev, hew⟩ := R.exists_common_stage v w
  rw [← hev, ← hew, R.wordElt_mul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine R.wordElt_mem_labelWordSet Q ?_
  have : ((v' + w' : A.SourceLabel k) : PauliCoordinateLabels I) =
      (v : PauliCoordinateLabels I) + (w : PauliCoordinateLabels I) := by
    rw [Submodule.coe_add, hv', hw']
  rw [this]
  exact hQadd _ _ hv hw

theorem star_mem_labelSpan {T : R.sourceCStar} (hT : T ∈ Submodule.span ℂ (R.labelWordSet Q)) :
    star T ∈ Submodule.span ℂ (R.labelWordSet Q) := by
  induction hT using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨n, v, hv, rfl⟩ := hu
      rw [R.wordElt_star]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (R.wordElt_mem_labelWordSet Q hv))
  | zero => simp
  | add a b _ _ iha ihb => rw [star_add]; exact Submodule.add_mem _ iha ihb
  | smul c a _ iha => rw [star_smul]; exact Submodule.smul_mem _ _ iha

/-- **The algebraic coordinate subalgebra** attached to a class `Q` of
coordinate labels closed under `0` and `+`: the complex span of the concrete
stage Pauli words with label in `Q`.  It is a genuine unital star subalgebra of
the P55C/P55D concrete source C⋆-algebra. -/
noncomputable def labelSpanAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d)) :
    StarSubalgebra ℂ R.sourceCStar where
  toSubalgebra := (Submodule.span ℂ (R.labelWordSet Q)).toSubalgebra
    (Submodule.subset_span (R.one_mem_labelWordSet hQ0))
    (by
      intro x y hx hy
      have hle : Submodule.span ℂ (R.labelWordSet Q) * Submodule.span ℂ (R.labelWordSet Q)
          ≤ Submodule.span ℂ (R.labelWordSet Q) := by
        rw [Submodule.span_mul_span, Submodule.span_le]
        rintro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := hz
        exact R.mul_mem_labelSpan hQadd ha hb
      exact hle (Submodule.mul_mem_mul hx hy))
  star_mem' := R.star_mem_labelSpan

@[simp] theorem coe_labelSpanAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d)) :
    ((R.labelSpanAlg hQ0 hQadd : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar)
      = (Submodule.span ℂ (R.labelWordSet Q) : Set R.sourceCStar) := rfl

/-- **The coordinate quasi-local C⋆-algebra** attached to a class `Q` of
coordinate labels: the norm closure inside the concrete source C⋆-algebra of
the span of the stage Pauli words with label in `Q`. -/
noncomputable def labelCStarAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d)) :
    StarSubalgebra ℂ R.sourceCStar :=
  (R.labelSpanAlg hQ0 hQadd).topologicalClosure

theorem coe_labelCStarAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d)) :
    ((R.labelCStarAlg hQ0 hQadd : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar)
      = closure (Submodule.span ℂ (R.labelWordSet Q) : Set R.sourceCStar) := by
  rw [labelCStarAlg, StarSubalgebra.topologicalClosure_coe]
  rfl

theorem wordElt_mem_labelCStarAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d))
    {n : ℕ} {v : A.SourceLabel n} (hv : Q (v : PauliCoordinateLabels I)) :
    R.wordElt n v ∈ R.labelCStarAlg hQ0 hQadd := by
  rw [SetLike.mem_coe.symm, R.coe_labelCStarAlg]
  exact subset_closure (Submodule.subset_span (R.wordElt_mem_labelWordSet Q hv))

/-- Any topologically closed set containing the generating words contains the
whole coordinate quasi-local C⋆-algebra.  This is the induction principle used
for commutation and for the product-state factorization. -/
theorem labelCStarAlg_subset_of_closed (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d))
    {C : Submodule ℂ R.sourceCStar} (hclosed : IsClosed (C : Set R.sourceCStar))
    (hgen : R.labelWordSet Q ⊆ (C : Set R.sourceCStar)) :
    ((R.labelCStarAlg hQ0 hQadd : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar)
      ⊆ (C : Set R.sourceCStar) := by
  rw [R.coe_labelCStarAlg]
  refine hclosed.closure_subset_iff.mpr ?_
  exact Submodule.span_le.mpr hgen

instance instIsClosedLabelCStarAlg (hQ0 : Q 0) (hQadd : ∀ c d, Q c → Q d → Q (c + d)) :
    IsClosed ((R.labelCStarAlg hQ0 hQadd : StarSubalgebra ℂ R.sourceCStar) :
      Set R.sourceCStar) :=
  StarSubalgebra.isClosed_topologicalClosure _

end GenericSpan

/-! ## 7. The pure and mixed coordinate quasi-local C⋆-algebras -/

/-- **The pure coordinate quasi-local C⋆-algebra**: the closed span of the
concrete Pauli words supported on the selected coordinates `P`. -/
noncomputable def pureCStar : StarSubalgebra ℂ R.sourceCStar :=
  R.labelCStarAlg (Q := A.IsPureLabel) A.isPureLabel_zero
    (fun _ _ hc hd => A.isPureLabel_add hc hd)

/-- **The mixed coordinate quasi-local C⋆-algebra**: the closed span of the
concrete Pauli words supported on the unselected coordinates `I \ P`. -/
noncomputable def mixedCStar : StarSubalgebra ℂ R.sourceCStar :=
  R.labelCStarAlg (Q := A.IsMixedLabel) A.isMixedLabel_zero
    (fun _ _ hc hd => A.isMixedLabel_add hc hd)

instance : IsClosed ((R.pureCStar : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance : IsClosed ((R.mixedCStar : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar) :=
  StarSubalgebra.isClosed_topologicalClosure _

noncomputable instance : CStarAlgebra R.pureCStar := StarSubalgebra.cstarAlgebra _

noncomputable instance : CStarAlgebra R.mixedCStar := StarSubalgebra.cstarAlgebra _

theorem wordElt_mem_pureCStar {n : ℕ} {v : A.SourceLabel n}
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I)) : R.wordElt n v ∈ R.pureCStar :=
  R.wordElt_mem_labelCStarAlg _ _ hv

theorem wordElt_mem_mixedCStar {n : ℕ} {v : A.SourceLabel n}
    (hv : A.IsMixedLabel (v : PauliCoordinateLabels I)) : R.wordElt n v ∈ R.mixedCStar :=
  R.wordElt_mem_labelCStarAlg _ _ hv

/-- The unital star-homomorphism of the pure factor into the total algebra. -/
noncomputable def pureEmbedding : R.pureCStar →⋆ₐ[ℂ] R.sourceCStar := R.pureCStar.subtype

/-- The unital star-homomorphism of the mixed factor into the total algebra. -/
noncomputable def mixedEmbedding : R.mixedCStar →⋆ₐ[ℂ] R.sourceCStar := R.mixedCStar.subtype

@[simp] theorem pureEmbedding_apply (a : R.pureCStar) :
    R.pureEmbedding a = (a : R.sourceCStar) := rfl

@[simp] theorem mixedEmbedding_apply (b : R.mixedCStar) :
    R.mixedEmbedding b = (b : R.sourceCStar) := rfl

theorem pureEmbedding_injective : Function.Injective R.pureEmbedding := Subtype.val_injective

theorem mixedEmbedding_injective : Function.Injective R.mixedEmbedding := Subtype.val_injective

/-! ## 8. The two factors commute -/

/-- The commutant of a single operator, as a complex submodule. -/
def commSubmodule (b : R.sourceCStar) : Submodule ℂ R.sourceCStar where
  carrier := {a | a * b = b * a}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show (x + y) * b = b * (x + y)
    rw [add_mul, mul_add, hx, hy]
  smul_mem' := by
    intro c x hx
    show (c • x) * b = b * (c • x)
    rw [smul_mul_assoc, mul_smul_comm, hx]

theorem isClosed_commSubmodule (b : R.sourceCStar) :
    IsClosed ((R.commSubmodule b : Submodule ℂ R.sourceCStar) : Set R.sourceCStar) :=
  isClosed_eq (continuous_mul_right b) (continuous_mul_left b)

/-- The commutant of a single operator, in the other variable. -/
def commSubmodule' (a : R.sourceCStar) : Submodule ℂ R.sourceCStar where
  carrier := {b | a * b = b * a}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show a * (x + y) = (x + y) * a
    rw [add_mul, mul_add, hx, hy]
  smul_mem' := by
    intro c x hx
    show a * (c • x) = (c • x) * a
    rw [smul_mul_assoc, mul_smul_comm, hx]

theorem isClosed_commSubmodule' (a : R.sourceCStar) :
    IsClosed ((R.commSubmodule' a : Submodule ℂ R.sourceCStar) : Set R.sourceCStar) :=
  isClosed_eq (continuous_mul_left a) (continuous_mul_right a)

/-- **Pure and mixed Pauli words commute.**  The `Z`/`X` pairing between a word
supported on selected coordinates and a word supported on unselected
coordinates vanishes, so the two twisted Pauli words commute exactly. -/
theorem wordElt_commute {n m : ℕ} {v : A.SourceLabel n} {w : A.SourceLabel m}
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsMixedLabel (w : PauliCoordinateLabels I)) :
    R.wordElt n v * R.wordElt m w = R.wordElt m w * R.wordElt n v := by
  obtain ⟨k, v', w', hv', hw', hev, hew⟩ := R.exists_common_stage v w
  have hvp : A.IsPureLabel (v' : PauliCoordinateLabels I) := by rw [hv']; exact hv
  have hwm : A.IsMixedLabel (w' : PauliCoordinateLabels I) := by rw [hw']; exact hw
  have h1 : (A.sourceForm k).form v' w' = 0 := A.coordPairing_pure_mixed hvp hwm
  have h2 : (A.sourceForm k).form w' v' = 0 := A.coordPairing_mixed_pure hvp hwm
  rw [← hev, ← hew, R.wordElt_mul, R.wordElt_mul, h1, h2, pauliSign_zero, one_smul, one_smul,
    add_comm]

/-- **The pure factor commutes with every mixed Pauli word.** -/
theorem pureCStar_commute_wordElt {a : R.sourceCStar} (ha : a ∈ R.pureCStar)
    {m : ℕ} {w : A.SourceLabel m} (hw : A.IsMixedLabel (w : PauliCoordinateLabels I)) :
    a * R.wordElt m w = R.wordElt m w * a := by
  have hsub := R.labelCStarAlg_subset_of_closed (Q := A.IsPureLabel) A.isPureLabel_zero
    (fun _ _ hc hd => A.isPureLabel_add hc hd)
    (C := R.commSubmodule (R.wordElt m w)) (R.isClosed_commSubmodule _) ?_
  · exact hsub ha
  · rintro _ ⟨n, v, hv, rfl⟩
    exact R.wordElt_commute hv hw

/-- **The two constructed coordinate factors commute elementwise.**  This is
the commutation clause of the manuscript's product decomposition. -/
theorem pureCStar_mixedCStar_commute {a b : R.sourceCStar} (ha : a ∈ R.pureCStar)
    (hb : b ∈ R.mixedCStar) : a * b = b * a := by
  have hsub := R.labelCStarAlg_subset_of_closed (Q := A.IsMixedLabel) A.isMixedLabel_zero
    (fun _ _ hc hd => A.isMixedLabel_add hc hd)
    (C := R.commSubmodule' a) (R.isClosed_commSubmodule' _) ?_
  · exact hsub hb
  · rintro _ ⟨m, w, hw, rfl⟩
    exact R.pureCStar_commute_wordElt ha hw

/-- Commutation in the form required by `ProductGNSData`. -/
theorem pureEmbedding_mixedEmbedding_commute (a : R.pureCStar) (b : R.mixedCStar) :
    R.pureEmbedding a * R.mixedEmbedding b = R.mixedEmbedding b * R.pureEmbedding a :=
  R.pureCStar_mixedCStar_commute a.2 b.2

/-! ## 9. The elementary products span a dense subspace -/

/-- The splitting of a stage Pauli word into its pure and mixed factors. -/
theorem wordElt_split {n : ℕ} (v : A.SourceLabel n) :
    R.wordElt n (A.pureStageLabel n v) * R.wordElt n (A.mixedStageLabel n v)
      = R.wordElt n v := by
  have h1 : (A.sourceForm n).form (A.pureStageLabel n v) (A.mixedStageLabel n v) = 0 :=
    A.coordPairing_pure_mixed (A.isPureLabel_pureFilter _) (A.isMixedLabel_mixedFilter _)
  rw [R.wordElt_mul, h1, pauliSign_zero, one_smul, A.pureStageLabel_add_mixedStageLabel]

/-- The submodule spanned by the elementary products of the two factors. -/
noncomputable def productSpan : Submodule ℂ R.sourceCStar :=
  Submodule.span ℂ (Set.range fun p : R.pureCStar × R.mixedCStar =>
    R.pureEmbedding p.1 * R.mixedEmbedding p.2)

theorem wordElt_mem_productSpan {n : ℕ} (v : A.SourceLabel n) :
    R.wordElt n v ∈ R.productSpan := by
  refine Submodule.subset_span ⟨(⟨R.wordElt n (A.pureStageLabel n v),
    R.wordElt_mem_pureCStar (A.isPureLabel_pureFilter _)⟩,
    ⟨R.wordElt n (A.mixedStageLabel n v),
      R.wordElt_mem_mixedCStar (A.isMixedLabel_mixedFilter _)⟩), ?_⟩
  exact R.wordElt_split v

theorem stageEmb_mem_productSpan (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    R.stageEmb n x ∈ R.productSpan := by
  have hcomap : (⊤ : Submodule ℂ (pauliAlgebra (A.sourceForm n))) ≤
      Submodule.comap ((R.stageEmb n).toAlgHom.toLinearMap) R.productSpan := by
    rw [← (pauliWordBasis (A.sourceForm n)).span_eq, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [pauliWordBasis_apply]
    exact R.wordElt_mem_productSpan v
  exact hcomap (Submodule.mem_top)

theorem sourceEmbedding_mem_productSpan (z : A.SourceLimit) :
    R.sourceEmbedding z ∈ R.productSpan := by
  induction z using DirectLimit.induction with
  | _ n x => exact R.stageEmb_mem_productSpan n x

/-- **The elementary products of the two coordinate factors span a norm dense
subspace of the concrete source C⋆-algebra.** -/
theorem dense_productSpan :
    Dense ((R.productSpan : Submodule ℂ R.sourceCStar) : Set R.sourceCStar) := by
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← R.sourceEmbedding_denseRange.closure_range]
  refine closure_mono ?_
  rintro _ ⟨z, rfl⟩
  exact R.sourceEmbedding_mem_productSpan z

/-! ## 10. The total state and its factorization on elementary products -/

/-- The recovered P56R pure/mixed product state on the concrete source
C⋆-algebra, the total state of the datum. -/
noncomputable abbrev totalStateCLM : R.sourceCStar →L[ℂ] ℂ := cstarProductStateRecovered R

theorem totalStateCLM_wordElt {n : ℕ} (v : A.SourceLabel n) :
    R.totalStateCLM (R.wordElt n v) = A.productExpectation (v : PauliCoordinateLabels I) := by
  rw [wordElt_def, cstarProductStateRecovered_sourceEmbedding, A.sourceProductState_word]

/-- **The word-level factorization.**  On a pure word times a mixed word the
recovered state is the product of the two expectations; this is the manuscript's
`main.tex:1925-1935` check on Pauli words. -/
theorem totalStateCLM_wordElt_mul {n m : ℕ} {v : A.SourceLabel n} {w : A.SourceLabel m}
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsMixedLabel (w : PauliCoordinateLabels I)) :
    R.totalStateCLM (R.wordElt n v * R.wordElt m w)
      = R.totalStateCLM (R.wordElt n v) * R.totalStateCLM (R.wordElt m w) := by
  obtain ⟨k, v', w', hv', hw', hev, hew⟩ := R.exists_common_stage v w
  have hvp : A.IsPureLabel (v' : PauliCoordinateLabels I) := by rw [hv']; exact hv
  have hwm : A.IsMixedLabel (w' : PauliCoordinateLabels I) := by rw [hw']; exact hw
  have h1 : (A.sourceForm k).form v' w' = 0 := A.coordPairing_pure_mixed hvp hwm
  have hcoe : ((v' + w' : A.SourceLabel k) : PauliCoordinateLabels I) =
      (v' : PauliCoordinateLabels I) + (w' : PauliCoordinateLabels I) := Submodule.coe_add _ _
  rw [← hev, ← hew, R.wordElt_mul, h1, pauliSign_zero, one_smul, R.totalStateCLM_wordElt,
    R.totalStateCLM_wordElt, R.totalStateCLM_wordElt, hcoe, A.productExpectation_add hvp hwm]

/-- The set of operators on which the recovered state factorizes against a fixed
right factor, as a complex submodule. -/
noncomputable def stateFactorLeft (b : R.sourceCStar) : Submodule ℂ R.sourceCStar where
  carrier := {a | R.totalStateCLM (a * b) = R.totalStateCLM a * R.totalStateCLM b}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show R.totalStateCLM ((x + y) * b) = R.totalStateCLM (x + y) * R.totalStateCLM b
    rw [add_mul, map_add, map_add, hx, hy, add_mul]
  smul_mem' := by
    intro c x hx
    show R.totalStateCLM ((c • x) * b) = R.totalStateCLM (c • x) * R.totalStateCLM b
    rw [smul_mul_assoc, map_smul, map_smul, hx, smul_mul_assoc]

theorem isClosed_stateFactorLeft (b : R.sourceCStar) :
    IsClosed ((R.stateFactorLeft b : Submodule ℂ R.sourceCStar) : Set R.sourceCStar) :=
  isClosed_eq (R.totalStateCLM.continuous.comp (continuous_mul_right b))
    (R.totalStateCLM.continuous.mul continuous_const)

/-- The set of operators on which the recovered state factorizes against a fixed
left factor, as a complex submodule. -/
noncomputable def stateFactorRight (a : R.sourceCStar) : Submodule ℂ R.sourceCStar where
  carrier := {b | R.totalStateCLM (a * b) = R.totalStateCLM a * R.totalStateCLM b}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show R.totalStateCLM (a * (x + y)) = R.totalStateCLM a * R.totalStateCLM (x + y)
    rw [mul_add, map_add, map_add, hx, hy, mul_add]
  smul_mem' := by
    intro c x hx
    show R.totalStateCLM (a * (c • x)) = R.totalStateCLM a * R.totalStateCLM (c • x)
    rw [mul_smul_comm, map_smul, map_smul, hx, mul_smul_comm]

theorem isClosed_stateFactorRight (a : R.sourceCStar) :
    IsClosed ((R.stateFactorRight a : Submodule ℂ R.sourceCStar) : Set R.sourceCStar) :=
  isClosed_eq (R.totalStateCLM.continuous.comp (continuous_mul_left a))
    (continuous_const.mul R.totalStateCLM.continuous)

theorem totalStateCLM_pureCStar_wordElt {a : R.sourceCStar} (ha : a ∈ R.pureCStar)
    {m : ℕ} {w : A.SourceLabel m} (hw : A.IsMixedLabel (w : PauliCoordinateLabels I)) :
    R.totalStateCLM (a * R.wordElt m w)
      = R.totalStateCLM a * R.totalStateCLM (R.wordElt m w) := by
  have hsub := R.labelCStarAlg_subset_of_closed (Q := A.IsPureLabel) A.isPureLabel_zero
    (fun _ _ hc hd => A.isPureLabel_add hc hd)
    (C := R.stateFactorLeft (R.wordElt m w)) (R.isClosed_stateFactorLeft _) ?_
  · exact hsub ha
  · rintro _ ⟨n, v, hv, rfl⟩
    exact R.totalStateCLM_wordElt_mul hv hw

/-- **The product-state factorization on elementary products.**  The recovered
P56R state factorizes as the product of its two marginals on every product of an
element of the pure factor and an element of the mixed factor. -/
theorem totalStateCLM_mul {a b : R.sourceCStar} (ha : a ∈ R.pureCStar) (hb : b ∈ R.mixedCStar) :
    R.totalStateCLM (a * b) = R.totalStateCLM a * R.totalStateCLM b := by
  have hsub := R.labelCStarAlg_subset_of_closed (Q := A.IsMixedLabel) A.isMixedLabel_zero
    (fun _ _ hc hd => A.isMixedLabel_add hc hd)
    (C := R.stateFactorRight a) (R.isClosed_stateFactorRight _) ?_
  · exact hsub hb
  · rintro _ ⟨m, w, hw, rfl⟩
    exact R.totalStateCLM_pureCStar_wordElt ha hw

/-! ## 11. The three states as Mathlib positive linear maps -/

theorem totalStateCLM_starSq_nonneg (T : R.sourceCStar) :
    (0 : ℂ) ≤ R.totalStateCLM (star T * T) := by
  obtain ⟨r, hr, hval⟩ := cstarProductStateRecovered_positive R T
  rw [hval]
  exact_mod_cast hr

/-- The total state as a Mathlib positive linear map for the pinned C⋆-order. -/
noncomputable def totalPositiveState :
    letI := CStarAlgebra.spectralOrder R.sourceCStar
    R.sourceCStar →ₚ[ℂ] ℂ :=
  positiveOfStarSq (R.totalStateCLM).toLinearMap R.totalStateCLM_starSq_nonneg

/-- The pure marginal, as a linear functional on the pure factor. -/
noncomputable def pureMarginal : R.pureCStar →ₗ[ℂ] ℂ :=
  (R.totalStateCLM).toLinearMap.comp (R.pureEmbedding.toAlgHom.toLinearMap)

/-- The mixed marginal, as a linear functional on the mixed factor. -/
noncomputable def mixedMarginal : R.mixedCStar →ₗ[ℂ] ℂ :=
  (R.totalStateCLM).toLinearMap.comp (R.mixedEmbedding.toAlgHom.toLinearMap)

@[simp] theorem pureMarginal_apply (a : R.pureCStar) :
    R.pureMarginal a = R.totalStateCLM (a : R.sourceCStar) := rfl

@[simp] theorem mixedMarginal_apply (b : R.mixedCStar) :
    R.mixedMarginal b = R.totalStateCLM (b : R.sourceCStar) := rfl

theorem pureMarginal_one : R.pureMarginal 1 = 1 := by
  show R.totalStateCLM ((1 : R.pureCStar) : R.sourceCStar) = 1
  rw [OneMemClass.coe_one, cstarProductStateRecovered_one]

theorem mixedMarginal_one : R.mixedMarginal 1 = 1 := by
  show R.totalStateCLM ((1 : R.mixedCStar) : R.sourceCStar) = 1
  rw [OneMemClass.coe_one, cstarProductStateRecovered_one]

theorem pureMarginal_starSq_nonneg (a : R.pureCStar) :
    (0 : ℂ) ≤ R.pureMarginal (star a * a) := by
  have hcoe : ((star a * a : R.pureCStar) : R.sourceCStar)
      = star (a : R.sourceCStar) * (a : R.sourceCStar) := by
    rw [MulMemClass.coe_mul, StarMemClass.coe_star]
  show (0 : ℂ) ≤ R.totalStateCLM ((star a * a : R.pureCStar) : R.sourceCStar)
  rw [hcoe]
  exact R.totalStateCLM_starSq_nonneg _

theorem mixedMarginal_starSq_nonneg (b : R.mixedCStar) :
    (0 : ℂ) ≤ R.mixedMarginal (star b * b) := by
  have hcoe : ((star b * b : R.mixedCStar) : R.sourceCStar)
      = star (b : R.sourceCStar) * (b : R.sourceCStar) := by
    rw [MulMemClass.coe_mul, StarMemClass.coe_star]
  show (0 : ℂ) ≤ R.totalStateCLM ((star b * b : R.mixedCStar) : R.sourceCStar)
  rw [hcoe]
  exact R.totalStateCLM_starSq_nonneg _

/-- **The pure marginal state** as a Mathlib positive linear map. -/
noncomputable def purePositiveState :
    letI := CStarAlgebra.spectralOrder R.pureCStar
    R.pureCStar →ₚ[ℂ] ℂ :=
  positiveOfStarSq R.pureMarginal R.pureMarginal_starSq_nonneg

/-- **The mixed marginal state** as a Mathlib positive linear map. -/
noncomputable def mixedPositiveState :
    letI := CStarAlgebra.spectralOrder R.mixedCStar
    R.mixedCStar →ₚ[ℂ] ℂ :=
  positiveOfStarSq R.mixedMarginal R.mixedMarginal_starSq_nonneg

/-- The total state is norm-decreasing; this is P56R's proved norm bound. -/
theorem norm_totalStateCLM_le (T : R.sourceCStar) : ‖R.totalStateCLM T‖ ≤ ‖T‖ :=
  le_trans (R.totalStateCLM.le_opNorm T)
    (by
      have := norm_cstarProductStateRecovered_le_one R
      nlinarith [norm_nonneg T, norm_nonneg (cstarProductStateRecovered R)])

/-! ## 12. The concrete `ProductGNSData` -/

open AristotleCandidates.ProductGNSTensor in
/-- **The concrete pure/mixed coordinate product datum.**

Every field is a theorem of this file or of P56R: the two factors are the
constructed pure and mixed coordinate quasi-local C⋆-algebras, the embeddings
are their inclusions into the P55C/P55D concrete source C⋆-algebra, the total
state is P56R's recovered `cstarProductStateRecovered`, and the two marginals
are its restrictions.  No `CoordinateSplitData`, density, product, positivity or
norm-bound premise is introduced. -/
noncomputable def concreteProductGNSData : ProductGNSData.{0} :=
  letI := CStarAlgebra.spectralOrder R.pureCStar
  letI := CStarAlgebra.spectralOrderedRing R.pureCStar
  letI := CStarAlgebra.spectralOrder R.mixedCStar
  letI := CStarAlgebra.spectralOrderedRing R.mixedCStar
  letI := CStarAlgebra.spectralOrder R.sourceCStar
  letI := CStarAlgebra.spectralOrderedRing R.sourceCStar
  { Pure := R.pureCStar
    Mixed := R.mixedCStar
    Total := R.sourceCStar
    pureEmb := R.pureEmbedding
    mixedEmb := R.mixedEmbedding
    pureState := R.purePositiveState
    mixedState := R.mixedPositiveState
    totalState := R.totalPositiveState
    commuting := R.pureEmbedding_mixedEmbedding_commute
    product := fun a b => R.totalStateCLM_mul a.2 b.2
    state_norm_le := R.norm_totalStateCLM_le
    span_dense := R.dense_productSpan }

section Identification

open AristotleCandidates.ProductGNSTensor

/-- The pure factor of the datum is the constructed pure coordinate
quasi-local C⋆-algebra. -/
theorem concreteProductGNSData_Pure :
    R.concreteProductGNSData.Pure = R.pureCStar := rfl

/-- The mixed factor of the datum is the constructed mixed coordinate
quasi-local C⋆-algebra. -/
theorem concreteProductGNSData_Mixed :
    R.concreteProductGNSData.Mixed = R.mixedCStar := rfl

/-- **The total algebra of the datum is the P55C/P55D concrete source
C⋆-algebra.** -/
theorem concreteProductGNSData_Total :
    R.concreteProductGNSData.Total = R.sourceCStar := rfl

theorem concreteProductGNSData_pureEmb :
    R.concreteProductGNSData.pureEmb = R.pureEmbedding := rfl

theorem concreteProductGNSData_mixedEmb :
    R.concreteProductGNSData.mixedEmb = R.mixedEmbedding := rfl

/-- **The total state of the datum is P56R's recovered pure/mixed product
state.** -/
theorem concreteProductGNSData_totalState_apply (T : R.sourceCStar) :
    R.concreteProductGNSData.totalState T = cstarProductStateRecovered R T := rfl

theorem concreteProductGNSData_pureState_apply (a : R.pureCStar) :
    R.concreteProductGNSData.pureState a = cstarProductStateRecovered R (a : R.sourceCStar) :=
  rfl

theorem concreteProductGNSData_mixedState_apply (b : R.mixedCStar) :
    R.concreteProductGNSData.mixedState b = cstarProductStateRecovered R (b : R.sourceCStar) :=
  rfl

/-- **The total state of the datum is P56R's recovered regional stabilizer
state transported through the P55D C⋆ `alpha`.** -/
theorem concreteProductGNSData_totalState_regional (T : R.sourceCStar) :
    R.concreteProductGNSData.totalState T = cstarRegionalStateRecovered R (R.cstarAlpha T) := by
  rw [concreteProductGNSData_totalState_apply, cstarRegionalStateRecovered_cstarAlpha]

/-- The total state of the datum is unital. -/
theorem concreteProductGNSData_totalState_one :
    R.concreteProductGNSData.totalState 1 = 1 :=
  cstarProductStateRecovered_one R

/-- The pure marginal of the datum is unital. -/
theorem concreteProductGNSData_pureState_one :
    R.concreteProductGNSData.pureState 1 = 1 := R.pureMarginal_one

/-- The mixed marginal of the datum is unital. -/
theorem concreteProductGNSData_mixedState_one :
    R.concreteProductGNSData.mixedState 1 = 1 := R.mixedMarginal_one

/-- On the concrete image of a stage Pauli word the total state of the datum is
the manuscript's pure/mixed product expectation of the word's label. -/
theorem concreteProductGNSData_totalState_wordElt {n : ℕ} (v : A.SourceLabel n) :
    R.concreteProductGNSData.totalState (R.wordElt n v)
      = A.productExpectation (v : PauliCoordinateLabels I) :=
  R.totalStateCLM_wordElt v

end Identification

end SourceConcreteRep

/-! ## 13. The branch-uniform concrete product datum -/

section Branch

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

open AristotleCandidates.ProductGNSTensor

/-- **The branch-uniform concrete pure/mixed product datum** of the
local-hyperbolic coordinate model, built from the P55C branch representation.
It carries no additional assumption argument. -/
noncomputable def concreteProductGNSData : ProductGNSData.{0} :=
  (A.branchSourceRep).concreteProductGNSData

/-- Its total algebra is the P55D source concrete C⋆-algebra. -/
theorem concreteProductGNSData_Total :
    (A.concreteProductGNSData).Total = A.SourceConcreteCStar := rfl

/-- Its total state is P56R's recovered pure/mixed product state. -/
theorem concreteProductGNSData_totalState_apply (T : A.SourceConcreteCStar) :
    (A.concreteProductGNSData).totalState T =
      SourceConcreteRep.cstarProductStateRecovered (A.branchSourceRep) T := rfl

/-- Its total state is P56R's recovered regional stabilizer state transported
through the P55D regional C⋆ `alpha`. -/
theorem concreteProductGNSData_totalState_regional (T : A.SourceConcreteCStar) :
    (A.concreteProductGNSData).totalState T =
      SourceConcreteRep.cstarRegionalStateRecovered (A.branchSourceRep) (A.regionalCStarAlpha T) :=
  (A.branchSourceRep).concreteProductGNSData_totalState_regional T

end Branch

end AlphaData

/-! ## 14. Non-vacuity -/

/-- **Non-vacuity.**  For the P53 tautological coordinate data the concrete
pure/mixed product datum exists, its total algebra is the P55D source concrete
C⋆-algebra, and its total state is P56R's recovered product state. -/
theorem standardAlphaData_concreteProductGNSData :
    (standardAlphaData.concreteProductGNSData).Total =
        standardAlphaData.SourceConcreteCStar ∧
      ∀ T : standardAlphaData.SourceConcreteCStar,
        (standardAlphaData.concreteProductGNSData).totalState T =
          AlphaData.SourceConcreteRep.cstarProductStateRecovered
            (standardAlphaData.branchSourceRep) T :=
  ⟨rfl, fun _ => rfl⟩

end LocalHyperbolicAlpha

end StabilizerHyperfinite
