import AristotleCandidates.RegionalConcreteCStarAlpha
import Formalization.FinitePureMixedQubitState

/-!
# P56 / P56R — the regional/product-state identity and its recovery

**Context declaration.**  Source basis: `main.tex:1915-1969` (the state
`\tilde\omega = \omega_S \circ \alpha` and its identification with the
pure/mixed product state `\bigotimes_{i\in F\cap P}|0\rangle\langle 0|\otimes
\bigotimes_{j\in F\setminus P}\mathbb 1_j/2`, "checked on Pauli words, which
form a basis of the operators").

## Plan alignment

* Packages `P56` (§§1–10, preserved partial artifact) and `P56R` (§11, the
  recovery), lane `H`; predecessor `P55D`
  (`AristotleCandidates.RegionalConcreteCStarAlpha`), integrated and audited,
  together with the checked pure/mixed one-qubit expectations of
  `Formalization.FinitePureMixedQubitState`.
* Gate discharged by `P56R`: construct the pure/mixed product **C⋆ state** on
  the concrete source C⋆-algebra with *no* supplied boundedness, positivity,
  state or completion datum, prove it unital, positive on `star T * T` and of
  norm at most one, transport it through the exact P55D C⋆ `alpha` and prove
  that the resulting regional state satisfies
  `cstarRegionalStateRecovered (cstarAlpha T) = cstarProductStateRecovered T`.
* Forbidden downstream claims, none of which is made here: no GNS tensor
  splitting, no von Neumann spatial tensor product, no factorhood, no trivial
  centre, and no trace or weight classification.

## What is constructed and proved

For every `A : AlphaData L I` of P53:

1. `allowedLabels`, the manuscript's selection rule on coordinate Pauli words
   (no `X` exponent, every `Z` exponent on a selected coordinate `i ∈ P`), and
   `stabilizerLabels`, the local stabilizer group `W_Γ`, proved equal to
   `span_{F₂} {z i : i ∈ P}`, together with the **stabilizer membership
   criterion** `coordinateMap_mem_stabilizerLabels_iff`.
2. `productExpectation`, the pure/mixed product-state expectation of a
   coordinate Pauli word, defined as the finite product of the *checked*
   one-qubit expectations `singleQubitPureExpectation` (on `i ∈ P`) and
   `singleQubitMixedExpectation` (on `i ∉ P`) of
   `Formalization.FinitePureMixedQubitState`, and proved equal to the indicator
   of `allowedLabels`.
3. `sourceProductState`, the pure/mixed product state on the algebraic
   quasi-local Pauli algebra, and `regionalStabilizerState`, the regional
   stabilizer state on the algebraic regional algebra, both built from
   compatible finite-stage functionals; both are unital.
4. **The finite-word identity** `regionalStabilizerState_alpha_word` and its
   consequence on the whole algebraic limit `regionalStabilizerState_alpha`:
   `ω_S ∘ α = ω_prod`.
5. The stabilizer-character package `stabilizerElement`, `..._mul`,
   `..._star`, `regionalStabilizerState_stabilizerElement`: the images `α(O)` of
   allowed words form a group of self-adjoint elements with expectation `1`,
   and every regional Pauli word outside `W_Γ` is annihilated.
6. **The continuous state identity** `SourceConcreteRep.cstarState_identity`
   (and its branch form `regionalCStarAlpha_state_identity`): *any* two
   continuous functionals on the P55C concrete C⋆-algebras restricting to the
   two algebraic states on the dense algebraic images satisfy `g ∘ alpha = f`
   for the exact P55D C⋆ `alpha`.  Each is unique
   (`cstarSourceState_unique`, `cstarRegionalState_unique`).
7. Under the single auxiliary assumption below, the two continuous functionals
   are *constructed* (`cstarProductState`, `cstarRegionalState`) by a proved
   dense-extension theorem for bounded linear functionals, and the final
   equality is `cstarRegionalState_cstarAlpha`.

## Auxiliary assumptions

**None in the recovery section §11 (`P56R`).**  Sections 1–10 are the preserved
`P56` artifact and still carry, in §8 only, the explicit structure
`AlphaData.SourceConcreteRep.ProductStateBound`: a norm bound
`‖ω_prod z‖ ≤ C ‖R.sourceEmbedding z‖` for the algebraic product state with
respect to the concrete C⋆-norm of P55C.  Section 11 *proves* that bound with
`C = 1` and therefore uses no `ProductStateBound` argument and no other supplied
datum:

* `AlphaData.norm_stageProductState_le` — the finite-stage estimate
  `‖ω_n x‖ ≤ ‖x‖` for the `l²`-operator C⋆-norm of the stage matrix algebra,
  obtained from the explicit stage density matrix
  `D = ∑_{v ∈ allowedStage n} P_v` (self-adjoint, `D * D = |G| • D`,
  `tr D = dim`) by writing `tr (D x D)` as a sum of vector expectations over
  the columns of `D`;
* `AlphaData.stageProductState_positive` — the matching finite-stage positivity
  `ω_n (star x * x) ≥ 0`, and its direct-limit consequence
  `AlphaData.sourceProductState_positive`;
* `AlphaData.norm_sourceEmbedding_sourceOf` — the stage embedding into the
  concrete P55C/P55D model is isometric, because an injective star homomorphism
  of C⋆-algebras is isometric;
* `SourceConcreteRep.cstarProductStateRecovered` — the continuous extension of
  the (now proved `1`-Lipschitz) algebraic product state, with
  `cstarProductStateRecovered_one`, `cstarProductStateRecovered_positive`,
  `norm_cstarProductStateRecovered_le_one`;
* `SourceConcreteRep.cstarRegionalStateRecovered` — its transport through
  `cstarAlpha.symm`, unital and positive, agreeing with
  `regionalStabilizerState` on the dense algebraic image, and satisfying the
  recovery gate `cstarRegionalStateRecovered_cstarAlpha`.

Unitality plus positivity on squares is recorded by the pinned local predicate
`IsAlgebraicState` of `Formalization.TraceTransport`; all of its fields are
proved, none assumed.
-/

namespace StabilizerHyperfinite

namespace LocalHyperbolicAlpha

open CoherentLocalHyperbolic

/-! ## 0. Extension of a bounded linear functional along a dense isometric image

This is the analytic tool used in §9: a linear functional on a dense subspace
which is bounded for the ambient norm has a unique continuous extension.  It is
the functional analogue of `Formalization.ConcreteCStarCompletion`'s extension
of star-algebra homomorphisms, and it is proved, not assumed. -/

section DenseFunctional

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  {i : E →ₗ[ℂ] X} {f : E →ₗ[ℂ] ℂ}

/-- The extension of a linear functional along an isometric linear map with
dense range. -/
noncomputable def extendFunctional (hi : Isometry i) (hd : DenseRange i) (f : E →ₗ[ℂ] ℂ) :
    X → ℂ :=
  IsDenseInducing.extend (hi.isUniformInducing.isDenseInducing hd) f

/-- Two continuous functionals which agree on a dense isometric image agree. -/
theorem eq_of_denseRange (hd : DenseRange i) (g h : X →L[ℂ] ℂ)
    (hgh : ∀ a, g (i a) = h (i a)) : g = h := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  have hfun : (g : X → ℂ) = h :=
    Continuous.ext_on hd g.continuous h.continuous (by rintro _ ⟨a, rfl⟩; exact hgh a)
  exact congrFun hfun x

variable (hi : Isometry i) (hd : DenseRange i) (hf : UniformContinuous f)

include hf in
theorem extendFunctional_apply (a : E) : extendFunctional hi hd f (i a) = f a :=
  uniformly_extend_of_ind hi.isUniformInducing hd hf a

include hf in
theorem continuous_extendFunctional : Continuous (extendFunctional hi hd f) :=
  (uniformContinuous_uniformly_extend hi.isUniformInducing hd hf).continuous

include hf in
theorem extendFunctional_add (x y : X) :
    extendFunctional hi hd f (x + y) =
      extendFunctional hi hd f x + extendFunctional hi hd f y := by
  have hc := continuous_extendFunctional hi hd hf
  have hfun : (fun p : X × X => extendFunctional hi hd f (p.1 + p.2)) =
      fun p : X × X => extendFunctional hi hd f p.1 + extendFunctional hi hd f p.2 := by
    refine Continuous.ext_on (hd.prodMap hd) (hc.comp (continuous_fst.add continuous_snd))
      ((hc.comp continuous_fst).add (hc.comp continuous_snd)) ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show extendFunctional hi hd f (i a + i b) =
      extendFunctional hi hd f (i a) + extendFunctional hi hd f (i b)
    rw [← map_add i, extendFunctional_apply hi hd hf, extendFunctional_apply hi hd hf,
      extendFunctional_apply hi hd hf, map_add f]
  exact congrFun hfun (x, y)

include hf in
theorem extendFunctional_smul (c : ℂ) (x : X) :
    extendFunctional hi hd f (c • x) = c • extendFunctional hi hd f x := by
  have hc := continuous_extendFunctional hi hd hf
  have hfun : (fun x : X => extendFunctional hi hd f (c • x)) =
      fun x : X => c • extendFunctional hi hd f x := by
    refine Continuous.ext_on hd (hc.comp (continuous_const_smul c)) (hc.const_smul c) ?_
    rintro _ ⟨a, rfl⟩
    show extendFunctional hi hd f (c • i a) = c • extendFunctional hi hd f (i a)
    rw [← map_smul i, extendFunctional_apply hi hd hf, extendFunctional_apply hi hd hf,
      map_smul f]
  exact congrFun hfun x

/-- **The continuous extension**, as a continuous linear functional. -/
noncomputable def extendCLM (hi : Isometry i) (hd : DenseRange i) {f : E →ₗ[ℂ] ℂ}
    (hf : UniformContinuous f) : X →L[ℂ] ℂ where
  toFun := extendFunctional hi hd f
  map_add' := extendFunctional_add hi hd hf
  map_smul' c x := extendFunctional_smul hi hd hf c x
  cont := continuous_extendFunctional hi hd hf

@[simp] theorem extendCLM_apply (a : E) : extendCLM hi hd hf (i a) = f a :=
  extendFunctional_apply hi hd hf a

/-- **Uniqueness of the continuous extension.** -/
theorem eq_extendCLM (g : X →L[ℂ] ℂ) (hg : ∀ a, g (i a) = f a) : g = extendCLM hi hd hf := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  have hfun : (g : X → ℂ) = extendCLM hi hd hf := by
    refine Continuous.ext_on hd g.continuous (extendCLM hi hd hf).continuous ?_
    rintro _ ⟨a, rfl⟩
    rw [hg a, extendCLM_apply hi hd hf a]
  exact congrFun hfun x

end DenseFunctional

namespace AlphaData

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

/-! ## 1. The allowed source labels and the regional stabilizer labels -/

/-- **The allowed source Pauli labels.**  The manuscript's condition on a
coordinate Pauli word `O = \prod_i X_i^{a_i} Z_i^{b_i}`: no `X` exponent at all,
and every `Z` exponent carried by a selected (`P`) coordinate.  In the
coordinate label group `(I ⊕ I) →₀ F₂` the `Z` exponents sit on `Sum.inl` and
the `X` exponents on `Sum.inr`. -/
def allowedLabels : Submodule PauliBit (PauliCoordinateLabels I) :=
  Finsupp.supported PauliBit PauliBit (Sum.inl '' A.family.selected)

theorem mem_allowedLabels_iff (c : PauliCoordinateLabels I) :
    c ∈ A.allowedLabels ↔
      (∀ i : I, c (Sum.inr i) = 0) ∧ ∀ i : I, c (Sum.inl i) ≠ 0 → i ∈ A.family.selected := by
  classical
  rw [allowedLabels, Finsupp.mem_supported]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_contra hne
      obtain ⟨j, hj, hji⟩ := h (Finsupp.mem_support_iff.mpr hne)
      exact Sum.inl_ne_inr hji
    · obtain ⟨j, hj, hji⟩ := h (Finsupp.mem_support_iff.mpr hi)
      rw [← Sum.inl.injEq j i |>.mp hji]
      exact hj
  · rintro ⟨hx, hz⟩ p hp
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hp
    rcases p with i | i
    · exact ⟨i, hz i hp, rfl⟩
    · exact absurd (hx i) hp

/-- **The regional stabilizer labels** `W_Γ`: the image of the allowed source
labels under the coordinate map, i.e. the `F₂`-span of `{z i : i ∈ P}`. -/
noncomputable def stabilizerLabels : Submodule PauliBit (PhaseSpace L) :=
  A.allowedLabels.map A.family.coordinateMap

/-- `W_Γ = span_{F₂} {z i : i ∈ P}`, the manuscript's description of the local
stabilizer group. -/
theorem stabilizerLabels_eq_span :
    A.stabilizerLabels = Submodule.span PauliBit (A.family.z '' A.family.selected) := by
  rw [stabilizerLabels, allowedLabels, Finsupp.supported_eq_span_single, Submodule.map_span]
  congr 1
  simp only [Set.image_image]
  exact Set.image_congr (fun i _ => A.family.coordinateMap_single_z i)

/-- **The stabilizer membership criterion.**  A coordinate word lands in the
regional stabilizer group exactly when it is an allowed word.  This is the
injectivity of the adapted coordinate map in the form used by the manuscript's
"the resulting operator will have a string that is [outside] `W_Γ`". -/
theorem coordinateMap_mem_stabilizerLabels_iff (c : PauliCoordinateLabels I) :
    A.family.coordinateMap c ∈ A.stabilizerLabels ↔ c ∈ A.allowedLabels := by
  constructor
  · rintro ⟨d, hd, hdc⟩
    rwa [A.family.coordinateMap_injective hdc] at hd
  · intro hc
    exact ⟨c, hc, rfl⟩

/-! ## 2. The pure/mixed product expectation of a coordinate Pauli word -/

/-- The one-qubit Pauli label carried by the coordinate `i` of a coordinate
Pauli word: the `X` exponent is the `Sum.inr` entry, the `Z` exponent the
`Sum.inl` entry. -/
def coordLabel (c : PauliCoordinateLabels I) (i : I) : SingleQubitLabel :=
  (c (Sum.inr i), c (Sum.inl i))

/-- **The one-qubit factor of the pure/mixed product state** at the coordinate
`i`: the checked zero-vector expectation `singleQubitPureExpectation` on a
selected (`i ∈ P`) coordinate, and the checked normalized-trace expectation
`singleQubitMixedExpectation` on an unselected one. -/
noncomputable def coordFactor (c : PauliCoordinateLabels I) (i : I) : ℂ := by
  classical
  exact if i ∈ A.family.selected then singleQubitPureExpectation (coordLabel c i)
    else singleQubitMixedExpectation (coordLabel c i)

theorem coordFactor_selected {c : PauliCoordinateLabels I} {i : I}
    (hi : i ∈ A.family.selected) :
    A.coordFactor c i = singleQubitPureExpectation (coordLabel c i) := by
  classical
  rw [coordFactor, if_pos hi]

theorem coordFactor_not_selected {c : PauliCoordinateLabels I} {i : I}
    (hi : i ∉ A.family.selected) :
    A.coordFactor c i = singleQubitMixedExpectation (coordLabel c i) := by
  classical
  rw [coordFactor, if_neg hi]

open scoped Classical in
/-- The finite set of coordinates touched by a coordinate Pauli word. -/
noncomputable def coordSupport' (c : PauliCoordinateLabels I) : Finset I :=
  c.support.image site

open scoped Classical in
theorem mem_coordSupport'_iff (c : PauliCoordinateLabels I) (i : I) :
    i ∈ coordSupport' (I := I) c ↔ c (Sum.inl i) ≠ 0 ∨ c (Sum.inr i) ≠ 0 := by
  classical
  rw [coordSupport', Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finsupp.mem_support_iff] at hp
    rcases p with j | j
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (h | h)
    · exact ⟨Sum.inl i, Finsupp.mem_support_iff.mpr h, rfl⟩
    · exact ⟨Sum.inr i, Finsupp.mem_support_iff.mpr h, rfl⟩

open scoped Classical in
/-- **The pure/mixed product-state expectation of a coordinate Pauli word**
(`main.tex:1927-1931`): the finite product of the one-qubit expectations over
the coordinates touched by the word.  All other coordinates contribute the
factor `1`. -/
noncomputable def productExpectation (c : PauliCoordinateLabels I) : ℂ :=
  ∏ i ∈ coordSupport' (I := I) c, A.coordFactor c i

/-- **The manuscript's selection rule, positive half.**  The product-state
expectation of an allowed coordinate Pauli word — no `X` exponent, all `Z`
exponents on selected coordinates — is `1`. -/
theorem productExpectation_of_mem {c : PauliCoordinateLabels I} (hc : c ∈ A.allowedLabels) :
    A.productExpectation c = 1 := by
  classical
  · rw [productExpectation]
    obtain ⟨hx, hz⟩ := (A.mem_allowedLabels_iff c).mp hc
    refine Finset.prod_eq_one (fun i hi => ?_)
    have hisel : i ∈ A.family.selected := by
      rcases (mem_coordSupport'_iff c i).mp hi with h | h
      · exact hz i h
      · exact absurd (hx i) h
    rw [A.coordFactor_selected hisel, coordLabel, hx i]
    simp [singleQubitPureExpectation]

/-- **The manuscript's selection rule, vanishing half.**  Every coordinate
Pauli word which is not allowed has product-state expectation `0`. -/
theorem productExpectation_of_not_mem {c : PauliCoordinateLabels I}
    (hc : c ∉ A.allowedLabels) : A.productExpectation c = 0 := by
  classical
  · rw [productExpectation]
    have hex : ∃ i : I, A.coordFactor c i = 0 ∧ i ∈ coordSupport' (I := I) c := by
      by_contra hno
      push_neg at hno
      refine hc ((A.mem_allowedLabels_iff c).mpr ⟨fun i => ?_, fun i hi => ?_⟩)
      · by_contra hne
        have hmem : i ∈ coordSupport' (I := I) c :=
          (mem_coordSupport'_iff c i).mpr (Or.inr hne)
        have hzero : A.coordFactor c i = 0 := by
          by_cases hisel : i ∈ A.family.selected
          · rw [A.coordFactor_selected hisel, coordLabel]
            simp [singleQubitPureExpectation, hne]
          · rw [A.coordFactor_not_selected hisel, coordLabel]
            simp [singleQubitMixedExpectation, Prod.ext_iff, hne]
        exact (hno i hzero) hmem
      · by_contra hisel
        have hmem : i ∈ coordSupport' (I := I) c :=
          (mem_coordSupport'_iff c i).mpr (Or.inl hi)
        have hzero : A.coordFactor c i = 0 := by
          rw [A.coordFactor_not_selected hisel, coordLabel]
          simp [singleQubitMixedExpectation, Prod.ext_iff, hi]
        exact (hno i hzero) hmem
    obtain ⟨i, hzero, hmem⟩ := hex
    exact Finset.prod_eq_zero hmem hzero

open scoped Classical in
/-- **The manuscript's selection rule.**  The product-state expectation of a
coordinate Pauli word is the indicator of the allowed words. -/
theorem productExpectation_eq_indicator (c : PauliCoordinateLabels I) :
    A.productExpectation c = if c ∈ A.allowedLabels then 1 else 0 := by
  by_cases hc : c ∈ A.allowedLabels
  · rw [if_pos hc, A.productExpectation_of_mem hc]
  · rw [if_neg hc, A.productExpectation_of_not_mem hc]

@[simp] theorem productExpectation_zero : A.productExpectation 0 = 1 :=
  A.productExpectation_of_mem (Submodule.zero_mem _)

/-! ## 3. The product state on the algebraic source limit -/

/-- The stage-`n` product-state functional: the linear functional whose value on
each Pauli word is the pure/mixed product expectation of its label. -/
noncomputable def stageProductState (n : ℕ) : pauliAlgebra (A.sourceForm n) →ₗ[ℂ] ℂ :=
  (pauliWordBasis (A.sourceForm n)).constr ℂ
    (fun v => A.productExpectation (v : PauliCoordinateLabels I))

@[simp] theorem stageProductState_word (n : ℕ) (v : A.SourceLabel n) :
    A.stageProductState n (pauliWord (A.sourceForm n) v) =
      A.productExpectation (v : PauliCoordinateLabels I) := by
  rw [stageProductState, ← pauliWordBasis_apply, Module.Basis.constr_basis]

/-- The stage product states are compatible with the stage inclusions: the
manuscript's "for every local product `F ⋐ I`" coherence. -/
theorem stageProductState_connecting (n m : ℕ) (h : n ≤ m) (x : pauliAlgebra (A.sourceForm n)) :
    A.stageProductState m (A.sourceConnecting n m h x) = A.stageProductState n x := by
  refine pauliAlgebra_linear_ext (A.sourceForm n)
    ((A.stageProductState m).comp (A.sourceConnecting n m h).toAlgHom.toLinearMap)
    (A.stageProductState n) (fun v => ?_) x
  show A.stageProductState m (A.sourceConnecting n m h (pauliWord (A.sourceForm n) v)) = _
  rw [A.sourceConnecting_word, A.stageProductState_word, A.stageProductState_word,
    A.sourceIncl_coe]

/-- **The pure/mixed product state on the algebraic quasi-local Pauli algebra**
`𝒫I`: the coherent limit of the finite product states. -/
noncomputable def sourceProductState : A.SourceLimit →ₗ[ℂ] ℂ :=
  algebraicLimitTrace A.stageProductState A.stageProductState_connecting

@[simp] theorem sourceProductState_of (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceProductState (A.sourceOf n x) = A.stageProductState n x :=
  algebraicLimitTrace_of (f := fun i j le => A.directedFamily.sourceConnecting i j le)
    A.stageProductState A.stageProductState_connecting n x

theorem sourceProductState_word (n : ℕ) (v : A.SourceLabel n) :
    A.sourceProductState (A.sourceOf n (pauliWord (A.sourceForm n) v)) =
      A.productExpectation (v : PauliCoordinateLabels I) := by
  rw [A.sourceProductState_of, A.stageProductState_word]

/-! ## 4. The regional stabilizer state on the algebraic regional limit -/

open scoped Classical in
/-- The allowed coordinate word labelling a regional stabilizer vector.  It is
unique when it exists, by injectivity of the adapted coordinate map. -/
noncomputable def stabPreimage (u : PhaseSpace L) : PauliCoordinateLabels I :=
  if h : ∃ c : PauliCoordinateLabels I, c ∈ A.allowedLabels ∧ A.family.coordinateMap c = u
    then h.choose else 0

theorem stabPreimage_coordinateMap {c : PauliCoordinateLabels I} (hc : c ∈ A.allowedLabels) :
    A.stabPreimage (A.family.coordinateMap c) = c := by
  classical
  have hex : ∃ d : PauliCoordinateLabels I,
      d ∈ A.allowedLabels ∧ A.family.coordinateMap d = A.family.coordinateMap c := ⟨c, hc, rfl⟩
  rw [stabPreimage, dif_pos hex]
  exact A.family.coordinateMap_injective hex.choose_spec.2

/-- **The stabilizer sign character.**  On a regional stabilizer vector
`u = \sum_{i} z_i` it is the inverse of the P53 calibration phase of the
coordinate word labelling `u`; this is exactly the sign convention that makes
the calibrated regional Pauli words `α(O)` the `+1`-eigenvalue stabilizer
elements. -/
noncomputable def stabSign (u : PhaseSpace L) : ℂ :=
  (zmodFourPhase (A.qGlobal (A.stabPreimage u)))⁻¹

theorem stabSign_coordinateMap {c : PauliCoordinateLabels I} (hc : c ∈ A.allowedLabels) :
    A.stabSign (A.family.coordinateMap c) = (zmodFourPhase (A.qGlobal c))⁻¹ := by
  rw [stabSign, A.stabPreimage_coordinateMap hc]

open scoped Classical in
/-- **The value of the regional stabilizer state on a regional Pauli word**: the
stabilizer sign on the stabilizer group `W_Γ`, and `0` on every Pauli string
outside it (`main.tex:1936-1943`). -/
noncomputable def regionalWordValue (u : PhaseSpace L) : ℂ :=
  if u ∈ A.stabilizerLabels then A.stabSign u else 0

theorem regionalWordValue_of_not_mem {u : PhaseSpace L} (hu : u ∉ A.stabilizerLabels) :
    A.regionalWordValue u = 0 := by
  classical
  rw [regionalWordValue, if_neg hu]

theorem regionalWordValue_coordinateMap {c : PauliCoordinateLabels I}
    (hc : c ∈ A.allowedLabels) :
    A.regionalWordValue (A.family.coordinateMap c) = (zmodFourPhase (A.qGlobal c))⁻¹ := by
  classical
  rw [regionalWordValue, if_pos ((A.coordinateMap_mem_stabilizerLabels_iff c).mpr hc),
    A.stabSign_coordinateMap hc]

/-- The stage-`n` regional stabilizer functional. -/
noncomputable def stageRegionalState (n : ℕ) : pauliAlgebra (A.targetForm n) →ₗ[ℂ] ℂ :=
  (pauliWordBasis (A.targetForm n)).constr ℂ (fun u => A.regionalWordValue (u : PhaseSpace L))

@[simp] theorem stageRegionalState_word (n : ℕ) (u : A.TargetLabel n) :
    A.stageRegionalState n (pauliWord (A.targetForm n) u) =
      A.regionalWordValue (u : PhaseSpace L) := by
  rw [stageRegionalState, ← pauliWordBasis_apply, Module.Basis.constr_basis]

theorem stageRegionalState_connecting (n m : ℕ) (h : n ≤ m) (y : pauliAlgebra (A.targetForm n)) :
    A.stageRegionalState m (A.targetConnecting n m h y) = A.stageRegionalState n y := by
  refine pauliAlgebra_linear_ext (A.targetForm n)
    ((A.stageRegionalState m).comp (A.targetConnecting n m h).toAlgHom.toLinearMap)
    (A.stageRegionalState n) (fun u => ?_) y
  show A.stageRegionalState m (A.targetConnecting n m h (pauliWord (A.targetForm n) u)) = _
  rw [A.targetConnecting_word, A.stageRegionalState_word, A.stageRegionalState_word,
    A.targetIncl_coe]

/-- **The regional stabilizer state on the algebraic regional algebra** `𝒜Γ`. -/
noncomputable def regionalStabilizerState : A.TargetLimit →ₗ[ℂ] ℂ :=
  algebraicLimitTrace A.stageRegionalState A.stageRegionalState_connecting

@[simp] theorem regionalStabilizerState_of (n : ℕ) (y : pauliAlgebra (A.targetForm n)) :
    A.regionalStabilizerState (A.targetOf n y) = A.stageRegionalState n y :=
  algebraicLimitTrace_of (f := fun i j le => A.directedFamily.targetConnecting i j le)
    A.stageRegionalState A.stageRegionalState_connecting n y

theorem regionalStabilizerState_word (n : ℕ) (u : A.TargetLabel n) :
    A.regionalStabilizerState (A.targetOf n (pauliWord (A.targetForm n) u)) =
      A.regionalWordValue (u : PhaseSpace L) := by
  rw [A.regionalStabilizerState_of, A.stageRegionalState_word]

/-- The regional stabilizer state annihilates every regional Pauli word whose
string lies outside the local stabilizer group `W_Γ`. -/
theorem regionalStabilizerState_word_of_not_mem (n : ℕ) {u : A.TargetLabel n}
    (hu : (u : PhaseSpace L) ∉ A.stabilizerLabels) :
    A.regionalStabilizerState (A.targetOf n (pauliWord (A.targetForm n) u)) = 0 := by
  rw [A.regionalStabilizerState_word, A.regionalWordValue_of_not_mem hu]

/-! ## 5. Unitality of the two algebraic functionals -/

theorem sourceOf_one (n : ℕ) : A.sourceOf n (1 : pauliAlgebra (A.sourceForm n)) = 1 :=
  (DirectLimit.one_def (G := A.directedFamily.limitData.Source)
    (f := fun i j h => A.directedFamily.limitData.sourceConnecting i j h) n).symm

theorem targetOf_one (n : ℕ) : A.targetOf n (1 : pauliAlgebra (A.targetForm n)) = 1 :=
  (DirectLimit.one_def (G := A.directedFamily.limitData.Target)
    (f := fun i j h => A.directedFamily.limitData.targetConnecting i j h) n).symm

theorem sourceOf_mul (n : ℕ) (x y : pauliAlgebra (A.sourceForm n)) :
    A.sourceOf n (x * y) = A.sourceOf n x * A.sourceOf n y :=
  (DirectLimit.mul_def (G := A.directedFamily.limitData.Source)
    (f := fun i j h => A.directedFamily.limitData.sourceConnecting i j h) n x y).symm

theorem sourceOf_star (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceOf n (star x) = star (A.sourceOf n x) :=
  (star_of (f := fun i j h => A.directedFamily.limitData.sourceConnecting i j h) n x).symm

@[simp] theorem sourceProductState_one : A.sourceProductState 1 = 1 := by
  rw [← A.sourceOf_one 0, A.sourceProductState_of,
    show (1 : pauliAlgebra (A.sourceForm 0)) = pauliWord (A.sourceForm 0) 0 from
      (pauliWord_zero _).symm, A.stageProductState_word]
  simp

@[simp] theorem regionalStabilizerState_one : A.regionalStabilizerState 1 = 1 := by
  rw [← A.targetOf_one 0, A.regionalStabilizerState_of,
    show (1 : pauliAlgebra (A.targetForm 0)) = pauliWord (A.targetForm 0) 0 from
      (pauliWord_zero _).symm, A.stageRegionalState_word]
  have h0 : ((0 : A.TargetLabel 0) : PhaseSpace L) = A.family.coordinateMap 0 := by simp
  rw [h0, A.regionalWordValue_coordinateMap (Submodule.zero_mem _)]
  simp [A.qGlobal_zero]

/-! ## 6. The finite Pauli-word identity -/

/-- **The finite-word state identity** (`main.tex:1927-1943`).  On every finite
coordinate Pauli word, the regional stabilizer state pulled back by the exact
P53/P55D `alpha` is the pure/mixed product expectation of the word: it is `1`
when the word has no `X` exponent and all its `Z` exponents on selected
coordinates — equivalently, when the regional string lies in `W_Γ` — and `0`
otherwise. -/
theorem regionalStabilizerState_alpha_word (n : ℕ) (v : A.SourceLabel n) :
    A.regionalStabilizerState (A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) v))) =
      A.productExpectation (v : PauliCoordinateLabels I) := by
  classical
  rw [A.alpha_word n v, A.regionalStabilizerState_of, map_smul, A.stageRegionalState_word,
    smul_eq_mul, A.stageLabelMap_coe]
  by_cases hv : (v : PauliCoordinateLabels I) ∈ A.allowedLabels
  · rw [A.regionalWordValue_coordinateMap hv, A.productExpectation_of_mem hv]
    exact mul_inv_cancel₀ (A.phase_ne_zero n v)
  · rw [A.regionalWordValue_of_not_mem
      (fun h => hv ((A.coordinateMap_mem_stabilizerLabels_iff _).mp h)),
      A.productExpectation_of_not_mem hv, mul_zero]

/-- **The algebraic state identity.**  On the whole algebraic quasi-local Pauli
algebra, `\tilde\omega = \omega_S \circ \alpha` is the pure/mixed product state.
This is the manuscript's "since the states agree on a basis of operators, they
are the same states", at the algebraic level. -/
theorem regionalStabilizerState_alpha (z : A.SourceLimit) :
    A.regionalStabilizerState (A.alpha z) = A.sourceProductState z := by
  refine sourceLimit_linear_ext A
    (A.regionalStabilizerState.comp A.alpha.toAlgEquiv.toLinearMap) A.sourceProductState
    (fun n v => ?_) z
  show A.regionalStabilizerState (A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) v))) = _
  rw [A.regionalStabilizerState_alpha_word, A.sourceProductState_word]

/-- Composition form of the algebraic state identity. -/
theorem regionalStabilizerState_comp_alpha :
    A.regionalStabilizerState.comp A.alpha.toAlgEquiv.toLinearMap = A.sourceProductState :=
  LinearMap.ext A.regionalStabilizerState_alpha

/-- Inverse form of the algebraic state identity. -/
theorem sourceProductState_alpha_symm (y : A.TargetLimit) :
    A.sourceProductState (A.alpha.symm y) = A.regionalStabilizerState y := by
  rw [← A.regionalStabilizerState_alpha (A.alpha.symm y), StarAlgEquiv.apply_symm_apply]

/-! ## 7. The regional stabilizer elements -/

section Stabilizer

variable {A}

/-- On allowed labels the source Pauli pairing vanishes: allowed words carry no
`X` exponent, so they commute and are self-adjoint. -/
theorem sourceForm_eq_zero_of_allowed_right {n : ℕ} (v w : A.SourceLabel n)
    (hw : (w : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    (A.sourceForm n).form v w = 0 := by
  obtain ⟨hx, -⟩ := (A.mem_allowedLabels_iff _).mp hw
  show (coordPairing I).form (v : PauliCoordinateLabels I) (w : PauliCoordinateLabels I) = 0
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rcases p with i | i
  · simp [hx i]
  · simp

/-- Allowed source Pauli words multiply without a sign. -/
theorem pauliWord_mul_of_allowed {n : ℕ} (v w : A.SourceLabel n)
    (hw : (w : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    pauliWord (A.sourceForm n) v * pauliWord (A.sourceForm n) w =
      pauliWord (A.sourceForm n) (v + w) := by
  rw [pauliWord_mul, sourceForm_eq_zero_of_allowed_right v w hw, pauliSign_zero, one_smul]

/-- Allowed source Pauli words are self-adjoint. -/
theorem pauliWord_star_of_allowed {n : ℕ} (v : A.SourceLabel n)
    (hv : (v : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    star (pauliWord (A.sourceForm n) v) = pauliWord (A.sourceForm n) v := by
  rw [pauliWord_star, sourceForm_eq_zero_of_allowed_right v v hv, pauliSign_zero, one_smul,
    pauli_neg_eq_self]

variable (A)

/-- **The regional stabilizer elements.**  The image under the P53/P55D `alpha`
of an allowed coordinate Pauli word: a phase-calibrated regional Pauli word
whose string is the stabilizer vector `\sum_i z_i`. -/
noncomputable def stabilizerElement (n : ℕ) (v : A.SourceLabel n) : A.TargetLimit :=
  A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) v))

/-- The regional stabilizer element is the calibrated regional Pauli word of the
image string. -/
theorem stabilizerElement_eq (n : ℕ) (v : A.SourceLabel n) :
    A.stabilizerElement n v =
      A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v)) :=
  A.alpha_word n v

/-- The string of a regional stabilizer element lies in `W_Γ`. -/
theorem stageLabelMap_mem_stabilizerLabels {n : ℕ} (v : A.SourceLabel n)
    (hv : (v : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    ((A.stageLabelMap n v : A.TargetLabel n) : PhaseSpace L) ∈ A.stabilizerLabels := by
  rw [A.stageLabelMap_coe]
  exact (A.coordinateMap_mem_stabilizerLabels_iff _).mpr hv

@[simp] theorem stabilizerElement_zero (n : ℕ) : A.stabilizerElement n 0 = 1 := by
  rw [stabilizerElement, pauliWord_zero, A.sourceOf_one, map_one]

/-- The regional stabilizer elements form a group under multiplication. -/
theorem stabilizerElement_mul {n : ℕ} (v w : A.SourceLabel n)
    (hw : (w : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    A.stabilizerElement n v * A.stabilizerElement n w = A.stabilizerElement n (v + w) := by
  rw [stabilizerElement, stabilizerElement, stabilizerElement, ← map_mul, ← A.sourceOf_mul,
    pauliWord_mul_of_allowed v w hw]

/-- The regional stabilizer elements are self-adjoint. -/
theorem stabilizerElement_star {n : ℕ} (v : A.SourceLabel n)
    (hv : (v : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    star (A.stabilizerElement n v) = A.stabilizerElement n v := by
  rw [stabilizerElement, ← map_star, ← A.sourceOf_star, pauliWord_star_of_allowed v hv]

/-- **The stabilizer-state property.**  The regional state has expectation `1`
on every regional stabilizer element, i.e. the elements `α(O)` of allowed words
are exactly the `+1`-eigenvalue stabilizer operators of the state. -/
theorem regionalStabilizerState_stabilizerElement {n : ℕ} (v : A.SourceLabel n)
    (hv : (v : PauliCoordinateLabels I) ∈ A.allowedLabels) :
    A.regionalStabilizerState (A.stabilizerElement n v) = 1 := by
  rw [stabilizerElement, A.regionalStabilizerState_alpha_word, A.productExpectation_of_mem hv]

end Stabilizer

/-! ## 8. The identity on the concrete C⋆-algebras -/

namespace SourceConcreteRep

variable {A} (R : A.SourceConcreteRep)

/-- **The continuous state identity** (`main.tex:1944-1946`, "since the states
agree on a basis of operators, they are the same states").

If `f` is *any* continuous linear functional on the P55C concrete source
C⋆-algebra restricting to the pure/mixed product state on the dense algebraic
image, and `g` is *any* continuous linear functional on the P55C concrete
regional C⋆-algebra restricting to the regional stabilizer state on the dense
algebraic image, then `g ∘ alpha = f` for the exact P55D C⋆ `alpha`.  No
boundedness or continuity premise beyond the continuity of `f` and `g`
themselves is used. -/
theorem cstarState_identity (f : R.sourceCStar →L[ℂ] ℂ) (g : R.targetCStar →L[ℂ] ℂ)
    (hf : ∀ z : A.SourceLimit, f (R.sourceEmbedding z) = A.sourceProductState z)
    (hg : ∀ y : A.TargetLimit, g (R.targetEmbedding y) = A.regionalStabilizerState y)
    (T : R.sourceCStar) : g (R.cstarAlpha T) = f T := by
  have hfun : (fun T : R.sourceCStar => g (R.cstarAlpha T)) = fun T => f T := by
    refine Continuous.ext_on R.sourceEmbedding_denseRange
      (g.continuous.comp R.continuous_cstarAlpha) f.continuous ?_
    rintro _ ⟨z, rfl⟩
    show g (R.cstarAlpha (R.sourceEmbedding z)) = f (R.sourceEmbedding z)
    rw [R.cstarAlpha_sourceEmbedding, hg, hf, A.regionalStabilizerState_alpha]
  exact congrFun hfun T

/-- A continuous functional on the concrete source C⋆-algebra is determined by
its restriction to the dense algebraic image. -/
theorem cstarSourceState_unique (f f' : R.sourceCStar →L[ℂ] ℂ)
    (hf : ∀ z : A.SourceLimit, f (R.sourceEmbedding z) = A.sourceProductState z)
    (hf' : ∀ z : A.SourceLimit, f' (R.sourceEmbedding z) = A.sourceProductState z) : f = f' := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  have hfun : (f : R.sourceCStar → ℂ) = f' :=
    Continuous.ext_on R.sourceEmbedding_denseRange f.continuous f'.continuous
      (by rintro _ ⟨z, rfl⟩; rw [hf z, hf' z])
  exact congrFun hfun T

/-- A continuous functional on the concrete regional C⋆-algebra is determined by
its restriction to the dense algebraic image. -/
theorem cstarRegionalState_unique (g g' : R.targetCStar →L[ℂ] ℂ)
    (hg : ∀ y : A.TargetLimit, g (R.targetEmbedding y) = A.regionalStabilizerState y)
    (hg' : ∀ y : A.TargetLimit, g' (R.targetEmbedding y) = A.regionalStabilizerState y) :
    g = g' := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  have hfun : (g : R.targetCStar → ℂ) = g' :=
    Continuous.ext_on R.targetEmbedding_denseRange g.continuous g'.continuous
      (by rintro _ ⟨y, rfl⟩; rw [hg y, hg' y])
  exact congrFun hfun T

/-! ### Existence of the two continuous states

The only auxiliary assumption of this module: the algebraic product state is
bounded for the concrete C⋆-norm of P55C.  It is the analytic input that the
manuscript leaves implicit when it passes from Pauli words to the quasi-local
C⋆-algebra.  Nothing else — no supplied state, no supplied extension, no
supplied density interface — is assumed: the extension itself is constructed
and proved unique. -/

/-- **Auxiliary assumption (product-state boundedness).**  A norm bound for the
algebraic pure/mixed product state with respect to the concrete C⋆-norm of the
P55C representation. -/
structure ProductStateBound where
  /-- The bound constant. -/
  const : ℝ
  /-- The bound itself. -/
  norm_le : ∀ z : A.SourceLimit,
    ‖A.sourceProductState z‖ ≤ const * ‖R.sourceEmbedding z‖

variable {R}

theorem uniformContinuous_sourceProductState (hb : R.ProductStateBound) :
    letI := R.sourceNormedRing
    letI := R.sourceNormedAlgebra
    UniformContinuous A.sourceProductState := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact (AddMonoidHomClass.lipschitz_of_bound A.sourceProductState hb.const
    (fun z => hb.norm_le z)).uniformContinuous

/-- **The continuous pure/mixed product state** on the concrete source
C⋆-algebra, constructed by density from the algebraic product state. -/
noncomputable def cstarProductState (hb : R.ProductStateBound) : R.sourceCStar →L[ℂ] ℂ :=
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  extendCLM (i := (R.sourceEmbedding : A.SourceLimit →⋆ₐ[ℂ] R.sourceCStar).toAlgHom.toLinearMap)
    R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    (uniformContinuous_sourceProductState hb)

@[simp] theorem cstarProductState_sourceEmbedding (hb : R.ProductStateBound)
    (z : A.SourceLimit) :
    cstarProductState hb (R.sourceEmbedding z) = A.sourceProductState z := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact extendCLM_apply (i := (R.sourceEmbedding :
      A.SourceLimit →⋆ₐ[ℂ] R.sourceCStar).toAlgHom.toLinearMap)
    R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    (uniformContinuous_sourceProductState hb) z

variable (R)

/-- The inverse of the P55D C⋆ `alpha`, as a continuous linear map. -/
noncomputable def cstarAlphaSymmCLM : R.targetCStar →L[ℂ] R.sourceCStar where
  toFun := R.cstarAlpha.symm
  map_add' := map_add _
  map_smul' c x := map_smul R.cstarAlpha.symm c x
  cont := R.continuous_cstarAlpha_symm

@[simp] theorem cstarAlphaSymmCLM_apply (T : R.targetCStar) :
    R.cstarAlphaSymmCLM T = R.cstarAlpha.symm T := rfl

variable {R}

/-- **The continuous regional stabilizer state** on the concrete regional
C⋆-algebra.  It exists as soon as the product state is bounded, and it is the
unique continuous functional restricting to the algebraic regional stabilizer
state. -/
noncomputable def cstarRegionalState (hb : R.ProductStateBound) : R.targetCStar →L[ℂ] ℂ :=
  (cstarProductState hb).comp R.cstarAlphaSymmCLM

@[simp] theorem cstarRegionalState_targetEmbedding (hb : R.ProductStateBound)
    (y : A.TargetLimit) :
    cstarRegionalState hb (R.targetEmbedding y) = A.regionalStabilizerState y := by
  show cstarProductState hb (R.cstarAlpha.symm (R.targetEmbedding y)) = _
  rw [R.cstarAlpha_symm_targetEmbedding, cstarProductState_sourceEmbedding,
    A.sourceProductState_alpha_symm]

/-- **The final continuous state equality.**  The continuous regional stabilizer
state, pulled back by the exact P55D C⋆ `alpha`, is the continuous pure/mixed
product state on the whole concrete quasi-local C⋆-algebra. -/
theorem cstarRegionalState_cstarAlpha (hb : R.ProductStateBound) (T : R.sourceCStar) :
    cstarRegionalState hb (R.cstarAlpha T) = cstarProductState hb T :=
  cstarState_identity R _ _ (cstarProductState_sourceEmbedding hb)
    (cstarRegionalState_targetEmbedding hb) T

/-- Function form of the final continuous state equality. -/
theorem cstarRegionalState_comp_cstarAlpha (hb : R.ProductStateBound) :
    (fun T : R.sourceCStar => cstarRegionalState hb (R.cstarAlpha T)) =
      fun T => cstarProductState hb T :=
  funext (cstarRegionalState_cstarAlpha hb)

end SourceConcreteRep

/-! ## 9. The branch-uniform regional state identity -/

/-- The branch-uniform continuous state identity for the P55C/P55D branch
representation datum and the exact P55D `A.regionalCStarAlpha`. -/
theorem regionalCStarAlpha_state_identity
    (f : A.SourceConcreteCStar →L[ℂ] ℂ) (g : A.TargetConcreteCStar →L[ℂ] ℂ)
    (hf : ∀ z : A.SourceLimit, f (A.sourceCStarEmbedding z) = A.sourceProductState z)
    (hg : ∀ y : A.TargetLimit, g (A.targetCStarEmbedding y) = A.regionalStabilizerState y)
    (T : A.SourceConcreteCStar) : g (A.regionalCStarAlpha T) = f T :=
  SourceConcreteRep.cstarState_identity (A.branchSourceRep) f g hf hg T

end AlphaData

/-! ## 10. Non-vacuity -/

/-- For the tautological P53 data every coordinate is selected, so the allowed
words are exactly the `X`-free coordinate words. -/
theorem standardAlphaData_mem_allowedLabels_iff (c : PauliCoordinateLabels ℕ) :
    c ∈ standardAlphaData.allowedLabels ↔ ∀ i : ℕ, c (Sum.inr i) = 0 := by
  rw [AlphaData.mem_allowedLabels_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i _ => Set.mem_univ i⟩⟩

/-- **Non-vacuity.**  For the tautological P53 data the algebraic state identity
holds and the two states are unital, so neither is the zero functional. -/
theorem standardAlphaData_state_identity :
    (∀ z, standardAlphaData.regionalStabilizerState (standardAlphaData.alpha z) =
      standardAlphaData.sourceProductState z) ∧
    standardAlphaData.sourceProductState 1 = 1 ∧
    standardAlphaData.regionalStabilizerState 1 = 1 :=
  ⟨AlphaData.regionalStabilizerState_alpha _, AlphaData.sourceProductState_one _,
    AlphaData.regionalStabilizerState_one _⟩

/-! ## 11. Recovery (P56R): the C⋆ product state without a supplied bound

This section replaces the auxiliary `ProductStateBound` of §8 by a *proved*
finite-dimensional estimate.  Every stage of the source direct limit is a
twisted Pauli algebra, i.e. a star-subalgebra of a finite matrix algebra, hence
a genuine finite-dimensional C⋆-algebra.  The stage product state is the
normalized matrix expectation `x ↦ tr(D x)/dim` of the explicit stage density
matrix `D = ∑_{v allowed} P_v`, which is self-adjoint and satisfies `D² =
|G| D`.  Writing `tr(D x D)` as a sum of vector expectations over the columns of
`D` gives at once

* positivity of every stage functional on `star x * x`, and
* the norm bound `|ω_n(x)| ≤ ‖x‖` for the C⋆-norm of the stage matrix algebra.

Because an injective star homomorphism of C⋆-algebras is isometric, the second
statement transports to the concrete P55C/P55D model, and the algebraic product
state is `1`-Lipschitz there; its continuous extension is the recovered C⋆
state.  No boundedness, positivity or state datum is assumed anywhere below. -/

section Recovery

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open scoped Matrix.Norms.L2Operator

/-- The finite matrix algebra of a finite index type is a C⋆-algebra for the
`l²`-operator norm.  All components are already in Mathlib; only the bundling is
local. -/
noncomputable local instance matrixCStarAlgebra {V : Type*} [Fintype V] [DecidableEq V] :
    CStarAlgebra (Matrix V V ℂ) where

/-- A twisted Pauli algebra is a closed star-subalgebra of its matrix algebra:
it is a finite-dimensional subspace. -/
instance pauliAlgebra_isClosed {V : Type*} [AddCommGroup V] [Module PauliBit V] [DecidableEq V]
    [Fintype V] (B : PauliForm V) :
    IsClosed ((pauliAlgebra B : StarSubalgebra ℂ (Matrix V V ℂ)) : Set (Matrix V V ℂ)) := by
  have h : ((pauliAlgebra B : StarSubalgebra ℂ (Matrix V V ℂ)) : Set (Matrix V V ℂ))
      = ((pauliSpan B : Submodule ℂ (Matrix V V ℂ)) : Set (Matrix V V ℂ)) := rfl
  rw [h]
  exact Submodule.closed_of_finiteDimensional _

/-! ### 11.1 The normalized trace of a twisted Pauli word -/

/-- The matrix trace of a twisted Pauli word: `dim` for the trivial word and `0`
for every nontrivial one. -/
theorem trace_pauliMat {V : Type*} [AddCommGroup V] [Module PauliBit V] [DecidableEq V]
    [Fintype V] (B : PauliForm V) (v : V) :
    Matrix.trace (pauliMat B v) = if v = 0 then (Fintype.card V : ℂ) else 0 := by
  classical
  rw [Matrix.trace]
  by_cases hv : v = 0
  · subst hv
    rw [if_pos rfl]
    have hdiag : ∀ r : V, (pauliMat B 0).diag r = 1 := by
      intro r
      show pauliMat B 0 r r = 1
      rw [pauliMat_apply, if_pos (by rw [zero_add]), B.zero_left, pauliSign_zero]
    rw [Finset.sum_congr rfl (fun r _ => hdiag r)]
    simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    show pauliMat B v r r = 0
    rw [pauliMat_apply, if_neg]
    intro h
    exact hv (add_right_cancel (a := v) (b := r) (c := (0 : V)) (by rw [zero_add]; exact h.symm))

/-! ### 11.2 Injectivity of the stage maps -/

/-- A linear map built from a basis by a linearly independent family is
injective. -/
theorem constr_injective {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (b : Module.Basis ι ℂ M) (g : ι → N) (hg : LinearIndependent ℂ g) :
    Function.Injective (b.constr ℂ g) := by
  intro x y hxy
  have h1 : Finsupp.linearCombination ℂ g (b.repr x) = Finsupp.linearCombination ℂ g (b.repr y) := by
    simpa [Module.Basis.constr_apply, Finsupp.linearCombination_apply] using hxy
  exact b.repr.injective (hg h1)

section TwistedInjective

variable {V W : Type*}
variable [AddCommGroup V] [Module PauliBit V] [DecidableEq V] [Fintype V]
variable [AddCommGroup W] [Module PauliBit W] [DecidableEq W] [Fintype W]

/-- A twisted Pauli star homomorphism attached to an injective label map is
injective. -/
theorem twistHom_injective (B : PauliForm V) (C : PauliForm W) (f : V →+ W)
    (hf : ∀ v w, C.form (f v) (f w) = B.form v w) (hinj : Function.Injective f) :
    Function.Injective (twistHom B C f hf) := by
  have hli : LinearIndependent ℂ (fun v : V => pauliWord C (f v)) := by
    have h := (pauliWordBasis C).linearIndependent
    have h2 : LinearIndependent ℂ (pauliWord C) := by
      simpa [funext (pauliWordBasis_apply C)] using h
    exact h2.comp f hinj
  intro x y hxy
  exact constr_injective (pauliWordBasis B) (fun v => pauliWord C (f v)) hli hxy

end TwistedInjective

/-! ### 11.3 Vector expectations of a conjugated matrix trace -/

section MatrixEstimates

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The `r`-th column of a matrix, read as a Euclidean vector. -/
noncomputable def matCol (M : Matrix W W ℂ) (r : W) : EuclideanSpace ℂ W :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M (EuclideanSpace.single r 1)

/-- The matrix trace as the sum of the diagonal vector expectations. -/
theorem matrix_trace_eq_sum_inner (N : Matrix W W ℂ) :
    Matrix.trace N = ∑ r : W, inner ℂ (EuclideanSpace.single r (1:ℂ))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) N (EuclideanSpace.single r 1)) := by
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [EuclideanSpace.inner_single_left]
  simp [Matrix.diag]

/-- For a self-adjoint `M`, the conjugated trace `tr(M N M)` is the sum of the
expectations of `N` in the columns of `M`. -/
theorem matrix_trace_conj (M N : Matrix W W ℂ) (hM : star M = M) :
    Matrix.trace (M * N * M)
      = ∑ r : W, inner ℂ (matCol M r) (Matrix.toEuclideanCLM (𝕜 := ℂ) N (matCol M r)) := by
  rw [matrix_trace_eq_sum_inner]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hsa : star (Matrix.toEuclideanCLM (𝕜 := ℂ) M) = Matrix.toEuclideanCLM (𝕜 := ℂ) M := by
    rw [← map_star, hM]
  rw [map_mul, map_mul]
  show inner ℂ (EuclideanSpace.single r (1:ℂ))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) M (Matrix.toEuclideanCLM (𝕜 := ℂ) N
        (Matrix.toEuclideanCLM (𝕜 := ℂ) M (EuclideanSpace.single r 1)))) = _
  rw [matCol, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hsa]

/-- The total column mass of a self-adjoint matrix is the trace of its square. -/
theorem matrix_trace_sq (M : Matrix W W ℂ) (hM : star M = M) :
    Matrix.trace (M * M) = ((∑ r : W, ‖matCol M r‖^2 : ℝ) : ℂ) := by
  have h := matrix_trace_conj M 1 hM
  rw [mul_one] at h
  rw [h]
  push_cast
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_one]
  simp [inner_self_eq_norm_sq_to_K]

/-- **The finite-dimensional norm estimate.**  The conjugated trace is bounded
by the operator norm times the total column mass. -/
theorem norm_matrix_trace_conj_le (M N : Matrix W W ℂ) (hM : star M = M) :
    ‖Matrix.trace (M * N * M)‖ ≤ ‖N‖ * ∑ r : W, ‖matCol M r‖^2 := by
  rw [matrix_trace_conj M N hM, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  calc ‖inner ℂ (matCol M r) (Matrix.toEuclideanCLM (𝕜 := ℂ) N (matCol M r))‖
      ≤ ‖matCol M r‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) N (matCol M r)‖ := norm_inner_le_norm _ _
    _ ≤ ‖matCol M r‖ * (‖N‖ * ‖matCol M r‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← Matrix.l2_opNorm_toEuclideanCLM N]
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖N‖ * ‖matCol M r‖^2 := by ring

/-- **The finite-dimensional positivity identity.** -/
theorem matrix_trace_conj_star_self (M y : Matrix W W ℂ) (hM : star M = M) :
    Matrix.trace (M * (star y * y) * M)
      = ((∑ r : W, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) y (matCol M r)‖^2 : ℝ) : ℂ) := by
  rw [matrix_trace_conj M _ hM]
  push_cast
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_mul, map_star]
  show inner ℂ (matCol M r) ((star (Matrix.toEuclideanCLM (𝕜 := ℂ) y) *
    Matrix.toEuclideanCLM (𝕜 := ℂ) y) (matCol M r)) = _
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simp [inner_self_eq_norm_sq_to_K]

end MatrixEstimates

namespace AlphaData

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

/-! ### 11.4 The stage density matrix -/

open scoped Classical in
/-- The allowed labels of a stage: those whose coordinate word is allowed. -/
noncomputable def allowedStage (n : ℕ) : Finset (A.SourceLabel n) :=
  Finset.univ.filter (fun v => (v : PauliCoordinateLabels I) ∈ A.allowedLabels)

theorem mem_allowedStage {n : ℕ} {v : A.SourceLabel n} :
    v ∈ A.allowedStage n ↔ (v : PauliCoordinateLabels I) ∈ A.allowedLabels := by
  classical
  rw [allowedStage, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem zero_mem_allowedStage (n : ℕ) : (0 : A.SourceLabel n) ∈ A.allowedStage n := by
  rw [A.mem_allowedStage]
  simp

theorem add_mem_allowedStage {n : ℕ} {v w : A.SourceLabel n} (hv : v ∈ A.allowedStage n)
    (hw : w ∈ A.allowedStage n) : v + w ∈ A.allowedStage n := by
  rw [A.mem_allowedStage] at hv hw ⊢
  simpa using Submodule.add_mem A.allowedLabels hv hw

theorem card_allowedStage_pos (n : ℕ) : 0 < (A.allowedStage n).card :=
  Finset.card_pos.mpr ⟨0, A.zero_mem_allowedStage n⟩

/-- **The stage density matrix** `D = ∑_{v allowed} P_v`: the unnormalized
pure/mixed product density of the manuscript, written in the coordinate Pauli
basis. -/
noncomputable def stageDensityMat (n : ℕ) : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ :=
  ∑ v ∈ A.allowedStage n, pauliMat (A.sourceForm n) v

theorem stageDensityMat_star (n : ℕ) : star (A.stageDensityMat n) = A.stageDensityMat n := by
  rw [stageDensityMat, star_sum]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [pauliMat_star, sourceForm_eq_zero_of_allowed_right v v (A.mem_allowedStage.mp hv),
    pauliSign_zero, one_smul]

/-- The density matrix is `|G|` times a projection. -/
theorem stageDensityMat_mul_self (n : ℕ) :
    A.stageDensityMat n * A.stageDensityMat n
      = ((A.allowedStage n).card : ℂ) • A.stageDensityMat n := by
  classical
  rw [stageDensityMat, Finset.sum_mul]
  have step : ∀ v ∈ A.allowedStage n,
      (pauliMat (A.sourceForm n) v) * (∑ w ∈ A.allowedStage n, pauliMat (A.sourceForm n) w)
        = A.stageDensityMat n := by
    intro v hv
    rw [Finset.mul_sum]
    have hprod : ∀ w ∈ A.allowedStage n,
        pauliMat (A.sourceForm n) v * pauliMat (A.sourceForm n) w
          = pauliMat (A.sourceForm n) (v + w) := by
      intro w hw
      rw [pauliMat_mul, sourceForm_eq_zero_of_allowed_right v w (A.mem_allowedStage.mp hw),
        pauliSign_zero, one_smul]
    rw [Finset.sum_congr rfl hprod]
    refine Finset.sum_nbij' (i := fun w => v + w) (j := fun u => v + u) ?_ ?_ ?_ ?_ ?_
    · intro w hw; exact A.add_mem_allowedStage hv hw
    · intro u hu; exact A.add_mem_allowedStage hv hu
    · intro w _
      show v + (v + w) = w
      rw [← add_assoc, pauliBit_add_self_eq_zero, zero_add]
    · intro u _
      show v + (v + u) = u
      rw [← add_assoc, pauliBit_add_self_eq_zero, zero_add]
    · intro w _; rfl
  rw [Finset.sum_congr rfl step, Finset.sum_const, ← stageDensityMat]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

theorem trace_stageDensityMat (n : ℕ) :
    Matrix.trace (A.stageDensityMat n) = (Fintype.card (A.SourceLabel n) : ℂ) := by
  classical
  rw [stageDensityMat, Matrix.trace_sum,
    Finset.sum_congr rfl (fun v _ => trace_pauliMat (A.sourceForm n) v),
    Finset.sum_ite_eq' (A.allowedStage n) (0 : A.SourceLabel n)
      (fun _ => (Fintype.card (A.SourceLabel n) : ℂ)),
    if_pos (A.zero_mem_allowedStage n)]

/-- **The density matrix computes the product expectation of a Pauli word.** -/
theorem trace_stageDensityMat_mul_word (n : ℕ) (w : A.SourceLabel n) :
    Matrix.trace (A.stageDensityMat n * pauliMat (A.sourceForm n) w)
      = (Fintype.card (A.SourceLabel n) : ℂ) *
        A.productExpectation (w : PauliCoordinateLabels I) := by
  classical
  rw [stageDensityMat, Finset.sum_mul, Matrix.trace_sum]
  have hterm : ∀ c ∈ A.allowedStage n,
      Matrix.trace (pauliMat (A.sourceForm n) c * pauliMat (A.sourceForm n) w)
        = if c = w then (Fintype.card (A.SourceLabel n) : ℂ) else 0 := by
    intro c hc
    rw [pauliMat_mul, Matrix.trace_smul, trace_pauliMat, smul_eq_mul]
    by_cases hcw : c = w
    · subst hcw
      rw [if_pos rfl, if_pos (pauliBit_add_self_eq_zero c),
        sourceForm_eq_zero_of_allowed_right c c (A.mem_allowedStage.mp hc), pauliSign_zero, one_mul]
    · rw [if_neg hcw, if_neg, mul_zero]
      intro h
      refine hcw ?_
      have hcw2 : c + w + w = 0 + w := by rw [h, zero_add]
      rwa [add_assoc, pauliBit_add_self_eq_zero, add_zero, zero_add] at hcw2
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (A.allowedStage n) w
    (fun _ => (Fintype.card (A.SourceLabel n) : ℂ)), A.productExpectation_eq_indicator]
  by_cases hw : (w : PauliCoordinateLabels I) ∈ A.allowedLabels
  · rw [if_pos (A.mem_allowedStage.mpr hw), if_pos hw, mul_one]
  · rw [if_neg (fun h => hw (A.mem_allowedStage.mp h)), if_neg hw, mul_zero]

/-- Pairing of a stage element against the stage density matrix. -/
noncomputable def traceAgainstDensity (n : ℕ) : pauliAlgebra (A.sourceForm n) →ₗ[ℂ] ℂ where
  toFun x := Matrix.trace (A.stageDensityMat n *
    (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ))
  map_add' x y := by
    show Matrix.trace (A.stageDensityMat n * ((x + y : pauliAlgebra (A.sourceForm n)) :
      Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)) = _
    push_cast
    rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' c x := by
    show Matrix.trace (A.stageDensityMat n * ((c • x : pauliAlgebra (A.sourceForm n)) :
      Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)) = _
    push_cast
    rw [Matrix.mul_smul, Matrix.trace_smul]
    rfl

/-- **The stage product state is the normalized density expectation.** -/
theorem traceAgainstDensity_eq (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.traceAgainstDensity n x
      = (Fintype.card (A.SourceLabel n) : ℂ) * A.stageProductState n x := by
  refine pauliAlgebra_linear_ext (A.sourceForm n) (A.traceAgainstDensity n)
    ((Fintype.card (A.SourceLabel n) : ℂ) • A.stageProductState n) (fun v => ?_) x
  show Matrix.trace (A.stageDensityMat n * pauliMat (A.sourceForm n) v) = _
  rw [A.trace_stageDensityMat_mul_word n v]
  show _ = (Fintype.card (A.SourceLabel n) : ℂ) * A.stageProductState n (pauliWord _ v)
  rw [A.stageProductState_word]

/-- The conjugated density trace of a stage element. -/
theorem trace_density_conj (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    Matrix.trace (A.stageDensityMat n *
        (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ) * A.stageDensityMat n)
      = ((A.allowedStage n).card : ℂ) * (Fintype.card (A.SourceLabel n) : ℂ) *
        A.stageProductState n x := by
  rw [Matrix.trace_mul_cycle, A.stageDensityMat_mul_self, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, mul_assoc]
  congr 1
  exact A.traceAgainstDensity_eq n x

/-! ### 11.5 The stage state: unitality, positivity and the C⋆-norm bound -/

theorem stageDensity_normalization (n : ℕ) :
    ∑ r : A.SourceLabel n, ‖matCol (A.stageDensityMat n) r‖ ^ 2
      = ((A.allowedStage n).card : ℝ) * (Fintype.card (A.SourceLabel n) : ℝ) := by
  have h1 := matrix_trace_sq (A.stageDensityMat n) (A.stageDensityMat_star n)
  rw [A.stageDensityMat_mul_self n, Matrix.trace_smul, smul_eq_mul,
    A.trace_stageDensityMat n] at h1
  have h2 : ((∑ r : A.SourceLabel n, ‖matCol (A.stageDensityMat n) r‖ ^ 2 : ℝ) : ℂ)
      = ((((A.allowedStage n).card : ℝ) * (Fintype.card (A.SourceLabel n) : ℝ) : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    ring
  exact_mod_cast h2

/-- **The stage C⋆-norm bound**, proved from the density-matrix estimate: the
stage product state is norm-decreasing for the C⋆-norm of the stage matrix
algebra. -/
theorem norm_stageProductState_le (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    ‖A.stageProductState n x‖ ≤ ‖(x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)‖ := by
  set c : ℝ := ((A.allowedStage n).card : ℝ) * (Fintype.card (A.SourceLabel n) : ℝ) with hc
  have hcpos : 0 < c := by
    have h1 : (0:ℝ) < ((A.allowedStage n).card : ℝ) := by
      exact_mod_cast A.card_allowedStage_pos n
    have h2 : (0:ℝ) < (Fintype.card (A.SourceLabel n) : ℝ) := by
      have := Fintype.card_pos (α := A.SourceLabel n)
      exact_mod_cast this
    exact mul_pos h1 h2
  have hbound := norm_matrix_trace_conj_le (A.stageDensityMat n)
    (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ) (A.stageDensityMat_star n)
  rw [A.stageDensity_normalization n, A.trace_density_conj n x] at hbound
  have hleft : ‖((A.allowedStage n).card : ℂ) * (Fintype.card (A.SourceLabel n) : ℂ) *
      A.stageProductState n x‖ = c * ‖A.stageProductState n x‖ := by
    rw [norm_mul, hc]
    congr 1
    rw [norm_mul]
    simp
  rw [hleft] at hbound
  have h3 : c * ‖A.stageProductState n x‖
      ≤ c * ‖(x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)‖ := by
    refine hbound.trans_eq ?_
    rw [hc]
    ring
  exact le_of_mul_le_mul_left h3 hcpos

/-- **Stage positivity**, proved from the density-matrix identity. -/
theorem stageProductState_positive (n : ℕ) : IsPositiveFunctional (A.stageProductState n) := by
  intro x
  have hstar : ((star x * x : pauliAlgebra (A.sourceForm n)) :
      Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)
      = star (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ) *
        (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ) := rfl
  set c : ℂ := ((A.allowedStage n).card : ℂ) * (Fintype.card (A.SourceLabel n) : ℂ) with hc
  have hcne : c ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (A.card_allowedStage_pos n).ne')
      (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := A.SourceLabel n)).ne')
  have h1 := A.trace_density_conj n (star x * x)
  rw [hstar, matrix_trace_conj_star_self (A.stageDensityMat n)
    (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ) (A.stageDensityMat_star n)] at h1
  refine ⟨(∑ r : A.SourceLabel n,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)
        (matCol (A.stageDensityMat n) r)‖ ^ 2) / (((A.allowedStage n).card : ℝ) *
        (Fintype.card (A.SourceLabel n) : ℝ)), ?_, ?_⟩
  · refine div_nonneg (Finset.sum_nonneg (fun r _ => sq_nonneg _)) ?_
    positivity
  · rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_natCast, eq_div_iff hcne, h1]
    ring

/-! ### 11.6 The algebraic product state is a state -/

theorem sourceProductState_positive : IsPositiveFunctional A.sourceProductState :=
  algebraicLimitTrace_positive A.stageProductState A.stageProductState_connecting
    A.stageProductState_positive

/-- **The algebraic pure/mixed product state is a state**: unital and positive
on squares.  Nothing is assumed. -/
theorem sourceProductState_isAlgebraicState : IsAlgebraicState A.sourceProductState :=
  ⟨A.sourceProductState_one, A.sourceProductState_positive⟩

/-! ### 11.7 The stage maps into the algebraic limit -/

theorem sourceIncl_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (A.sourceIncl h) := by
  intro v w hvw
  apply Subtype.ext
  have hcoe := congrArg (fun u : A.SourceLabel m => (u : PauliCoordinateLabels I)) hvw
  simpa using hcoe

theorem sourceConnecting_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (A.sourceConnecting n m h) :=
  twistHom_injective _ _ _ _ (A.sourceIncl_injective h)

theorem sourceOf_injective (n : ℕ) : Function.Injective (A.sourceOf n) :=
  DirectLimit.mk_injective
    (F := A.directedFamily.limitData.Source)
    (f := fun i j h => A.directedFamily.limitData.sourceConnecting i j h)
    (fun _ _ hij => A.sourceConnecting_injective hij) n

/-- The stage map into the algebraic limit, as a linear map. -/
noncomputable def sourceOfLin (n : ℕ) : pauliAlgebra (A.sourceForm n) →ₗ[ℂ] A.SourceLimit :=
  DirectLimit.Module.of ℂ A.directedFamily.limitData.Index A.directedFamily.limitData.Source
    (fun i j le => A.directedFamily.limitData.sourceConnecting i j le) n

/-- The stage map into the algebraic limit, as a star-algebra homomorphism. -/
noncomputable def stageStarHom (n : ℕ) : pauliAlgebra (A.sourceForm n) →⋆ₐ[ℂ] A.SourceLimit where
  toFun := A.sourceOf n
  map_one' := A.sourceOf_one n
  map_mul' := A.sourceOf_mul n
  map_zero' := map_zero (A.sourceOfLin n)
  map_add' := map_add (A.sourceOfLin n)
  commutes' := by
    intro r
    show A.sourceOf n (algebraMap ℂ _ r) = algebraMap ℂ _ r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      show A.sourceOf n (r • (1 : pauliAlgebra (A.sourceForm n))) = r • A.sourceOf n 1 from
        map_smul (A.sourceOfLin n) r 1, A.sourceOf_one]
  map_star' := A.sourceOf_star n

@[simp] theorem stageStarHom_apply (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.stageStarHom n x = A.sourceOf n x := rfl

/-- **The stage embedding into the concrete C⋆-model is isometric**, because an
injective star homomorphism of C⋆-algebras is isometric. -/
theorem norm_sourceEmbedding_sourceOf (R : A.SourceConcreteRep) (n : ℕ)
    (x : pauliAlgebra (A.sourceForm n)) :
    ‖R.sourceEmbedding (A.sourceOf n x)‖
      = ‖(x : Matrix (A.SourceLabel n) (A.SourceLabel n) ℂ)‖ := by
  have hinj : Function.Injective (R.sourceEmbedding.comp (A.stageStarHom n)) :=
    R.sourceEmbedding_injective.comp (A.sourceOf_injective n)
  exact NonUnitalStarAlgHom.norm_map (R.sourceEmbedding.comp (A.stageStarHom n)) hinj x

/-! ### 11.8 The recovered C⋆ states -/

namespace SourceConcreteRep

variable {A} (R : A.SourceConcreteRep)

/-- **The proved norm bound**: the algebraic product state is norm-decreasing
for the concrete C⋆-norm of P55C.  This is exactly the estimate that §8 had to
assume. -/
theorem norm_sourceProductState_le (z : A.SourceLimit) :
    ‖A.sourceProductState z‖ ≤ ‖R.sourceEmbedding z‖ := by
  induction z using DirectLimit.induction with
  | _ n x =>
    show ‖A.sourceProductState (A.sourceOf n x)‖ ≤ ‖R.sourceEmbedding (A.sourceOf n x)‖
    rw [A.sourceProductState_of, A.norm_sourceEmbedding_sourceOf R n x]
    exact A.norm_stageProductState_le n x

theorem uniformContinuous_sourceProductState_recovered :
    letI := R.sourceNormedRing
    letI := R.sourceNormedAlgebra
    UniformContinuous A.sourceProductState := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact (AddMonoidHomClass.lipschitz_of_bound A.sourceProductState 1
    (fun z => by simpa using R.norm_sourceProductState_le z)).uniformContinuous

/-- **The recovered continuous pure/mixed product state** on the concrete source
C⋆-algebra.  No `ProductStateBound` and no other supplied datum enters. -/
noncomputable def cstarProductStateRecovered : R.sourceCStar →L[ℂ] ℂ :=
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  extendCLM (i := (R.sourceEmbedding : A.SourceLimit →⋆ₐ[ℂ] R.sourceCStar).toAlgHom.toLinearMap)
    R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    (uniformContinuous_sourceProductState_recovered R)

@[simp] theorem cstarProductStateRecovered_sourceEmbedding (z : A.SourceLimit) :
    cstarProductStateRecovered R (R.sourceEmbedding z) = A.sourceProductState z := by
  letI := R.sourceNormedRing
  letI := R.sourceNormedAlgebra
  exact extendCLM_apply (i := (R.sourceEmbedding :
      A.SourceLimit →⋆ₐ[ℂ] R.sourceCStar).toAlgHom.toLinearMap)
    R.isometry_sourceEmbedding R.sourceEmbedding_denseRange
    (uniformContinuous_sourceProductState_recovered R) z

theorem cstarProductStateRecovered_one : cstarProductStateRecovered R 1 = 1 := by
  have h1 : (1 : R.sourceCStar) = R.sourceEmbedding 1 := (map_one _).symm
  rw [h1, cstarProductStateRecovered_sourceEmbedding, A.sourceProductState_one]

theorem cstarProductStateRecovered_positive (T : R.sourceCStar) :
    ∃ r : ℝ, 0 ≤ r ∧ cstarProductStateRecovered R (star T * T) = (r : ℂ) := by
  have hK : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hg : Continuous (fun T : R.sourceCStar => cstarProductStateRecovered R (star T * T)) :=
    (cstarProductStateRecovered R).continuous.comp
      (continuous_mul.comp (continuous_star.prodMk continuous_id))
  have hsub : (Set.range (fun z : A.SourceLimit => R.sourceEmbedding z)) ⊆
      (fun T : R.sourceCStar => cstarProductStateRecovered R (star T * T)) ⁻¹'
        {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨r, hr, hval⟩ := A.sourceProductState_positive z
    have hz : cstarProductStateRecovered R (star (R.sourceEmbedding z) * R.sourceEmbedding z)
        = (r : ℂ) := by
      rw [← map_star, ← map_mul, cstarProductStateRecovered_sourceEmbedding, hval]
    simp [hz, hr]
  have hclosed : IsClosed ((fun T : R.sourceCStar =>
      cstarProductStateRecovered R (star T * T)) ⁻¹' {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) :=
    hK.preimage hg
  have hall := hclosed.closure_subset_iff.mpr hsub
  have hmem : cstarProductStateRecovered R (star T * T) ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    hall (by rw [R.sourceEmbedding_denseRange.closure_range]; trivial)
  exact ⟨(cstarProductStateRecovered R (star T * T)).re, hmem.2,
    Complex.ext rfl (by simpa using hmem.1)⟩

/-- **The recovered source state is a state**: unital and positive on squares. -/
theorem cstarProductStateRecovered_isAlgebraicState :
    IsAlgebraicState (cstarProductStateRecovered R).toLinearMap :=
  ⟨cstarProductStateRecovered_one R, fun T => cstarProductStateRecovered_positive R T⟩

/-- The recovered source state has norm at most one. -/
theorem norm_cstarProductStateRecovered_le_one : ‖cstarProductStateRecovered R‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
  have hK : IsClosed {p : R.sourceCStar | ‖cstarProductStateRecovered R p‖ ≤ 1 * ‖p‖ } :=
    isClosed_le ((cstarProductStateRecovered R).continuous.norm)
      (continuous_const.mul continuous_norm)
  have hsub : (Set.range (fun z : A.SourceLimit => R.sourceEmbedding z)) ⊆
      {p : R.sourceCStar | ‖cstarProductStateRecovered R p‖ ≤ 1 * ‖p‖ } := by
    rintro _ ⟨z, rfl⟩
    show ‖cstarProductStateRecovered R (R.sourceEmbedding z)‖ ≤ 1 * ‖R.sourceEmbedding z‖
    rw [cstarProductStateRecovered_sourceEmbedding, one_mul]
    exact R.norm_sourceProductState_le z
  have hall := hK.closure_subset_iff.mpr hsub
  exact hall (by rw [R.sourceEmbedding_denseRange.closure_range]; trivial)

/-- **The recovered continuous regional stabilizer state**, obtained by
transporting the recovered source state through the exact P55D C⋆ `alpha`. -/
noncomputable def cstarRegionalStateRecovered : R.targetCStar →L[ℂ] ℂ :=
  (cstarProductStateRecovered R).comp R.cstarAlphaSymmCLM

@[simp] theorem cstarRegionalStateRecovered_apply (T : R.targetCStar) :
    cstarRegionalStateRecovered R T = cstarProductStateRecovered R (R.cstarAlpha.symm T) := rfl

@[simp] theorem cstarRegionalStateRecovered_targetEmbedding (y : A.TargetLimit) :
    cstarRegionalStateRecovered R (R.targetEmbedding y) = A.regionalStabilizerState y := by
  rw [cstarRegionalStateRecovered_apply, R.cstarAlpha_symm_targetEmbedding,
    cstarProductStateRecovered_sourceEmbedding, A.sourceProductState_alpha_symm]

theorem cstarRegionalStateRecovered_one : cstarRegionalStateRecovered R 1 = 1 := by
  rw [cstarRegionalStateRecovered_apply, map_one, cstarProductStateRecovered_one]

theorem cstarRegionalStateRecovered_positive (T : R.targetCStar) :
    ∃ r : ℝ, 0 ≤ r ∧ cstarRegionalStateRecovered R (star T * T) = (r : ℂ) := by
  obtain ⟨r, hr, hval⟩ := cstarProductStateRecovered_positive R (R.cstarAlpha.symm T)
  refine ⟨r, hr, ?_⟩
  rw [cstarRegionalStateRecovered_apply, map_mul, map_star, hval]

/-- **The recovered regional state is a state**: unital and positive on
squares. -/
theorem cstarRegionalStateRecovered_isAlgebraicState :
    IsAlgebraicState (cstarRegionalStateRecovered R).toLinearMap :=
  ⟨cstarRegionalStateRecovered_one R, fun T => cstarRegionalStateRecovered_positive R T⟩

/-- **The recovery gate of P56R.**  The recovered regional state, transported
through the exact P55D C⋆ `alpha`, is the recovered pure/mixed product state on
the whole concrete quasi-local C⋆-algebra.  Neither side carries a supplied
boundedness, positivity or state hypothesis. -/
theorem cstarRegionalStateRecovered_cstarAlpha (T : R.sourceCStar) :
    cstarRegionalStateRecovered R (R.cstarAlpha T) = cstarProductStateRecovered R T := by
  rw [cstarRegionalStateRecovered_apply, StarAlgEquiv.symm_apply_apply]

/-- Function form of the recovery gate. -/
theorem cstarRegionalStateRecovered_comp_cstarAlpha :
    (fun T : R.sourceCStar => cstarRegionalStateRecovered R (R.cstarAlpha T))
      = fun T => cstarProductStateRecovered R T :=
  funext (cstarRegionalStateRecovered_cstarAlpha R)

end SourceConcreteRep

end AlphaData

end Recovery

end LocalHyperbolicAlpha

end StabilizerHyperfinite
