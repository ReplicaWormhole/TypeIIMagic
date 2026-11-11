import FiniteFiber.FullPauliSupportLocality
import FiniteFiber.FinitePauliStabilizer

/-!
# Finite stabilizer densities from full Pauli words

This file connects an **explicitly finite** consistent stabilizer subgroup of
the algebraic normal-form group `FullPauliWord Site` to its finite-region
matrix image, and identifies the resulting group average with the positive
trace-one stabilizer density already constructed abstractly in the
finite-density layer (`FiniteFiber.FinitePauliStabilizerData`).

Nothing here is global.  Every statement is about one fixed finite region
`F : Finset Site` and one fixed finite subgroup of `FullPauliWord Site`, all of
whose elements are syntactically supported in `F`.

## Supplied hypotheses

The bundled structure `FullPauliRegionStabilizer` states all of them
explicitly:

* `group`, a subgroup of the algebraic full-Pauli group `FullPauliWord Site`;
* `region`, the finite region `F`;
* `groupFintype`, an explicit finiteness datum for the subgroup;
* `supported`, the explicit finite-support realization hypothesis
  `g.label.support ⊆ F` for every `g` in the subgroup (this is exactly the
  condition proved equivalent to finite-region matrix realizability in
  `FiniteFiber.supportedIn_iff_hasFiniteRegionRealization`);
* `involutive`, `g * g = 1` for every `g` in the subgroup, the algebraic form
  of Hermiticity of the represented stabilizer;
* `consistent`, the manuscript's consistency condition
  `negativeIdentity ∉ group`, i.e. the central word `-1` is not a stabilizer.

## What is proved

* `fullPauliRegionMatrix_eq_pauliSign_smul`: the finite-region matrix of a
  member of the subgroup is *exactly* `± P`, a real sign times the phase-free
  Hermitian finite-region Pauli matrix of its canonical labels.  The sign is
  `regionSign`, read off from the total `ZMod 4` phase
  `regionHermitianPhase = a.phase + finiteRegionNormalFormCorrection`, i.e.
  the central phase convention of `FullPauliWord` composed with the
  `X`-then-`Z` normal-form correction fixed in `OneSitePauliNormalForm`.  This
  is the exact sign/central-phase convention of the abstract signed-Pauli
  layer `signedPauliStringMatrix`.
* `stabilizerData`: the subgroup, its finite-region matrix image, and that
  sign convention assemble into an honest
  `FinitePauliStabilizerData ↥D.group D.region.card`; its `injective` and
  `no_negative_identity` fields are *proved*, not assumed.
* `regionToQubitMatrix_regionDensity`: the region-level density
  `ρ_F = 2^{-|F|} ∑_{g ∈ G} g` of the manuscript is, after the canonical
  basis identification `QubitIndex |F| ≃ (↥F → Fin 2)`, literally the abstract
  `FinitePauliStabilizerData.stabilizerDensity` of that data.
* Consequently `ρ_F` is positive semidefinite with trace one, equals its
  trace-normalized code projector `P_F / Tr P_F`, and `Tr P_F = 2^{|F|}/|G|`;
  every stabilizer fixes `P_F`, which is a nonzero self-adjoint idempotent.
* `FullPauliRegionStabilizer.ofGlobalStabilizer` and
  `FullPauliRegionStabilizer.ofGenerators`: the manuscript's local stabilizer
  group `G_{S,F} = G_S ∩ A_F` of a (possibly infinite) global consistent
  stabilizer group — or of a set of pairwise-commuting order-two generators —
  *is* such an explicitly finite subgroup; its finiteness is proved from finite
  support alone.  `regionDensity_ofGenerators` states the resulting positive
  trace-one density directly for that input.
* `zWordStabilizer`: the hypotheses are non-vacuous.  A single `Z` stabilizer
  at one site is an explicitly finite consistent stabilizer subgroup with a
  nonidentity element, and its finite-region matrix is the Hermitian Pauli
  matrix `Z` (`fullPauliRegionMatrix_zWord`).

## What is *not* claimed

No countable stabilizer system is inferred from short-range order, no
exhaustion, no quasilocal algebra, no state on an infinite system, and no GNS
representation.  All algebras here are finite complex matrix algebras.
-/

namespace FiniteFiber

open scoped BigOperators ComplexOrder
open scoped FiniteFiber.FiniteRegionQubitMatrix

variable {Site : Type*} [DecidableEq Site]

/-! ### The canonical basis identification of a finite region -/

/--
The canonical identification of the recursive `|F|`-qubit computational basis
with the bit assignments of the finite region `F`, obtained from the chosen
enumeration `Finset.equivFin` of the region.
-/
noncomputable def regionBasisEquiv (F : Finset Site) :
    QubitIndex F.card ≃ finiteRegionBasis F :=
  (qubitIndexFinEquiv F.card).trans
    (Equiv.arrowCongr F.equivFin (Equiv.refl (Fin 2))).symm

omit [DecidableEq Site] in
@[simp] theorem regionBasisEquiv_apply (F : Finset Site) (x : QubitIndex F.card)
    (i : ↥F) :
    regionBasisEquiv F x i = qubitIndexFinEquiv F.card x (F.equivFin i) := rfl

/--
The induced star-algebra identification of the finite-region matrix algebra
with the `|F|`-qubit matrix algebra of the abstract finite-density layer.
-/
noncomputable def regionToQubitMatrix (F : Finset Site) :
    finiteRegionQubitAlgebra F ≃ₐ[ℂ]
      Matrix (QubitIndex F.card) (QubitIndex F.card) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (regionBasisEquiv F).symm

theorem regionToQubitMatrix_apply (F : Finset Site)
    (A : finiteRegionQubitAlgebra F) (u v : QubitIndex F.card) :
    regionToQubitMatrix F A u v = A (regionBasisEquiv F u) (regionBasisEquiv F v) :=
  rfl

/-- The basis identification is inverted by the reverse reindexing. -/
theorem submatrix_regionToQubitMatrix (F : Finset Site)
    (A : finiteRegionQubitAlgebra F) :
    (regionToQubitMatrix F A).submatrix (regionBasisEquiv F).symm
      (regionBasisEquiv F).symm = A := by
  funext x y
  simp [regionToQubitMatrix_apply]

/-- The basis identification carries traces to traces. -/
theorem trace_regionToQubitMatrix (F : Finset Site)
    (A : finiteRegionQubitAlgebra F) :
    (regionToQubitMatrix F A).trace = A.trace :=
  trace_reindex (regionBasisEquiv F).symm A

/--
The basis identification carries a finite-region phase-free Pauli matrix to the
tensor-product Pauli string of the enumerated labels.
-/
theorem regionToQubitMatrix_pauliMatrix (F : Finset Site) (b : ↥F → PauliLabel) :
    regionToQubitMatrix F (finiteRegionPauliMatrix F b) =
      pauliStringMatrix (fun j => b (F.equivFin.symm j)) := by
  funext u v
  rw [regionToQubitMatrix_apply, pauliStringMatrix_apply_qubitIndexFinEquiv]
  refine Fintype.prod_equiv F.equivFin
    (fun i : ↥F => PauliLabel.matrix (b i)
      (regionBasisEquiv F u i) (regionBasisEquiv F v i))
    (fun j : Fin F.card => PauliLabel.matrix (b (F.equivFin.symm j))
      (qubitIndexFinEquiv F.card u j) (qubitIndexFinEquiv F.card v j)) ?_
  intro i
  simp

/-- The basis identification is trace-preserving and multiplicative. -/
theorem regionToQubitMatrix_symm_apply (F : Finset Site)
    (A : Matrix (QubitIndex F.card) (QubitIndex F.card) ℂ) :
    (regionToQubitMatrix F).symm A =
      Matrix.reindex (regionBasisEquiv F) (regionBasisEquiv F) A := rfl

/-! ### The sign of a Hermitian full-Pauli word in a finite region -/

/--
The total `ZMod 4` phase of a full Pauli word inside the finite region `F`:
its central phase together with the summed `X`-then-`Z` normal-form
correction of the region.
-/
noncomputable def regionHermitianPhase (F : Finset Site) (a : FullPauliWord Site) :
    ZMod 4 :=
  a.phase + finiteRegionNormalFormCorrection F (restrictLabel F a.label)

/-- The canonical Hermitian Pauli labels of a full Pauli word on the region `F`. -/
noncomputable def regionPauliLabels (F : Finset Site) (a : FullPauliWord Site) :
    ↥F → PauliLabel :=
  fun i => FullPauliWord.localPauliLabel a i.val

omit [DecidableEq Site] in
/--
The finite-region matrix of a full Pauli word is its total phase factor times
the phase-free Hermitian finite-region Pauli matrix of its canonical labels.
-/
theorem fullPauliRegionMatrix_eq_regionHermitianPhase_smul
    (F : Finset Site) (a : FullPauliWord Site) :
    fullPauliRegionMatrix F a =
      zmod4PhaseFactor (regionHermitianPhase F a) •
        finiteRegionPauliMatrix F (regionPauliLabels F a) := by
  rw [fullPauliRegionMatrix,
    finiteRegionNormalFormMatrix_eq_phase_smul_pauliMatrix, smul_smul,
    ← zmod4PhaseFactor_add]
  rfl

/-- Sitewise, the self-crossing sign exponent is twice the Hermitian correction. -/
theorem phaseEmbed_self_mul_eq_two_correction (q : ProjectivePauliLabel) :
    FullPauliWord.phaseEmbed (q.2 * q.1) =
      normalFormHermitianCorrection q + normalFormHermitianCorrection q := by
  obtain ⟨x, z⟩ := q
  fin_cases x <;> fin_cases z <;> decide

omit [DecidableEq Site] in
/-- The self-cocycle of a word supported in `F` is twice its summed correction. -/
theorem cocycle_self_eq_two_correction
    (F : Finset Site) (a : FullPauliWord Site) (ha : a.label.support ⊆ F) :
    FullPauliWord.cocycle a.label a.label =
      finiteRegionNormalFormCorrection F (restrictLabel F a.label) +
        finiteRegionNormalFormCorrection F (restrictLabel F a.label) := by
  rw [cocycle_eq_finiteRegionNormalFormCocycle F a.label a.label ha,
    finiteRegionNormalFormCocycle, finiteRegionNormalFormCorrection,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    phaseEmbed_self_mul_eq_two_correction (restrictLabel F a.label i)

omit [DecidableEq Site] in
/--
An involutive full Pauli word supported in `F` has a total region phase of
order two: the represented matrix is real-signed, never `±i`.
-/
theorem regionHermitianPhase_add_self
    (F : Finset Site) (a : FullPauliWord Site) (ha : a.label.support ⊆ F)
    (hinv : a * a = 1) :
    regionHermitianPhase F a + regionHermitianPhase F a = 0 := by
  have hphase : a.phase + a.phase + FullPauliWord.cocycle a.label a.label = 0 :=
    congrArg FullPauliWord.phase hinv
  rw [cocycle_self_eq_two_correction F a ha] at hphase
  rw [regionHermitianPhase]
  linear_combination (norm := abel_nf) hphase

omit [DecidableEq Site] in
/-- The total region phase of an involutive supported word is `0` or `2`. -/
theorem regionHermitianPhase_eq_zero_or_two
    (F : Finset Site) (a : FullPauliWord Site) (ha : a.label.support ⊆ F)
    (hinv : a * a = 1) :
    regionHermitianPhase F a = 0 ∨ regionHermitianPhase F a = 2 :=
  FullPauliWord.phase_eq_zero_or_two_of_double_eq_zero _
    (regionHermitianPhase_add_self F a ha hinv)

/--
The Hermitian sign of a full Pauli word in the region `F`: `true` exactly when
its total region phase is the central sign exponent `2`.
-/
noncomputable def regionSign (F : Finset Site) (a : FullPauliWord Site) : Bool :=
  decide (regionHermitianPhase F a = 2)

omit [DecidableEq Site] in
/--
**The sign convention.**  For an involutive word supported in `F`, its
finite-region matrix is exactly the real sign `±1` times the phase-free
Hermitian finite-region Pauli matrix of its canonical labels.
-/
theorem fullPauliRegionMatrix_eq_pauliSign_smul
    (F : Finset Site) (a : FullPauliWord Site) (ha : a.label.support ⊆ F)
    (hinv : a * a = 1) :
    fullPauliRegionMatrix F a =
      pauliSign (regionSign F a) •
        finiteRegionPauliMatrix F (regionPauliLabels F a) := by
  rw [fullPauliRegionMatrix_eq_regionHermitianPhase_smul]
  congr 1
  rcases regionHermitianPhase_eq_zero_or_two F a ha hinv with h | h
  · rw [h, zmod4PhaseFactor_zero, pauliSign, regionSign, h]
    norm_num
    decide
  · rw [h, zmod4PhaseFactor_two, pauliSign, regionSign, h]
    norm_num

omit [DecidableEq Site] in
/-- Convention regression: the identity word has the positive sign. -/
theorem regionSign_one (F : Finset Site) :
    regionSign F (1 : FullPauliWord Site) = false := by
  have h : regionHermitianPhase F (1 : FullPauliWord Site) = 0 := by
    rw [regionHermitianPhase,
      show restrictLabel F (1 : FullPauliWord Site).label = fun _ => 0 from rfl,
      finiteRegionNormalFormCorrection_zero]
    rfl
  rw [regionSign, h]
  decide

omit [DecidableEq Site] in
/-- Convention regression: the central word `-1` has the negative sign. -/
theorem regionSign_negativeIdentity (F : Finset Site) :
    regionSign F (FullPauliWord.negativeIdentity (Site := Site)) = true := by
  have h : regionHermitianPhase F
      (FullPauliWord.negativeIdentity (Site := Site)) = 2 := by
    rw [regionHermitianPhase,
      show restrictLabel F (FullPauliWord.negativeIdentity (Site := Site)).label
        = fun _ => 0 from rfl,
      finiteRegionNormalFormCorrection_zero]
    rfl
  rw [regionSign, h]
  decide

/-! ### Traces of finite-region Pauli matrices -/

/-- The computational basis of a finite region has the expected dimension. -/
theorem card_finiteRegionBasis (F : Finset Site) :
    Fintype.card (finiteRegionBasis F) = 2 ^ F.card := by
  simp [finiteRegionBasis]

/-- A finite-region Pauli string with a nonidentity factor is traceless. -/
theorem trace_finiteRegionPauliMatrix_eq_zero_of_exists_ne_I
    (F : Finset Site) (b : ↥F → PauliLabel) (h : ∃ i, b i ≠ PauliLabel.I) :
    (finiteRegionPauliMatrix F b).trace = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [← trace_regionToQubitMatrix, regionToQubitMatrix_pauliMatrix]
  refine pauliStringMatrix_trace_eq_zero_of_exists_ne_I _ ⟨F.equivFin i, ?_⟩
  simpa using hi

/-! ### An explicitly finite consistent stabilizer subgroup in a finite region -/

/--
An **explicitly finite** consistent stabilizer subgroup of the algebraic
full-Pauli group, together with a finite region containing the support of all
its elements.  Every hypothesis of the finite-density identity below is a
field of this structure; nothing is inferred from an infinite lattice.
-/
structure FullPauliRegionStabilizer (Site : Type*) [DecidableEq Site] where
  /-- The stabilizer subgroup of the algebraic full-Pauli group. -/
  group : Subgroup (FullPauliWord Site)
  /-- The finite region carrying the matrix realization. -/
  region : Finset Site
  /-- The explicit finiteness datum of the subgroup. -/
  groupFintype : Fintype ↥group
  /-- Every stabilizer is syntactically supported in the region. -/
  supported : ∀ g ∈ group, (g : FullPauliWord Site).label.support ⊆ region
  /-- Every stabilizer squares to the identity word (algebraic Hermiticity). -/
  involutive : ∀ g ∈ group, g * g = 1
  /-- Consistency: the central word `-1` is not a stabilizer. -/
  consistent : FullPauliWord.negativeIdentity (Site := Site) ∉ group

attribute [instance] FullPauliRegionStabilizer.groupFintype

namespace FullPauliRegionStabilizer

variable (D : FullPauliRegionStabilizer Site)

/-- A finite involutive subgroup is abelian, hence a consistent stabilizer group. -/
noncomputable def toConsistentStabilizerGroup : FullPauliWord.ConsistentStabilizerGroup Site where
  group := D.group
  commute := by
    intro g h
    have hgh : ((g : FullPauliWord Site) * h) * ((g : FullPauliWord Site) * h) = 1 :=
      D.involutive _ (mul_mem g.2 h.2)
    have hg : (g : FullPauliWord Site) = (g : FullPauliWord Site)⁻¹ :=
      eq_inv_of_mul_eq_one_left (D.involutive _ g.2)
    have hh : (h : FullPauliWord Site) = (h : FullPauliWord Site)⁻¹ :=
      eq_inv_of_mul_eq_one_left (D.involutive _ h.2)
    show (g : FullPauliWord Site) * h = (h : FullPauliWord Site) * g
    calc (g : FullPauliWord Site) * h = ((g : FullPauliWord Site) * h)⁻¹ :=
          eq_inv_of_mul_eq_one_left hgh
      _ = (h : FullPauliWord Site)⁻¹ * (g : FullPauliWord Site)⁻¹ := mul_inv_rev _ _
      _ = (h : FullPauliWord Site) * g := by rw [← hg, ← hh]
  involutive := fun g => D.involutive _ g.2
  no_negative_identity := D.consistent

/-- A stabilizer with trivial projective label is the identity word. -/
theorem eq_one_of_label_eq_zero (g : D.group)
    (hlabel : (g : FullPauliWord Site).label = 0) :
    (g : FullPauliWord Site) = 1 :=
  FullPauliWord.element_eq_one_of_label_eq_zero D.toConsistentStabilizerGroup g hlabel

/--
A stabilizer whose finite-region matrix is a nonzero scalar multiple of the
identity is the identity word.  This is the consistency step: tracelessness of
nonidentity Pauli strings forces the trivial label, and the excluded central
word `-1` then forces the trivial phase.
-/
theorem eq_one_of_regionMatrix_eq_smul_one (g : D.group) (c : ℂ) (hc : c ≠ 0)
    (h : fullPauliRegionMatrix D.region (g : FullPauliWord Site) = c • 1) :
    (g : FullPauliWord Site) = 1 := by
  refine D.eq_one_of_label_eq_zero g ?_
  by_contra hne
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
  have hiF : i ∈ D.region :=
    D.supported _ g.2 (Finsupp.mem_support_iff.mpr hi)
  have hlabelI : regionPauliLabels D.region (g : FullPauliWord Site) ⟨i, hiF⟩ ≠
      PauliLabel.I := by
    rw [regionPauliLabels, FullPauliWord.localPauliLabel,
      Ne, PauliLabel.ofProjectiveCoordinates_eq_I_iff]
    exact hi
  have htr0 : (fullPauliRegionMatrix D.region (g : FullPauliWord Site)).trace = 0 := by
    rw [fullPauliRegionMatrix_eq_regionHermitianPhase_smul, Matrix.trace_smul,
      trace_finiteRegionPauliMatrix_eq_zero_of_exists_ne_I _ _ ⟨⟨i, hiF⟩, hlabelI⟩,
      smul_zero]
  rw [h, Matrix.trace_smul, Matrix.trace_one, card_finiteRegionBasis] at htr0
  exact hc (by simpa [pow_ne_zero] using htr0)

/-- The finite-region matrix realization of the stabilizer subgroup. -/
noncomputable def regionRepresentation :
    D.group →* Matrix (QubitIndex D.region.card) (QubitIndex D.region.card) ℂ where
  toFun g := regionToQubitMatrix D.region
    (fullPauliRegionMatrix D.region (g : FullPauliWord Site))
  map_one' := by
    rw [show ((1 : D.group) : FullPauliWord Site) = 1 from rfl,
      fullPauliRegionMatrix_one, map_one]
  map_mul' g h := by
    rw [show ((g * h : D.group) : FullPauliWord Site) =
        (g : FullPauliWord Site) * h from rfl,
      fullPauliRegionMatrix_mul _ _ _ (D.supported _ g.2), map_mul]

@[simp] theorem regionRepresentation_apply (g : D.group) :
    D.regionRepresentation g =
      regionToQubitMatrix D.region
        (fullPauliRegionMatrix D.region (g : FullPauliWord Site)) := rfl

/-- The realization is injective on the stabilizer subgroup. -/
theorem regionRepresentation_injective : Function.Injective D.regionRepresentation := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine D.eq_one_of_regionMatrix_eq_smul_one g 1 one_ne_zero ?_
  rw [one_smul]
  apply (regionToQubitMatrix D.region).injective
  rw [map_one]
  exact hg

/-- No stabilizer is realized by the central matrix `-1`. -/
theorem regionRepresentation_ne_neg_one (g : D.group) :
    D.regionRepresentation g ≠
      (-1 : Matrix (QubitIndex D.region.card) (QubitIndex D.region.card) ℂ) := by
  intro hneg
  have hmatrix : fullPauliRegionMatrix D.region (g : FullPauliWord Site) =
      (-1 : ℂ) • 1 := by
    apply (regionToQubitMatrix D.region).injective
    rw [map_smul, map_one]
    simpa using hneg
  have hone : (g : FullPauliWord Site) = 1 :=
    D.eq_one_of_regionMatrix_eq_smul_one g (-1) (by norm_num) hmatrix
  rw [hone, fullPauliRegionMatrix_one] at hmatrix
  have hentry := congrFun (congrFun hmatrix (fun _ => 0)) (fun _ => 0)
  rw [Matrix.one_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq] at hentry
  norm_num at hentry

/--
**The abstract finite-density data.**  The finite consistent stabilizer
subgroup, its finite-region matrix image and the Hermitian sign convention
`regionSign` assemble into the signed-Pauli stabilizer data of the
finite-density layer.  Faithfulness and the exclusion of `-1` are proved, not
assumed.
-/
noncomputable def stabilizerData :
    FinitePauliStabilizerData D.group D.region.card where
  representation := D.regionRepresentation
  negative g := regionSign D.region (g : FullPauliWord Site)
  labels g j :=
    regionPauliLabels D.region (g : FullPauliWord Site) (D.region.equivFin.symm j)
  representation_eq g := by
    rw [regionRepresentation_apply,
      fullPauliRegionMatrix_eq_pauliSign_smul _ _ (D.supported _ g.2)
        (D.involutive _ g.2),
      map_smul, regionToQubitMatrix_pauliMatrix]
    exact (FinitePauliStabilizerData.signedPauliStringMatrix_eq_signedPauliTerm _ _).symm
  injective := D.regionRepresentation_injective
  no_negative_identity := D.regionRepresentation_ne_neg_one

/-! ### The finite-region stabilizer density -/

/-- The unnormalized local stabilizer sum `∑_{g ∈ G} g` on the region. -/
noncomputable def regionSum : finiteRegionQubitAlgebra D.region :=
  ∑ g : D.group, fullPauliRegionMatrix D.region (g : FullPauliWord Site)

/-- The local code projector `P_F = |G|⁻¹ ∑_{g ∈ G} g` of the manuscript. -/
noncomputable def regionProjector : finiteRegionQubitAlgebra D.region :=
  (Fintype.card D.group : ℂ)⁻¹ • D.regionSum

/-- The local density matrix `ρ_F = 2^{-|F|} ∑_{g ∈ G} g` of the manuscript. -/
noncomputable def regionDensity : finiteRegionQubitAlgebra D.region :=
  ((2 : ℂ) ^ D.region.card)⁻¹ • D.regionSum

/-- The basis identification carries the local sum to the abstract sum. -/
theorem regionToQubitMatrix_regionSum :
    regionToQubitMatrix D.region D.regionSum = D.stabilizerData.stabilizerSum := by
  rw [regionSum, map_sum]
  rfl

/-- The basis identification carries the local code projector to the abstract one. -/
theorem regionToQubitMatrix_regionProjector :
    regionToQubitMatrix D.region D.regionProjector =
      D.stabilizerData.stabilizerProjector := by
  rw [regionProjector, map_smul, regionToQubitMatrix_regionSum]
  rfl

/--
**The finite density identity.**  After the canonical basis identification of
the finite region with the `|F|`-qubit computational basis, the group average
`ρ_F = 2^{-|F|} ∑_{g ∈ G} g` of the finite-region matrix image is *exactly* the
stabilizer density constructed abstractly in the finite-density layer, with the
same sign and central-phase convention.
-/
theorem regionToQubitMatrix_regionDensity :
    regionToQubitMatrix D.region D.regionDensity =
      D.stabilizerData.stabilizerDensity := by
  rw [regionDensity, map_smul, regionToQubitMatrix_regionSum]
  rfl

/-- The basis identification preserves adjoints. -/
theorem regionToQubitMatrix_star (F : Finset Site) (A : finiteRegionQubitAlgebra F) :
    regionToQubitMatrix F (star A) = star (regionToQubitMatrix F A) := rfl

/-! ### The manuscript's finite-volume conclusions -/

/-- Every stabilizer fixes the local code projector: `g P_F = P_F`. -/
theorem fullPauliRegionMatrix_mul_regionProjector (g : D.group) :
    fullPauliRegionMatrix D.region (g : FullPauliWord Site) * D.regionProjector =
      D.regionProjector := by
  apply (regionToQubitMatrix D.region).injective
  rw [map_mul, regionToQubitMatrix_regionProjector]
  exact D.stabilizerData.representation_mul_stabilizerProjector_left g

/-- The local code projector is a self-adjoint idempotent. -/
theorem regionProjector_isStarProjection : IsStarProjection D.regionProjector := by
  constructor
  · apply (regionToQubitMatrix D.region).injective
    rw [map_mul, regionToQubitMatrix_regionProjector]
    exact D.stabilizerData.stabilizerProjector_isIdempotent
  · change star D.regionProjector = D.regionProjector
    apply (regionToQubitMatrix D.region).injective
    rw [regionToQubitMatrix_star, regionToQubitMatrix_regionProjector]
    exact D.stabilizerData.stabilizerProjector_isSelfAdjoint

/-- The local code projector has the manuscript's trace `2^{|F|}/|G|`. -/
theorem regionProjector_trace :
    D.regionProjector.trace = (Fintype.card D.group : ℂ)⁻¹ * (2 : ℂ) ^ D.region.card := by
  rw [← trace_regionToQubitMatrix, regionToQubitMatrix_regionProjector]
  exact D.stabilizerData.stabilizerProjector_trace

/-- The local density matrix has trace one. -/
theorem regionDensity_trace : D.regionDensity.trace = 1 := by
  rw [← trace_regionToQubitMatrix, regionToQubitMatrix_regionDensity]
  exact D.stabilizerData.stabilizerDensity_trace

/-- The local density matrix is the trace-normalized local code projector. -/
theorem regionDensity_eq_trace_normalized_regionProjector :
    D.regionDensity = (D.regionProjector.trace)⁻¹ • D.regionProjector := by
  apply (regionToQubitMatrix D.region).injective
  rw [regionToQubitMatrix_regionDensity, map_smul,
    regionToQubitMatrix_regionProjector, ← trace_regionToQubitMatrix,
    regionToQubitMatrix_regionProjector]
  exact D.stabilizerData.stabilizerDensity_eq_trace_normalized_projector

/-- The local density matrix is positive semidefinite. -/
theorem regionDensity_posSemidef : D.regionDensity.PosSemidef := by
  rw [← submatrix_regionToQubitMatrix D.region D.regionDensity,
    regionToQubitMatrix_regionDensity]
  exact (Matrix.posSemidef_submatrix_equiv (regionBasisEquiv D.region).symm).mpr
    D.stabilizerData.stabilizerDensity_posSemidef

/-- The local code projector is positive semidefinite and nonzero. -/
theorem regionProjector_ne_zero : D.regionProjector ≠ 0 := by
  intro hzero
  refine D.stabilizerData.stabilizerProjector_ne_zero ?_
  rw [← regionToQubitMatrix_regionProjector, hzero, map_zero]

end FullPauliRegionStabilizer

/-! ### Non-vacuity: explicit finite consistent stabilizer subgroups -/

/-- The two-element subgroup generated by an involutive full Pauli word. -/
def pairSubgroup (z : FullPauliWord Site) (hz : z * z = 1) :
    Subgroup (FullPauliWord Site) where
  carrier := {1, z}
  one_mem' := Set.mem_insert _ _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hz]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_left hz)

omit [DecidableEq Site] in
@[simp] theorem mem_pairSubgroup_iff (z : FullPauliWord Site) (hz : z * z = 1)
    (a : FullPauliWord Site) : a ∈ pairSubgroup z hz ↔ a = 1 ∨ a = z := by
  simp [pairSubgroup, Set.mem_insert_iff]

/-- The two-element subgroup generated by an involutive word is finite. -/
noncomputable def pairSubgroupFintype (z : FullPauliWord Site) (hz : z * z = 1) :
    Fintype ↥(pairSubgroup z hz) := by
  have : Finite ↥(pairSubgroup z hz) :=
    Set.Finite.to_subtype ((Set.finite_singleton z).insert 1)
  exact Fintype.ofFinite _

/--
Any involutive full Pauli word other than the central `-1`, together with a
finite region containing its support, is an explicitly finite consistent
stabilizer subgroup in the sense of `FullPauliRegionStabilizer`.
-/
noncomputable def FullPauliRegionStabilizer.ofInvolutiveWord
    (z : FullPauliWord Site) (hz : z * z = 1) (F : Finset Site)
    (hsupp : z.label.support ⊆ F)
    (hne : z ≠ FullPauliWord.negativeIdentity (Site := Site)) :
    FullPauliRegionStabilizer Site where
  group := pairSubgroup z hz
  region := F
  groupFintype := pairSubgroupFintype z hz
  supported := by
    intro g hg
    rcases (mem_pairSubgroup_iff z hz g).mp hg with rfl | rfl
    · show (0 : ProjectivePauliWord Site).support ⊆ F
      simp
    · exact hsupp
  involutive := by
    intro g hg
    rcases (mem_pairSubgroup_iff z hz g).mp hg with rfl | rfl
    · exact one_mul 1
    · exact hz
  consistent := by
    intro hmem
    rcases (mem_pairSubgroup_iff z hz _).mp hmem with h | h
    · exact FullPauliWord.negativeIdentity_ne_one h
    · exact hne h.symm

omit [DecidableEq Site] in
/-- The subgroup generated by an involutive word is exactly the two-element group. -/
theorem closure_singleton_eq_pairSubgroup (z : FullPauliWord Site) (hz : z * z = 1) :
    Subgroup.closure ({z} : Set (FullPauliWord Site)) = pairSubgroup z hz := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact (mem_pairSubgroup_iff z hz a).mpr (Or.inr ha)
  · intro a ha
    rcases (mem_pairSubgroup_iff z hz a).mp ha with rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure rfl

/--
A single involutive word other than `-1` is a consistent stabilizer generator
system in the sense of `FullPauliWord.StabilizerGeneratorData`.
-/
noncomputable def singleWordGeneratorData (z : FullPauliWord Site) (hz : z * z = 1)
    (hne : z ≠ FullPauliWord.negativeIdentity (Site := Site)) :
    FullPauliWord.StabilizerGeneratorData Site where
  generators := {z}
  pairwise_commute := Set.pairwise_singleton _ _
  generator_involutive := by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hz
  no_negative_identity := by
    rw [closure_singleton_eq_pairSubgroup z hz]
    intro hmem
    rcases (mem_pairSubgroup_iff z hz _).mp hmem with h | h
    · exact FullPauliWord.negativeIdentity_ne_one h
    · exact hne h.symm

/-! ### The manuscript's local stabilizer group `G_{S,F} = G_S ∩ A_F` -/

/--
The local stabilizer group of a (possibly infinite) global stabilizer subgroup
in a finite region: the stabilizers syntactically supported in `F`.  This is
the syntactic form of the manuscript's `G_{S,F} = G_S ∩ A_F`; by
`supportedIn_iff_hasFiniteRegionRealization`, the support condition is exactly
realizability inside the local matrix algebra of `F`.
-/
noncomputable def localStabilizerSubgroup (S : Subgroup (FullPauliWord Site))
    (F : Finset Site) : Subgroup (FullPauliWord Site) :=
  S ⊓ FullPauliWord.localGroup F

theorem mem_localStabilizerSubgroup_iff (S : Subgroup (FullPauliWord Site))
    (F : Finset Site) (a : FullPauliWord Site) :
    a ∈ localStabilizerSubgroup S F ↔ a ∈ S ∧ a.label.support ⊆ F :=
  Subgroup.mem_inf

/-- The local stabilizer group of a finite region is finite, with no assumption on `S`. -/
noncomputable def localStabilizerSubgroupFintype (S : Subgroup (FullPauliWord Site))
    (F : Finset Site) : Fintype ↥(localStabilizerSubgroup S F) := by
  letI : Fintype ↥(FullPauliWord.localGroup F) := FullPauliWord.localGroupFintype F
  have hinj : Function.Injective
      (fun g : ↥(localStabilizerSubgroup S F) =>
        (⟨g.1, ((mem_localStabilizerSubgroup_iff S F g.1).mp g.2).2⟩ :
          ↥(FullPauliWord.localGroup F))) := by
    intro g h hgh
    exact Subtype.ext (congrArg (fun x : ↥(FullPauliWord.localGroup F) =>
      (x : FullPauliWord Site)) hgh)
  have : Finite ↥(localStabilizerSubgroup S F) := Finite.of_injective _ hinj
  exact Fintype.ofFinite _

/--
**The manuscript's local stabilizer data.**  A global consistent stabilizer
subgroup of `FullPauliWord Site`, all of whose elements are involutive,
restricts to an explicitly finite consistent stabilizer subgroup in every
finite region.  No countability, exhaustion, or long-range-order input is
used: finiteness of the local group is proved from finite support alone.
-/
noncomputable def FullPauliRegionStabilizer.ofGlobalStabilizer
    (S : Subgroup (FullPauliWord Site)) (F : Finset Site)
    (hinv : ∀ g ∈ S, g * g = 1)
    (hcons : FullPauliWord.negativeIdentity (Site := Site) ∉ S) :
    FullPauliRegionStabilizer Site where
  group := localStabilizerSubgroup S F
  region := F
  groupFintype := localStabilizerSubgroupFintype S F
  supported g hg := ((mem_localStabilizerSubgroup_iff S F g).mp hg).2
  involutive g hg := hinv g ((mem_localStabilizerSubgroup_iff S F g).mp hg).1
  consistent hmem :=
    hcons ((mem_localStabilizerSubgroup_iff S F _).mp hmem).1

/--
The manuscript's actual input: a set of pairwise-commuting order-two full
Pauli generators whose generated group excludes `-1` gives, in every finite
region, an explicitly finite consistent stabilizer subgroup.
-/
noncomputable def FullPauliRegionStabilizer.ofGenerators
    (G : FullPauliWord.StabilizerGeneratorData Site) (F : Finset Site) :
    FullPauliRegionStabilizer Site :=
  FullPauliRegionStabilizer.ofGlobalStabilizer (Subgroup.closure G.generators) F
    (fun g hg => G.closure_involutive g hg) G.no_negative_identity

/--
**The manuscript's finite-volume density for a generated stabilizer system.**
For pairwise-commuting order-two full Pauli generators whose group excludes
`-1`, and for any finite region `F`, the group average
`ρ_F = 2^{-|F|} ∑_{g ∈ G_{S,F}} g` of the finite-region matrix images is a
positive semidefinite matrix of trace one, equal to the trace-normalized local
code projector.
-/
theorem regionDensity_ofGenerators
    (G : FullPauliWord.StabilizerGeneratorData Site) (F : Finset Site) :
    (FullPauliRegionStabilizer.ofGenerators G F).regionDensity.PosSemidef ∧
      (FullPauliRegionStabilizer.ofGenerators G F).regionDensity.trace = 1 ∧
      (FullPauliRegionStabilizer.ofGenerators G F).regionDensity =
        ((FullPauliRegionStabilizer.ofGenerators G F).regionProjector.trace)⁻¹ •
          (FullPauliRegionStabilizer.ofGenerators G F).regionProjector :=
  ⟨(FullPauliRegionStabilizer.ofGenerators G F).regionDensity_posSemidef,
    (FullPauliRegionStabilizer.ofGenerators G F).regionDensity_trace,
    (FullPauliRegionStabilizer.ofGenerators G F).regionDensity_eq_trace_normalized_regionProjector⟩

/-- The one-site `Z` word: trivial central phase, projective label `(0,1)` at `s`. -/
noncomputable def zWord (s : Site) : FullPauliWord Site :=
  ⟨0, Finsupp.single s (0, 1)⟩

omit [DecidableEq Site] in
/-- The one-site `Z` word is involutive. -/
theorem zWord_mul_self (s : Site) : zWord s * zWord s = 1 := by
  apply FullPauliWord.ext
  · show (0 : ZMod 4) + 0 + FullPauliWord.cocycle (zWord s).label (zWord s).label = 0
    have hx : FullPauliWord.xCoordinate (zWord s).label = 0 := by
      show Finsupp.mapRange.addMonoidHom _
        (Finsupp.single s ((0, 1) : ZMod 2 × ZMod 2)) = 0
      simp [Finsupp.mapRange_single]
    rw [FullPauliWord.cocycle, hx, FullPauliWord.binaryDot_zero_right, map_zero]
    simp
  · show (Finsupp.single s ((0, 1) : ZMod 2 × ZMod 2)) + Finsupp.single s (0, 1) = 0
    rw [← Finsupp.single_add]
    simp
    decide

omit [DecidableEq Site] in
/-- The one-site `Z` word is not the identity word. -/
theorem zWord_ne_one (s : Site) : zWord s ≠ 1 := by
  intro h
  have hl : Finsupp.single s ((0, 1) : ZMod 2 × ZMod 2) = 0 :=
    congrArg FullPauliWord.label h
  rw [Finsupp.single_eq_zero] at hl
  exact absurd hl (by decide)

omit [DecidableEq Site] in
/-- The one-site `Z` word is not the excluded central word `-1`. -/
theorem zWord_ne_negativeIdentity (s : Site) :
    zWord s ≠ FullPauliWord.negativeIdentity (Site := Site) := by
  intro h
  have hp : (0 : ZMod 4) = 2 := congrArg FullPauliWord.phase h
  exact absurd hp (by decide)

omit [DecidableEq Site] in
/-- The one-site `Z` word is supported at its site. -/
theorem zWord_support (s : Site) : (zWord s).label.support ⊆ {s} :=
  Finsupp.support_single_subset

/--
**Non-vacuity witness.**  A single `Z` stabilizer at one site gives an
explicitly finite consistent stabilizer subgroup with a nonidentity element in
the region `{s}`; all the finite-density conclusions above apply to it.
-/
noncomputable def zWordStabilizer (s : Site) : FullPauliRegionStabilizer Site :=
  FullPauliRegionStabilizer.ofInvolutiveWord (zWord s) (zWord_mul_self s) {s}
    (zWord_support s) (zWord_ne_negativeIdentity s)

omit [DecidableEq Site] in
/-- Convention regression: the one-site `Z` word carries the positive sign. -/
theorem regionSign_zWord (s : Site) : regionSign {s} (zWord s) = false := by
  have h : regionHermitianPhase {s} (zWord s) = 0 := by
    rw [regionHermitianPhase, finiteRegionNormalFormCorrection]
    have hzero : ∀ i : ↥({s} : Finset Site),
        normalFormHermitianCorrection (restrictLabel {s} (zWord s).label i) = 0 := by
      intro i
      have hi : i.val = s := Finset.mem_singleton.mp i.property
      simp [restrictLabel, zWord, hi, normalFormHermitianCorrection]
    rw [Finset.sum_congr rfl fun i _ => hzero i]
    simp [zWord]
  rw [regionSign, h]
  decide

omit [DecidableEq Site] in
/-- The canonical labels of the one-site `Z` word are the Pauli label `Z`. -/
theorem regionPauliLabels_zWord (s : Site) :
    regionPauliLabels {s} (zWord s) = fun _ => PauliLabel.Z := by
  funext i
  have hi : i.val = s := Finset.mem_singleton.mp i.property
  simp [regionPauliLabels, FullPauliWord.localPauliLabel, zWord, hi,
    PauliLabel.ofProjectiveCoordinates]

omit [DecidableEq Site] in
/-- The one-site `Z` word is realized by the Hermitian Pauli matrix `Z`. -/
theorem fullPauliRegionMatrix_zWord (s : Site) :
    fullPauliRegionMatrix {s} (zWord s) =
      finiteRegionPauliMatrix {s} (fun _ => PauliLabel.Z) := by
  rw [fullPauliRegionMatrix_eq_pauliSign_smul _ _ (zWord_support s)
      (zWord_mul_self s),
    regionSign_zWord, regionPauliLabels_zWord, pauliSign, if_neg (by decide),
    one_smul]

/--
**Non-vacuity of the generator-level statement.**  A single `Z` stabilizer at
one site is a consistent stabilizer generator system, so
`regionDensity_ofGenerators` applies to it in every finite region.
-/
noncomputable def zWordGeneratorData (s : Site) :
    FullPauliWord.StabilizerGeneratorData Site :=
  singleWordGeneratorData (zWord s) (zWord_mul_self s) (zWord_ne_negativeIdentity s)

/-- The one-site `Z` stabilizer subgroup is not the trivial group. -/
theorem zWord_mem_zWordStabilizer (s : Site) :
    zWord s ∈ (zWordStabilizer s).group ∧ zWord s ≠ 1 :=
  ⟨(mem_pairSubgroup_iff (zWord s) (zWord_mul_self s) (zWord s)).mpr (Or.inr rfl),
    zWord_ne_one s⟩

end FiniteFiber
