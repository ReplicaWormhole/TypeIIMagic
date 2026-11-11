import AristotleCandidates.ConcretePureMixedProductData
import AristotleCandidates.VacuumRestrictedITPCompletion
import AristotleCandidates.BicommutantVonNeumannCore
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# P57C — the pure coordinate GNS representation is the full type-I factor

**Context declaration.**  Source basis: `main.tex:1945-1963`.

## Plan alignment

* Package `P57C`, lane `H`.  Predecessors: `P59A`
  (`AristotleCandidates.ConcretePureMixedProductData`) and `P57B`
  (`AristotleCandidates.VacuumRestrictedITPCompletion`), both integrated, together with the
  bicommutant infrastructure `AristotleCandidates.BicommutantVonNeumannCore`.
* Gate discharged: identify the constructed pure coordinate GNS representation with the vacuum
  infinite tensor product and prove that the bicommutant of the represented pure coordinate
  algebra is the *whole* algebra of bounded operators on the completed pure space, whence its
  centre is trivial.
* Forbidden downstream claims, none of which is made here: no mixed-UHF identification, no
  regional factor transport, and no trace or weight conclusion.

## Auxiliary assumptions

None beyond the integrated P59A coordinate data (`AlphaData`, `SourceConcreteRep`) and the P57B
vacuum construction.  No `pure_factor`, `pure_commutant`, GNS-unitary or `B(K)`-closure premise
is supplied: every such statement below is proved.  There is no `axiom`, `sorry`, `admit`,
`opaque`, `unsafe` or `implemented_by` declaration in this file.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace AristotleCandidates
namespace PureGNSFactor

open StabilizerHyperfinite StabilizerHyperfinite.LocalHyperbolicAlpha
open CoherentLocalHyperbolic
open scoped ComplexOrder InnerProductSpace ComplexConjugate

variable {L I : Type*} [LinearOrder I] {A : AlphaData L I} (R : A.SourceConcreteRep)

/-! ## 1. `Z`-only pure stage labels -/

/-- The `Z`-only pure coordinate labels of stage `n`: the labels of the Pauli words which are
diagonal in the pure vacuum and supported on selected coordinates. -/
noncomputable def zSet (A : AlphaData L I) (n : ℕ) : Finset (A.SourceLabel n) := by
  classical
  exact Finset.univ.filter (fun v => A.IsPureLabel (v : PauliCoordinateLabels I) ∧
    ∀ i : I, (v : PauliCoordinateLabels I) (Sum.inr i) = 0)

theorem mem_zSet {A : AlphaData L I} {n : ℕ} {v : A.SourceLabel n} :
    v ∈ zSet A n ↔ (A.IsPureLabel (v : PauliCoordinateLabels I) ∧
      ∀ i : I, (v : PauliCoordinateLabels I) (Sum.inr i) = 0) := by
  classical
  rw [zSet, Finset.mem_filter]
  simp

theorem zSet_zero {A : AlphaData L I} {n : ℕ} : (0 : A.SourceLabel n) ∈ zSet A n := by
  refine mem_zSet.mpr ⟨A.isPureLabel_zero, fun i => ?_⟩
  simp

theorem zSet_add {A : AlphaData L I} {n : ℕ} {v w : A.SourceLabel n} (hv : v ∈ zSet A n)
    (hw : w ∈ zSet A n) : v + w ∈ zSet A n := by
  obtain ⟨hv1, hv2⟩ := mem_zSet.mp hv
  obtain ⟨hw1, hw2⟩ := mem_zSet.mp hw
  have hcoe : ((v + w : A.SourceLabel n) : PauliCoordinateLabels I)
      = (v : PauliCoordinateLabels I) + (w : PauliCoordinateLabels I) := rfl
  refine mem_zSet.mpr ⟨?_, fun i => ?_⟩
  · rw [hcoe]; exact A.isPureLabel_add hv1 hw1
  · rw [hcoe, Finsupp.add_apply, hv2, hw2, add_zero]

/-- The stage pairing vanishes against any `Z`-only label. -/
theorem form_eq_zero_of_mem_zSet {A : AlphaData L I} {n : ℕ} (v : A.SourceLabel n)
    {w : A.SourceLabel n} (hw : w ∈ zSet A n) : (A.sourceForm n).form v w = 0 := by
  have hw2 := (mem_zSet.mp hw).2
  show ((v : PauliCoordinateLabels I).sum fun p c =>
      c * Sum.elim (fun i => (w : PauliCoordinateLabels I) (Sum.inr i))
        (fun _ => (0 : PauliBit)) p) = 0
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rcases p with i | i
  · simp [hw2 i]
  · simp

theorem productExpectation_eq_one_of_mem_zSet {A : AlphaData L I} {n : ℕ} {v : A.SourceLabel n}
    (hv : v ∈ zSet A n) : A.productExpectation (v : PauliCoordinateLabels I) = 1 := by
  obtain ⟨h1, h2⟩ := mem_zSet.mp hv
  refine A.productExpectation_of_mem ((A.mem_allowedLabels_iff _).mpr ⟨h2, fun i hi => ?_⟩)
  exact h1 (Sum.inl i) hi

theorem pauliBit_eq_one {x : PauliBit} (hx : x ≠ 0) : x = 1 := by
  revert x
  decide

/-! ## 2. The stage vacuum projection of the pure factor -/

/-- **The stage-`n` vacuum projection** of the pure coordinate factor: the average of the
`Z`-only pure Pauli words of stage `n`. -/
noncomputable def vacProj (R : A.SourceConcreteRep) (n : ℕ) : R.sourceCStar :=
  ((zSet A n).card : ℂ)⁻¹ • ∑ v ∈ zSet A n, R.wordElt n v

theorem card_zSet_ne_zero (A : AlphaData L I) (n : ℕ) : (((zSet A n).card : ℂ)) ≠ 0 := by
  have h : (zSet A n).card ≠ 0 := Finset.card_ne_zero_of_mem zSet_zero
  exact_mod_cast h

theorem zSet_sum_reindex {n : ℕ} {v : A.SourceLabel n} (hv : v ∈ zSet A n)
    (f : A.SourceLabel n → R.sourceCStar) :
    ∑ c ∈ zSet A n, f (v + c) = ∑ c ∈ zSet A n, f c := by
  refine Finset.sum_equiv (Equiv.addLeft v) (fun c => ?_) (fun c _ => rfl)
  constructor
  · intro hc; exact zSet_add hv hc
  · intro hc
    have h : v + (v + c) = c := by
      rw [← add_assoc, pauliBit_add_self_eq_zero, zero_add]
    simpa [h] using zSet_add hv hc

theorem wordElt_mul_vacProj {n : ℕ} {v : A.SourceLabel n} (hv : v ∈ zSet A n) :
    R.wordElt n v * vacProj R n = vacProj R n := by
  rw [vacProj, mul_smul_comm, Finset.mul_sum]
  congr 1
  have h1 : ∀ c ∈ zSet A n, R.wordElt n v * R.wordElt n c = R.wordElt n (v + c) := by
    intro c hc
    rw [R.wordElt_mul, form_eq_zero_of_mem_zSet v hc, pauliSign_zero, one_smul]
  rw [Finset.sum_congr rfl h1]
  exact zSet_sum_reindex R hv (fun c => R.wordElt n c)

theorem vacProj_mul_wordElt {n : ℕ} {v : A.SourceLabel n} (hv : v ∈ zSet A n) :
    vacProj R n * R.wordElt n v = vacProj R n := by
  rw [vacProj, smul_mul_assoc, Finset.sum_mul]
  congr 1
  have h1 : ∀ c ∈ zSet A n, R.wordElt n c * R.wordElt n v = R.wordElt n (v + c) := by
    intro c hc
    rw [R.wordElt_mul, form_eq_zero_of_mem_zSet c hv, pauliSign_zero, one_smul, add_comm]
  rw [Finset.sum_congr rfl h1]
  exact zSet_sum_reindex R hv (fun c => R.wordElt n c)

theorem vacProj_mul_self (n : ℕ) : vacProj R n * vacProj R n = vacProj R n := by
  have h : vacProj R n * vacProj R n
      = ((zSet A n).card : ℂ)⁻¹ • ∑ c ∈ zSet A n, (R.wordElt n c * vacProj R n) := by
    nth_rewrite 1 [vacProj]
    rw [smul_mul_assoc, Finset.sum_mul]
  rw [h, Finset.sum_congr rfl (fun c hc => wordElt_mul_vacProj R hc), Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_zSet_ne_zero A n), one_smul]

theorem star_vacProj (n : ℕ) : star (vacProj R n) = vacProj R n := by
  rw [vacProj, star_smul, star_sum]
  have h1 : ∀ c ∈ zSet A n, star (R.wordElt n c) = R.wordElt n c := by
    intro c hc
    rw [R.wordElt_star, form_eq_zero_of_mem_zSet c hc, pauliSign_zero, one_smul]
  rw [Finset.sum_congr rfl h1]
  congr 1
  simp

theorem vacProj_mem_pureCStar (n : ℕ) : vacProj R n ∈ R.pureCStar := by
  rw [vacProj]
  refine SMulMemClass.smul_mem _ (sum_mem fun c hc => ?_)
  exact R.wordElt_mem_pureCStar (mem_zSet.mp hc).1

theorem totalState_vacProj (n : ℕ) : R.totalStateCLM (vacProj R n) = 1 := by
  rw [vacProj, map_smul, map_sum]
  have h1 : ∀ c ∈ zSet A n, R.totalStateCLM (R.wordElt n c) = 1 := by
    intro c hc
    rw [R.totalStateCLM_wordElt, productExpectation_eq_one_of_mem_zSet hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul,
    inv_mul_cancel₀ (card_zSet_ne_zero A n)]

theorem single_z_mem_sourceLabel {n : ℕ} {v : A.SourceLabel n} {i : I}
    (hi : (v : PauliCoordinateLabels I) (Sum.inr i) ≠ 0) :
    (Finsupp.single (Sum.inl i) (1 : PauliBit)) ∈ A.SourceLabel n := by
  rw [LocalHyperbolicFamily.mem_sourceLabels_iff]
  intro p hp
  have hpv : p = Sum.inl i := by
    have h := Finsupp.support_single_subset hp
    simpa using h
  subst hpv
  have hv := (A.family.mem_sourceLabels_iff A.exhaustion n _).mp v.2 (Sum.inr i)
    (Finsupp.mem_support_iff.mpr hi)
  simpa [site] using hv

/-- **The vacuum projection absorbs the pure Pauli words**: conjugating a pure stage word by
the stage vacuum projection returns the projection scaled by the state value of the word.  This
is the finite-level statement that the pure state restricted to a finite coordinate block is the
vector state of the block vacuum. -/
theorem vacProj_conj_wordElt {n : ℕ} (v : A.SourceLabel n)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I)) :
    vacProj R n * R.wordElt n v * vacProj R n
      = A.productExpectation (v : PauliCoordinateLabels I) • vacProj R n := by
  by_cases hx : ∀ i : I, (v : PauliCoordinateLabels I) (Sum.inr i) = 0
  · have hmem : v ∈ zSet A n := mem_zSet.mpr ⟨hv, hx⟩
    rw [vacProj_mul_wordElt R hmem, vacProj_mul_self,
      productExpectation_eq_one_of_mem_zSet hmem, one_smul]
  · push_neg at hx
    obtain ⟨i, hi⟩ := hx
    set Q := vacProj R n with hQ
    set c0 : A.SourceLabel n :=
      ⟨Finsupp.single (Sum.inl i) (1 : PauliBit), single_z_mem_sourceLabel hi⟩ with hc0def
    have hc0 : c0 ∈ zSet A n := by
      refine mem_zSet.mpr ⟨?_, ?_⟩
      · intro p hp
        have hpv : p = Sum.inl i := by
          have h : p ∈ (Finsupp.single (Sum.inl i) (1 : PauliBit)).support :=
            Finsupp.mem_support_iff.mpr hp
          simpa using Finsupp.support_single_subset h
        subst hpv
        exact hv (Sum.inr i) hi
      · intro j
        show (Finsupp.single (Sum.inl i) (1 : PauliBit)) (Sum.inr j) = 0
        rw [Finsupp.single_apply, if_neg (by simp)]
    have hA : Q * R.wordElt n c0 = Q := vacProj_mul_wordElt R hc0
    have hB : R.wordElt n c0 * Q = Q := wordElt_mul_vacProj R hc0
    have hform1 : (A.sourceForm n).form c0 v = 1 := by
      show ((Finsupp.single (Sum.inl i) (1 : PauliBit)).sum fun p c =>
          c * Sum.elim (fun j => (v : PauliCoordinateLabels I) (Sum.inr j))
            (fun _ => (0 : PauliBit)) p) = 1
      rw [Finsupp.sum_single_index (by simp)]
      simp only [Sum.elim_inl, one_mul]
      exact pauliBit_eq_one hi
    have hform2 : (A.sourceForm n).form v c0 = 0 := form_eq_zero_of_mem_zSet v hc0
    have e1 : Q * R.wordElt n v * Q = -(Q * R.wordElt n (c0 + v) * Q) := by
      calc Q * R.wordElt n v * Q
          = (Q * R.wordElt n c0) * R.wordElt n v * Q := by rw [hA]
        _ = Q * (R.wordElt n c0 * R.wordElt n v) * Q := by simp only [mul_assoc]
        _ = Q * ((-1 : ℂ) • R.wordElt n (c0 + v)) * Q := by
              rw [R.wordElt_mul, hform1, pauliSign_one]
        _ = -(Q * R.wordElt n (c0 + v) * Q) := by
              rw [mul_smul_comm, smul_mul_assoc, neg_one_smul]
    have e2 : Q * R.wordElt n (c0 + v) * Q = Q * R.wordElt n v * Q := by
      calc Q * R.wordElt n (c0 + v) * Q
          = Q * R.wordElt n (v + c0) * Q := by rw [add_comm]
        _ = Q * (R.wordElt n v * R.wordElt n c0) * Q := by
              rw [R.wordElt_mul, hform2, pauliSign_zero, one_smul]
        _ = Q * R.wordElt n v * (R.wordElt n c0 * Q) := by simp only [mul_assoc]
        _ = Q * R.wordElt n v * Q := by rw [hB]
    rw [e2] at e1
    have h2 : (2 : ℂ) • (Q * R.wordElt n v * Q) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e1]
      exact neg_add_cancel _
    have hzero : Q * R.wordElt n v * Q = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
    rw [hzero, A.productExpectation_of_not_mem, zero_smul]
    intro hmem
    exact hi (((A.mem_allowedLabels_iff _).mp hmem).1 i)

/-! ## 3. The pure GNS representation -/

noncomputable local instance purePO : PartialOrder R.pureCStar := CStarAlgebra.spectralOrder _

noncomputable local instance pureSOR : StarOrderedRing R.pureCStar :=
  CStarAlgebra.spectralOrderedRing _

/-- **The pure GNS Hilbert space**: the GNS space of the P59A pure marginal state. -/
noncomputable abbrev PureGNS := R.purePositiveState.GNS

theorem purePositiveState_apply (a : R.pureCStar) :
    R.purePositiveState a = R.totalStateCLM (a : R.sourceCStar) := rfl

theorem norm_purePositiveState_le (a : R.pureCStar) : ‖R.purePositiveState a‖ ≤ ‖a‖ := by
  rw [purePositiveState_apply]
  exact R.norm_totalStateCLM_le _

theorem norm_toPreGNS_le (a : R.pureCStar) :
    ‖(R.purePositiveState.toPreGNS a)‖ ≤ 1 * ‖a‖ := by
  have h := PositiveLinearMap.preGNS_norm_sq (f := R.purePositiveState)
    (R.purePositiveState.toPreGNS a)
  have h2 : ‖(R.purePositiveState.toPreGNS a)‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have hre : ((‖(R.purePositiveState.toPreGNS a)‖ ^ 2 : ℝ) : ℂ)
        = R.purePositiveState (star a * a) := by
      simpa using h
    calc (‖(R.purePositiveState.toPreGNS a)‖ ^ 2 : ℝ)
        = ‖((‖(R.purePositiveState.toPreGNS a)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ = ‖(R.purePositiveState (star a * a))‖ := by rw [hre]
      _ ≤ ‖star a * a‖ := norm_purePositiveState_le R _
      _ = ‖a‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- **The canonical map of the pure algebra into its GNS space.** -/
noncomputable def gvecL : R.pureCStar →L[ℂ] PureGNS R :=
  (UniformSpace.Completion.toComplL).comp
    (LinearMap.mkContinuous (R.purePositiveState.toPreGNS.toLinearMap) 1 (norm_toPreGNS_le R))

theorem gvecL_apply (a : R.pureCStar) :
    gvecL R a = ((R.purePositiveState.toPreGNS a : R.purePositiveState.PreGNS) : PureGNS R) := rfl

/-- **The GNS vacuum vector** of the pure coordinate state. -/
noncomputable def vac : PureGNS R := gvecL R 1

theorem vac_def : vac R = gvecL R 1 := rfl

/-- **The GNS representation** of the pure coordinate C⋆-algebra. -/
noncomputable abbrev pureRep : R.pureCStar →⋆ₐ[ℂ] (PureGNS R →L[ℂ] PureGNS R) :=
  R.purePositiveState.gnsStarAlgHom

theorem inner_gvecL (a b : R.pureCStar) :
    ⟪gvecL R a, gvecL R b⟫_ℂ = R.totalStateCLM ((star a * b : R.pureCStar) : R.sourceCStar) := by
  rw [gvecL_apply, gvecL_apply, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]
  rfl

theorem rep_gvecL (a b : R.pureCStar) : pureRep R a (gvecL R b) = gvecL R (a * b) := by
  simp [gvecL, PositiveLinearMap.gnsStarAlgHom]

theorem inner_vac_gvecL (a : R.pureCStar) :
    ⟪vac R, gvecL R a⟫_ℂ = R.totalStateCLM (a : R.sourceCStar) := by
  rw [vac_def, inner_gvecL]
  simp

theorem norm_vac : ‖vac R‖ = 1 := by
  have h : ⟪vac R, vac R⟫_ℂ = 1 := by
    have h1 := inner_vac_gvecL R 1
    rw [← vac_def] at h1
    rw [h1]
    simpa using R.pureMarginal_one
  rw [inner_self_eq_norm_sq_to_K] at h
  have h3 : ((‖vac R‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
  have h4 : ‖vac R‖ ^ 2 = 1 := by exact_mod_cast h3
  nlinarith [norm_nonneg (vac R)]

theorem rep_vac (a : R.pureCStar) : pureRep R a (vac R) = gvecL R a := by
  rw [vac_def]
  refine (rep_gvecL R a 1).trans ?_
  congr 1

theorem denseRange_gvecL : DenseRange (gvecL R) := by
  have h : Set.range (gvecL R) = Set.range ((↑) : R.purePositiveState.PreGNS → PureGNS R) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨R.purePositiveState.toPreGNS a, rfl⟩
    · rintro ⟨p, rfl⟩; exact ⟨R.purePositiveState.ofPreGNS p, rfl⟩
  rw [DenseRange, h]
  exact UniformSpace.Completion.denseRange_coe

/-! ## 4. Pure Pauli words and the vacuum projection inside the pure factor -/

/-- A pure stage Pauli word, as an element of the pure coordinate C⋆-algebra. -/
noncomputable def pureWordP {n : ℕ} (v : A.SourceLabel n)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I)) : R.pureCStar :=
  ⟨R.wordElt n v, R.wordElt_mem_pureCStar hv⟩

@[simp] theorem pureWordP_coe {n : ℕ} (v : A.SourceLabel n)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I)) :
    ((pureWordP R v hv : R.pureCStar) : R.sourceCStar) = R.wordElt n v := rfl

/-- The stage vacuum projection, as an element of the pure coordinate C⋆-algebra. -/
noncomputable def vacProjP (n : ℕ) : R.pureCStar := ⟨vacProj R n, vacProj_mem_pureCStar R n⟩

@[simp] theorem vacProjP_coe (n : ℕ) :
    ((vacProjP R n : R.pureCStar) : R.sourceCStar) = vacProj R n := rfl

theorem vacProjP_star (n : ℕ) : star (vacProjP R n) = vacProjP R n :=
  Subtype.ext (by simpa using star_vacProj R n)

theorem vacProjP_mul_self (n : ℕ) : vacProjP R n * vacProjP R n = vacProjP R n :=
  Subtype.ext (by simpa using vacProj_mul_self R n)

theorem totalState_vacProjP (n : ℕ) :
    R.totalStateCLM ((vacProjP R n : R.pureCStar) : R.sourceCStar) = 1 :=
  totalState_vacProj R n

/-- **The vacuum projection fixes the GNS vacuum vector.** -/
theorem gvecL_vacProjP (n : ℕ) : gvecL R (vacProjP R n) = vac R := by
  have hzero : ⟪gvecL R (vacProjP R n - 1), gvecL R (vacProjP R n - 1)⟫_ℂ = 0 := by
    rw [inner_gvecL]
    have hexp : star (vacProjP R n - 1) * (vacProjP R n - 1)
        = vacProjP R n * vacProjP R n - vacProjP R n - vacProjP R n + 1 := by
      rw [star_sub, star_one, vacProjP_star]
      noncomm_ring
    rw [hexp, vacProjP_mul_self]
    have hc : ((vacProjP R n - vacProjP R n - vacProjP R n + 1 : R.pureCStar) : R.sourceCStar)
        = -(vacProj R n) + 1 := by
      push_cast [vacProjP_coe]
      abel
    have hone : R.totalStateCLM (1 : R.sourceCStar) = 1 := by
      simpa using R.pureMarginal_one
    rw [hc, map_add, map_neg, totalState_vacProj, hone]
    ring
  have h0 : gvecL R (vacProjP R n - 1) = 0 := inner_self_eq_zero.mp hzero
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, vac_def]

/-- **The two-word absorption identity**: conjugating `x⋆ y` by the stage vacuum projection,
for pure stage words `x` and `y`, returns the projection scaled by the pure state value of
`x⋆ y`. -/
theorem vacProj_conj_star_word_mul {k : ℕ} (v w : A.SourceLabel k)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsPureLabel (w : PauliCoordinateLabels I)) :
    vacProj R k * (star (R.wordElt k v) * R.wordElt k w) * vacProj R k
      = R.totalStateCLM (star (R.wordElt k v) * R.wordElt k w) • vacProj R k := by
  have hvw : A.IsPureLabel ((v + w : A.SourceLabel k) : PauliCoordinateLabels I) := by
    have hcoe : ((v + w : A.SourceLabel k) : PauliCoordinateLabels I)
        = (v : PauliCoordinateLabels I) + (w : PauliCoordinateLabels I) := rfl
    rw [hcoe]
    exact A.isPureLabel_add hv hw
  set s1 : ℂ := pauliSign ((A.sourceForm k).form v v) with hs1
  set s2 : ℂ := pauliSign ((A.sourceForm k).form v w) with hs2
  have hprod : star (R.wordElt k v) * R.wordElt k w = (s1 * s2) • R.wordElt k (v + w) := by
    rw [R.wordElt_star, smul_mul_assoc, R.wordElt_mul, smul_smul]
  rw [hprod, map_smul, smul_eq_mul, mul_smul_comm, smul_mul_assoc,
    vacProj_conj_wordElt R (v + w) hvw, R.totalStateCLM_wordElt, smul_smul]

/-! ## 5. Irreducibility of the pure GNS representation -/

/-- The GNS vectors of the pure Pauli words. -/
def wordVecs : Set (PureGNS R) :=
  {u | ∃ (n : ℕ) (v : A.SourceLabel n) (hv : A.IsPureLabel (v : PauliCoordinateLabels I)),
    u = gvecL R (pureWordP R v hv)}

/-- The pure Pauli words, as a subset of the pure coordinate C⋆-algebra. -/
def pureWordSet : Set R.pureCStar :=
  {a | ∃ (n : ℕ) (v : A.SourceLabel n) (hv : A.IsPureLabel (v : PauliCoordinateLabels I)),
    a = pureWordP R v hv}

theorem image_pureWordSet : (gvecL R) '' (pureWordSet R) = wordVecs R := by
  ext u
  constructor
  · rintro ⟨a, ⟨n, v, hv, rfl⟩, rfl⟩
    exact ⟨n, v, hv, rfl⟩
  · rintro ⟨n, v, hv, rfl⟩
    exact ⟨pureWordP R v hv, ⟨n, v, hv, rfl⟩, rfl⟩

/-- **The pure Pauli words span a dense subspace of the pure coordinate C⋆-algebra.** -/
theorem dense_span_pureWordSet :
    Dense ((Submodule.span ℂ (pureWordSet R) : Submodule ℂ R.pureCStar) : Set R.pureCStar) := by
  have hcoe : ((R.pureCStar : StarSubalgebra ℂ R.sourceCStar) : Set R.sourceCStar)
      = closure ((Submodule.span ℂ (R.labelWordSet A.IsPureLabel) :
          Submodule ℂ R.sourceCStar) : Set R.sourceCStar) :=
    R.coe_labelCStarAlg _ _
  have hmap : Submodule.span ℂ (R.labelWordSet A.IsPureLabel)
      ≤ Submodule.map (R.pureCStar.subtype.toLinearMap) (Submodule.span ℂ (pureWordSet R)) := by
    rw [Submodule.span_le]
    rintro T ⟨n, v, hv, rfl⟩
    exact ⟨pureWordP R v hv, Submodule.subset_span ⟨n, v, hv, rfl⟩, rfl⟩
  intro a
  rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball]
  intro ε hε
  have ha : (a : R.sourceCStar) ∈ closure ((Submodule.span ℂ (R.labelWordSet A.IsPureLabel) :
      Submodule ℂ R.sourceCStar) : Set R.sourceCStar) := by
    rw [← hcoe]
    exact a.2
  rw [Metric.mem_closure_iff] at ha
  obtain ⟨y, hy, hdist⟩ := ha ε hε
  obtain ⟨b, hb, hby⟩ := hmap hy
  refine ⟨b, hb, ?_⟩
  rw [Metric.mem_ball, dist_comm]
  have hby' : (b : R.sourceCStar) = y := hby
  have hd : dist (a : R.sourceCStar) (b : R.sourceCStar) < ε := by rw [hby']; exact hdist
  exact hd

/-- **The GNS vectors of the pure Pauli words span a dense subspace of the pure GNS space.** -/
theorem dense_span_wordVecs :
    Dense ((Submodule.span ℂ (wordVecs R) : Submodule ℂ (PureGNS R)) : Set (PureGNS R)) := by
  have himg : ⇑(gvecL R : R.pureCStar →ₗ[ℂ] PureGNS R) '' pureWordSet R = wordVecs R :=
    image_pureWordSet R
  have hmap : Submodule.map (gvecL R : R.pureCStar →ₗ[ℂ] PureGNS R)
      (Submodule.span ℂ (pureWordSet R)) = Submodule.span ℂ (wordVecs R) := by
    rw [Submodule.map_span, himg]
  have hsub : Set.range (gvecL R) ⊆
      closure ((Submodule.span ℂ (wordVecs R) : Submodule ℂ (PureGNS R)) : Set (PureGNS R)) := by
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ closure ((Submodule.span ℂ (pureWordSet R) :
        Submodule ℂ R.pureCStar) : Set R.pureCStar) := dense_span_pureWordSet R a
    have himg2 : (gvecL R) '' closure ((Submodule.span ℂ (pureWordSet R) :
        Submodule ℂ R.pureCStar) : Set R.pureCStar)
        ⊆ closure ((gvecL R) '' ((Submodule.span ℂ (pureWordSet R) :
          Submodule ℂ R.pureCStar) : Set R.pureCStar)) :=
      image_closure_subset_closure_image (gvecL R).continuous
    have h2 : (gvecL R) '' ((Submodule.span ℂ (pureWordSet R) :
        Submodule ℂ R.pureCStar) : Set R.pureCStar)
        = ((Submodule.span ℂ (wordVecs R) : Submodule ℂ (PureGNS R)) : Set (PureGNS R)) := by
      rw [← hmap]; rfl
    rw [h2] at himg2
    exact himg2 ⟨a, ha, rfl⟩
  have hdense := (denseRange_gvecL R)
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense.closure_range]
  exact closure_minimal hsub isClosed_closure

/-- Any closed submodule containing the GNS word vectors is everything. -/
theorem eq_top_of_wordVecs_subset (p : Submodule ℂ (PureGNS R))
    (hp : IsClosed (p : Set (PureGNS R))) (hsub : wordVecs R ⊆ (p : Set (PureGNS R))) :
    (p : Set (PureGNS R)) = Set.univ := by
  have hle : ((Submodule.span ℂ (wordVecs R) : Submodule ℂ (PureGNS R)) : Set (PureGNS R))
      ⊆ (p : Set (PureGNS R)) := fun _ hx => (Submodule.span_le.mpr hsub) hx
  have hcl := (dense_span_wordVecs R).mono hle
  rw [dense_iff_closure_eq, hp.closure_eq] at hcl
  exact hcl

theorem eq_zero_of_inner_wordVecs {z : PureGNS R}
    (h : ∀ u ∈ wordVecs R, ⟪z, u⟫_ℂ = 0) : z = 0 := by
  have hker : ((LinearMap.ker ((innerSL ℂ z : PureGNS R →L[ℂ] ℂ) : PureGNS R →ₗ[ℂ] ℂ) :
      Submodule ℂ (PureGNS R)) : Set (PureGNS R)) = Set.univ := by
    refine eq_top_of_wordVecs_subset R _ ?_ ?_
    · exact (innerSL ℂ z).isClosed_ker
    · intro u hu
      simpa using h u hu
  have hz : z ∈ (LinearMap.ker ((innerSL ℂ z : PureGNS R →L[ℂ] ℂ) : PureGNS R →ₗ[ℂ] ℂ) :
      Submodule ℂ (PureGNS R)) := by
    rw [← SetLike.mem_coe, hker]; trivial
  have hzz : ⟪z, z⟫_ℂ = 0 := by simpa using hz
  exact inner_self_eq_zero.mp hzz

/-- A vector orthogonal to every GNS word vector vanishes (second-slot form). -/
theorem eq_zero_of_inner_wordVecs' {z : PureGNS R}
    (h : ∀ u ∈ wordVecs R, ⟪u, z⟫_ℂ = 0) : z = 0 := by
  refine eq_zero_of_inner_wordVecs R ?_
  intro u hu
  have hc := inner_conj_symm (𝕜 := ℂ) z u
  rw [← hc, h u hu, map_zero]

theorem eq_zero_of_apply_wordVecs {S : PureGNS R →L[ℂ] PureGNS R}
    (h : ∀ u ∈ wordVecs R, S u = 0) : S = 0 := by
  have hker : ((LinearMap.ker (S : PureGNS R →ₗ[ℂ] PureGNS R)) : Set (PureGNS R)) = Set.univ := by
    refine eq_top_of_wordVecs_subset R _ S.isClosed_ker ?_
    intro u hu
    simpa using h u hu
  ext x
  have hx : x ∈ (LinearMap.ker (S : PureGNS R →ₗ[ℂ] PureGNS R)) := by
    rw [← SetLike.mem_coe, hker]; trivial
  simpa using hx

/-- Adjoints of the represented pure algebra. -/
theorem inner_pureRep_left (a : R.pureCStar) (u z : PureGNS R) :
    ⟪pureRep R a u, z⟫_ℂ = ⟪u, pureRep R (star a) z⟫_ℂ := by
  have hstar : pureRep R (star a) = ContinuousLinearMap.adjoint (pureRep R a) :=
    (map_star _ _).trans (ContinuousLinearMap.star_eq_adjoint _)
  have h3 := congrArg (fun S : PureGNS R →L[ℂ] PureGNS R => ⟪u, S z⟫_ℂ) hstar
  exact (ContinuousLinearMap.adjoint_inner_right (pureRep R a) u z).symm.trans h3.symm

/-- Multiplicativity of the pure GNS representation, in applied form. -/
theorem pureRep_mul_apply (a b : R.pureCStar) (u : PureGNS R) :
    pureRep R (a * b) u = pureRep R a (pureRep R b u) :=
  congrArg (fun S : PureGNS R →L[ℂ] PureGNS R => S u) (map_mul (pureRep R) a b)

/-- **The absorption computation for a commutant operator.**  If `Q` is a vector-state absorbing
element (`gvecL Q = vac`) and `star (x * Q) * (y * Q) = c • Q`, then the matrix element of a
commuting operator `T` between the GNS vectors of `x` and `y` is `lam` times their inner
product, where `lam` is the vacuum expectation of `T`. -/
theorem inner_commutant_of_absorb {T : PureGNS R →L[ℂ] PureGNS R}
    (hcomm : ∀ (a : R.pureCStar) (u : PureGNS R), pureRep R a (T u) = T (pureRep R a u))
    (lam : ℂ) (hlam : ⟪vac R, T (vac R)⟫_ℂ = lam)
    (Q x y : R.pureCStar) (hQv : gvecL R Q = vac R) (c : ℂ)
    (hstarmul : star (x * Q) * (y * Q) = c • Q)
    (hinner : ⟪gvecL R x, gvecL R y⟫_ℂ = c) :
    ⟪gvecL R x, T (gvecL R y)⟫_ℂ = lam * ⟪gvecL R x, gvecL R y⟫_ℂ := by
  have hxQ : gvecL R (x * Q) = gvecL R x :=
    (rep_gvecL R x Q).symm.trans
      ((congrArg (fun u => pureRep R x u) hQv).trans (rep_vac R x))
  have hyQ : gvecL R (y * Q) = gvecL R y :=
    (rep_gvecL R y Q).symm.trans
      ((congrArg (fun u => pureRep R y u) hQv).trans (rep_vac R y))
  have hgv : gvecL R (star (x * Q) * (y * Q)) = c • vac R := by
    have h1 := congrArg (fun a : R.pureCStar => gvecL R a) hstarmul
    have h2 : gvecL R (c • Q) = c • gvecL R Q := map_smul (gvecL R) c Q
    rw [hQv] at h2
    exact h1.trans h2
  have step1 : ⟪gvecL R x, T (gvecL R y)⟫_ℂ
      = ⟪gvecL R (x * Q), T (gvecL R (y * Q))⟫_ℂ :=
    congrArg₂ (fun p q => ⟪p, T q⟫_ℂ) hxQ.symm hyQ.symm
  have step2 : ⟪gvecL R (x * Q), T (gvecL R (y * Q))⟫_ℂ
      = ⟪pureRep R (x * Q) (vac R), T (pureRep R (y * Q) (vac R))⟫_ℂ :=
    congrArg₂ (fun p q => ⟪p, T q⟫_ℂ) (rep_vac R (x * Q)).symm (rep_vac R (y * Q)).symm
  have step3 := inner_pureRep_left R (x * Q) (vac R) (T (pureRep R (y * Q) (vac R)))
  have step4 : ⟪vac R, pureRep R (star (x * Q)) (T (pureRep R (y * Q) (vac R)))⟫_ℂ
      = ⟪vac R, T (pureRep R (star (x * Q)) (pureRep R (y * Q) (vac R)))⟫_ℂ :=
    congrArg (fun u => ⟪vac R, u⟫_ℂ) (hcomm (star (x * Q)) _)
  have step5 : pureRep R (star (x * Q)) (pureRep R (y * Q) (vac R))
      = gvecL R (star (x * Q) * (y * Q)) :=
    (pureRep_mul_apply R _ _ _).symm.trans (rep_vac R _)
  have step6 : ⟪vac R, T (pureRep R (star (x * Q)) (pureRep R (y * Q) (vac R)))⟫_ℂ
      = ⟪vac R, T (c • vac R)⟫_ℂ :=
    congrArg (fun u => ⟪vac R, T u⟫_ℂ) (step5.trans hgv)
  have step7 : ⟪vac R, T (c • vac R)⟫_ℂ = c * ⟪vac R, T (vac R)⟫_ℂ :=
    (congrArg (fun u => ⟪vac R, u⟫_ℂ) (map_smul T c (vac R))).trans (inner_smul_right _ _ _)
  have hgoal := step1.trans (step2.trans (step3.trans (step4.trans (step6.trans step7))))
  refine hgoal.trans ?_
  rw [hinner, hlam]
  ring

/-- The stage vacuum projection absorbs a product of two pure stage words, inside the pure
coordinate C⋆-algebra. -/
theorem starmul_absorb_vacProjP {k : ℕ} (v w : A.SourceLabel k)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsPureLabel (w : PauliCoordinateLabels I)) :
    star (pureWordP R v hv * vacProjP R k) * (pureWordP R w hw * vacProjP R k)
      = R.totalStateCLM ((star (pureWordP R v hv) * pureWordP R w hw : R.pureCStar) :
          R.sourceCStar) • vacProjP R k := by
  refine Subtype.ext ?_
  have hl : ((star (pureWordP R v hv * vacProjP R k) *
        (pureWordP R w hw * vacProjP R k) : R.pureCStar) : R.sourceCStar)
      = vacProj R k * (star (R.wordElt k v) * R.wordElt k w) * vacProj R k := by
    simp only [MulMemClass.coe_mul, StarMemClass.coe_star, pureWordP_coe, vacProjP_coe,
      star_mul, star_vacProj, mul_assoc]
  have hr : ((R.totalStateCLM ((star (pureWordP R v hv) * pureWordP R w hw : R.pureCStar) :
        R.sourceCStar) • vacProjP R k : R.pureCStar) : R.sourceCStar)
      = R.totalStateCLM (star (R.wordElt k v) * R.wordElt k w) • vacProj R k := by
    push_cast
    rfl
  rw [hl, hr]
  exact vacProj_conj_star_word_mul R v w hv hw

/-- **The two-word matrix element of a commutant operator.**  For pure Pauli words at a common
stage, an operator commuting with the represented pure algebra has matrix elements proportional
to the corresponding inner products, the constant being its vacuum expectation. -/
theorem inner_word_commutant {T : PureGNS R →L[ℂ] PureGNS R}
    (hcomm : ∀ (a : R.pureCStar) (u : PureGNS R), pureRep R a (T u) = T (pureRep R a u))
    (lam : ℂ) (hlam : ⟪vac R, T (vac R)⟫_ℂ = lam)
    {k : ℕ} (v w : A.SourceLabel k)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsPureLabel (w : PauliCoordinateLabels I)) :
    ⟪gvecL R (pureWordP R v hv), T (gvecL R (pureWordP R w hw))⟫_ℂ
      = lam * ⟪gvecL R (pureWordP R v hv), gvecL R (pureWordP R w hw)⟫_ℂ :=
  inner_commutant_of_absorb R hcomm lam hlam (vacProjP R k) (pureWordP R v hv)
    (pureWordP R w hw) (gvecL_vacProjP R k) _ (starmul_absorb_vacProjP R v w hv hw)
    (inner_gvecL R _ _)

/-- Expansion of a matrix element of `T - lam` in terms of those of `T`. -/
theorem inner_sub_scalar_apply (T : PureGNS R →L[ℂ] PureGNS R) (lam : ℂ) (u z : PureGNS R) :
    ⟪u, (T - lam • (1 : PureGNS R →L[ℂ] PureGNS R)) z⟫_ℂ
      = ⟪u, T z⟫_ℂ - lam * ⟪u, z⟫_ℂ := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

/-- If all matrix elements of `T` between GNS word vectors are `lam` times the corresponding
inner products, then `T` is the scalar `lam`. -/
theorem eq_smul_one_of_word_matrix {T : PureGNS R →L[ℂ] PureGNS R} (lam : ℂ)
    (hk : ∀ {k : ℕ} (v w : A.SourceLabel k)
      (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
      (hw : A.IsPureLabel (w : PauliCoordinateLabels I)),
      ⟪gvecL R (pureWordP R v hv), T (gvecL R (pureWordP R w hw))⟫_ℂ
        = lam * ⟪gvecL R (pureWordP R v hv), gvecL R (pureWordP R w hw)⟫_ℂ) :
    T = lam • (1 : PureGNS R →L[ℂ] PureGNS R) := by
  have hzero : ∀ u ∈ wordVecs R,
      (T - lam • (1 : PureGNS R →L[ℂ] PureGNS R)) u = 0 := by
    rintro _ ⟨m, w, hw, rfl⟩
    refine eq_zero_of_inner_wordVecs' R ?_
    rintro _ ⟨n, v, hv, rfl⟩
    obtain ⟨k, v', w', hv', hw', hev, hew⟩ := R.exists_common_stage v w
    have hvp : A.IsPureLabel (v' : PauliCoordinateLabels I) := by rw [hv']; exact hv
    have hwp : A.IsPureLabel (w' : PauliCoordinateLabels I) := by rw [hw']; exact hw
    have hxv : pureWordP R v hv = pureWordP R v' hvp := Subtype.ext (by simp [hev])
    have hxw : pureWordP R w hw = pureWordP R w' hwp := Subtype.ext (by simp [hew])
    have h1 : ⟪gvecL R (pureWordP R v hv),
          (T - lam • (1 : PureGNS R →L[ℂ] PureGNS R)) (gvecL R (pureWordP R w hw))⟫_ℂ
        = ⟪gvecL R (pureWordP R v' hvp),
          (T - lam • (1 : PureGNS R →L[ℂ] PureGNS R)) (gvecL R (pureWordP R w' hwp))⟫_ℂ :=
      congrArg₂ (fun p q => ⟪gvecL R p,
        (T - lam • (1 : PureGNS R →L[ℂ] PureGNS R)) (gvecL R q)⟫_ℂ) hxv hxw
    exact h1.trans ((inner_sub_scalar_apply R T lam _ _).trans
      (sub_eq_zero_of_eq (hk v' w' hvp hwp)))
  have hTS : T - lam • (1 : PureGNS R →L[ℂ] PureGNS R) = 0 :=
    eq_zero_of_apply_wordVecs R hzero
  rw [sub_eq_zero] at hTS
  exact hTS

/-- **Irreducibility of the pure GNS representation.**  Every bounded operator commuting with
the represented pure coordinate algebra is a scalar. -/
theorem commutant_eq_scalar {T : PureGNS R →L[ℂ] PureGNS R}
    (hT : ∀ a : R.pureCStar, pureRep R a * T = T * pureRep R a) :
    T = (⟪vac R, T (vac R)⟫_ℂ) • (1 : PureGNS R →L[ℂ] PureGNS R) := by
  have hcomm : ∀ (a : R.pureCStar) (u : PureGNS R),
      pureRep R a (T u) = T (pureRep R a u) := by
    intro a u
    have h2 := congrArg (fun f : PureGNS R →L[ℂ] PureGNS R => f u) (hT a)
    simpa using h2
  exact eq_smul_one_of_word_matrix R _
    (fun v w hv hw => inner_word_commutant R hcomm _ rfl v w hv hw)

/-! ## 6. The represented pure algebra generates all of `B(K)` -/

/-- **The represented pure coordinate algebra**, as a star subalgebra of the bounded operators
on the pure GNS space. -/
noncomputable def pureVN : StarSubalgebra ℂ (PureGNS R →L[ℂ] PureGNS R) :=
  (pureRep R).range

theorem mem_pureVN_iff {T : PureGNS R →L[ℂ] PureGNS R} :
    T ∈ pureVN R ↔ ∃ a : R.pureCStar, pureRep R a = T := Iff.rfl

theorem pureRep_mem_pureVN (a : R.pureCStar) :
    pureRep R a ∈ ((pureVN R : StarSubalgebra ℂ (PureGNS R →L[ℂ] PureGNS R)) :
      Set (PureGNS R →L[ℂ] PureGNS R)) := ⟨a, rfl⟩

/-- The scalar operators on the pure GNS space. -/
def scalarOps : Set (PureGNS R →L[ℂ] PureGNS R) :=
  {T | ∃ c : ℂ, T = c • (1 : PureGNS R →L[ℂ] PureGNS R)}

theorem smul_one_mem_scalarOps (c : ℂ) :
    c • (1 : PureGNS R →L[ℂ] PureGNS R) ∈ scalarOps R := ⟨c, rfl⟩

theorem scalar_comm (c : ℂ) (y : PureGNS R →L[ℂ] PureGNS R) :
    y * (c • (1 : PureGNS R →L[ℂ] PureGNS R)) = (c • (1 : PureGNS R →L[ℂ] PureGNS R)) * y := by
  have h : (c • (1 : PureGNS R →L[ℂ] PureGNS R))
      = algebraMap ℂ (PureGNS R →L[ℂ] PureGNS R) c :=
    (Algebra.algebraMap_eq_smul_one c).symm
  rw [h]
  exact (Algebra.commutes c y).symm

/-- **The commutant of the represented pure coordinate algebra consists exactly of the
scalars.** -/
theorem centralizer_pureVN :
    Set.centralizer ((pureVN R : StarSubalgebra ℂ (PureGNS R →L[ℂ] PureGNS R)) :
      Set (PureGNS R →L[ℂ] PureGNS R)) = scalarOps R := by
  ext T
  rw [Set.mem_centralizer_iff]
  constructor
  · intro hT
    exact ⟨⟪vac R, T (vac R)⟫_ℂ,
      commutant_eq_scalar R (fun a => hT _ (pureRep_mem_pureVN R a))⟩
  · rintro ⟨c, rfl⟩ y _
    exact scalar_comm R c y

/-- The centralizer of the scalars is everything. -/
theorem centralizer_scalarOps :
    Set.centralizer (scalarOps R) = (Set.univ : Set (PureGNS R →L[ℂ] PureGNS R)) := by
  refine Set.eq_univ_of_forall (fun T => ?_)
  rw [Set.mem_centralizer_iff]
  rintro y ⟨c, rfl⟩
  exact (scalar_comm R c T).symm

/-- **The bicommutant of the represented pure coordinate algebra is all of `B(K)`.** -/
theorem coe_vonNeumannGenerated_pureVN :
    ((StarSubalgebra.vonNeumannGenerated (pureVN R) :
        VonNeumannAlgebra (PureGNS R)) : Set (PureGNS R →L[ℂ] PureGNS R)) = Set.univ := by
  rw [StarSubalgebra.coe_vonNeumannGenerated, centralizer_pureVN, centralizer_scalarOps]

/-- **The pure GNS representation generates the type-I factor `B(K)`**, in the form of an
equality of star subalgebras. -/
theorem vonNeumannGenerated_pureVN_eq_top :
    (StarSubalgebra.vonNeumannGenerated (pureVN R)).toStarSubalgebra
      = (⊤ : StarSubalgebra ℂ (PureGNS R →L[ℂ] PureGNS R)) := by
  refine SetLike.coe_injective ?_
  rw [StarSubalgebra.coe_top]
  exact coe_vonNeumannGenerated_pureVN R

/-- **Trivial centre**: the centre of the generated von Neumann algebra — its intersection with
its own commutant — consists exactly of the scalar operators.  This is the factor property. -/
theorem centre_vonNeumannGenerated_pureVN :
    ((StarSubalgebra.vonNeumannGenerated (pureVN R) :
        VonNeumannAlgebra (PureGNS R)) : Set (PureGNS R →L[ℂ] PureGNS R))
      ∩ Set.centralizer ((StarSubalgebra.vonNeumannGenerated (pureVN R) :
        VonNeumannAlgebra (PureGNS R)) : Set (PureGNS R →L[ℂ] PureGNS R))
      = scalarOps R := by
  rw [StarSubalgebra.centralizer_vonNeumannGenerated, centralizer_pureVN,
    coe_vonNeumannGenerated_pureVN, Set.univ_inter]

/-! ## 7. The pure GNS space is the vacuum infinite tensor product

The pure coordinate state is the product vacuum state on the selected coordinates, so the pure
GNS space should be the vacuum-restricted infinite tensor product of one qubit per selected
coordinate.  This section constructs that identification.  We first make the stage bookkeeping
uniform: a *pure coordinate word vector* depends only on the underlying coordinate label, not on
the stage at which the label is realized. -/

/-- Every coordinate label is realized at some stage of the exhaustion. -/
theorem exists_stage (c : PauliCoordinateLabels I) : ∃ n, c ∈ A.SourceLabel n := by
  classical
  have hchoice : ∀ p ∈ c.support, ∃ n, site p ∈ A.family.coordinateBlock A.exhaustion n :=
    fun p _ => A.family.exists_mem_coordinateBlock A.exhaustion (site p)
  choose stage hstage using hchoice
  refine ⟨c.support.attach.sup (fun p => stage p.1 p.2), ?_⟩
  rw [LocalHyperbolicFamily.mem_sourceLabels_iff]
  intro p hp
  have hle : stage p hp ≤ c.support.attach.sup (fun q : c.support => stage q.1 q.2) :=
    Finset.le_sup (f := fun q : c.support => stage q.1 q.2) (Finset.mem_attach _ ⟨p, hp⟩)
  exact A.family.coordinateBlock_mono A.exhaustion hle (hstage p hp)

theorem mem_stage_of_le {c : PauliCoordinateLabels I} {n m : ℕ} (h : n ≤ m)
    (hc : c ∈ A.SourceLabel n) : c ∈ A.SourceLabel m :=
  A.family.sourceLabels_mono A.exhaustion h hc

/-- A word element depends only on the underlying coordinate label. -/
theorem wordElt_congr {n m : ℕ} (v : A.SourceLabel n) (w : A.SourceLabel m)
    (h : (v : PauliCoordinateLabels I) = (w : PauliCoordinateLabels I)) :
    R.wordElt n v = R.wordElt m w := by
  have hn : n ≤ max n m := le_max_left n m
  have hm : m ≤ max n m := le_max_right n m
  have heq : A.sourceIncl hn v = A.sourceIncl hm w := by
    refine Subtype.ext ?_
    rw [A.sourceIncl_coe, A.sourceIncl_coe]
    exact h
  rw [← R.wordElt_incl hn v, ← R.wordElt_incl hm w, heq]

/-- A stage at which a given coordinate label is realized. -/
noncomputable def stageOf (c : PauliCoordinateLabels I) : ℕ := (exists_stage (A := A) c).choose

theorem mem_stageOf (c : PauliCoordinateLabels I) :
    c ∈ A.SourceLabel (stageOf (A := A) c) := (exists_stage (A := A) c).choose_spec

/-- A coordinate label, viewed as a stage label at the stage `stageOf`. -/
noncomputable def labelAt (c : PauliCoordinateLabels I) : A.SourceLabel (stageOf (A := A) c) :=
  ⟨c, mem_stageOf c⟩

/-- **The GNS vector of a pure coordinate word**, independent of any stage choice. -/
noncomputable def wordVec (c : PauliCoordinateLabels I) (hc : A.IsPureLabel c) : PureGNS R :=
  gvecL R (pureWordP R (labelAt (A := A) c) hc)

theorem wordVec_eq_gvecL {n : ℕ} (v : A.SourceLabel n)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I)) :
    wordVec R (v : PauliCoordinateLabels I) hv = gvecL R (pureWordP R v hv) :=
  congrArg (fun a : R.pureCStar => gvecL R a)
    (Subtype.ext (wordElt_congr R _ _ rfl) :
      pureWordP R (labelAt (A := A) (v : PauliCoordinateLabels I)) hv = pureWordP R v hv)

/-- The inner product of two stage word vectors. -/
theorem inner_gvecL_pureWordP {k : ℕ} (v w : A.SourceLabel k)
    (hv : A.IsPureLabel (v : PauliCoordinateLabels I))
    (hw : A.IsPureLabel (w : PauliCoordinateLabels I)) :
    ⟪gvecL R (pureWordP R v hv), gvecL R (pureWordP R w hw)⟫_ℂ
      = pauliSign ((A.sourceForm k).form v v) * pauliSign ((A.sourceForm k).form v w)
        * A.productExpectation (((v + w : A.SourceLabel k) : PauliCoordinateLabels I)) := by
  rw [inner_gvecL]
  have hcoe : ((star (pureWordP R v hv) * pureWordP R w hw : R.pureCStar) : R.sourceCStar)
      = star (R.wordElt k v) * R.wordElt k w := rfl
  rw [hcoe, R.wordElt_star, smul_mul_assoc, R.wordElt_mul, smul_smul, map_smul, smul_eq_mul,
    R.totalStateCLM_wordElt]

/-- The stage-independent coordinate pairing underlying `AlphaData.sourceForm`. -/
noncomputable def coordForm (c d : PauliCoordinateLabels I) : PauliBit :=
  c.sum fun p a => a * Sum.elim (fun i => d (Sum.inr i)) (fun _ => (0 : PauliBit)) p

theorem sourceForm_eq_coordForm {k : ℕ} (v w : A.SourceLabel k) :
    (A.sourceForm k).form v w
      = coordForm (v : PauliCoordinateLabels I) (w : PauliCoordinateLabels I) := rfl

/-- **The inner product of two pure coordinate word vectors**, entirely in terms of the
coordinate labels. -/
theorem inner_wordVec (c d : PauliCoordinateLabels I) (hc : A.IsPureLabel c)
    (hd : A.IsPureLabel d) :
    ⟪wordVec R c hc, wordVec R d hd⟫_ℂ
      = pauliSign (coordForm c c) * pauliSign (coordForm c d)
        * A.productExpectation (c + d) := by
  classical
  set k : ℕ := max (stageOf (A := A) c) (stageOf (A := A) d) with hk
  have hcm : c ∈ A.SourceLabel k := mem_stage_of_le (le_max_left _ _) (mem_stageOf c)
  have hdm : d ∈ A.SourceLabel k := mem_stage_of_le (le_max_right _ _) (mem_stageOf d)
  set v : A.SourceLabel k := ⟨c, hcm⟩ with hv
  set w : A.SourceLabel k := ⟨d, hdm⟩ with hw
  have hvc : (v : PauliCoordinateLabels I) = c := rfl
  have hwd : (w : PauliCoordinateLabels I) = d := rfl
  have h1 : wordVec R c hc = gvecL R (pureWordP R v hc) := wordVec_eq_gvecL R v hc
  have h2 : wordVec R d hd = gvecL R (pureWordP R w hd) := wordVec_eq_gvecL R w hd
  have h3 : ⟪wordVec R c hc, wordVec R d hd⟫_ℂ
      = ⟪gvecL R (pureWordP R v hc), gvecL R (pureWordP R w hd)⟫_ℂ :=
    congrArg₂ (fun p q => ⟪p, q⟫_ℂ) h1 h2
  rw [h3, inner_gvecL_pureWordP R v w hc hd, sourceForm_eq_coordForm, sourceForm_eq_coordForm]
  rfl
/-! ### The selected modes and their `X`-words -/

/-- **The selected coordinate modes**: the index set of the infinite tensor product. -/
abbrev Mode (A : AlphaData L I) : Type _ := {i : I // i ∈ A.family.selected}

/-- The `X`-only coordinate label supported on a finite set of selected modes. -/
noncomputable def xLabel (T : Finset (Mode A)) : PauliCoordinateLabels I :=
  Finsupp.indicator (T.image (fun i : Mode A => Sum.inr (i : I))) (fun _ _ => (1 : PauliBit))

theorem xLabel_apply (T : Finset (Mode A)) (p : I ⊕ I) :
    xLabel T p = if p ∈ T.image (fun i : Mode A => Sum.inr (i : I)) then 1 else 0 := by
  classical
  rw [xLabel, Finsupp.indicator_apply]
  split <;> simp_all

theorem xLabel_inl (T : Finset (Mode A)) (j : I) : xLabel (A := A) T (Sum.inl j) = 0 := by
  rw [xLabel_apply, if_neg]
  simp

theorem mem_image_inr_iff (T : Finset (Mode A)) (i : Mode A) :
    ((Sum.inr (i : I) : I ⊕ I) ∈ T.image (fun j : Mode A => Sum.inr (j : I))) ↔ i ∈ T := by
  classical
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    have hv : (j : I) = (i : I) := by simpa using hji
    rwa [Subtype.ext hv] at hj
  · intro h
    exact Finset.mem_image_of_mem _ h

theorem isPureLabel_xLabel (T : Finset (Mode A)) : A.IsPureLabel (xLabel T) := by
  intro p hp
  rw [xLabel_apply] at hp
  by_cases h : p ∈ T.image (fun i : Mode A => Sum.inr (i : I))
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact i.2
  · exact absurd (if_neg h) hp

/-- The `X`-words multiply by symmetric difference of their mode sets. -/
theorem xLabel_add (T T' : Finset (Mode A)) :
    xLabel T + xLabel T' = xLabel (A := A) (symmDiff T T') := by
  classical
  ext p
  rw [Finsupp.add_apply, xLabel_apply, xLabel_apply, xLabel_apply]
  by_cases hp : ∃ i : Mode A, (Sum.inr (i : I) : I ⊕ I) = p
  · obtain ⟨i, rfl⟩ := hp
    simp only [mem_image_inr_iff, Finset.mem_symmDiff]
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ T' <;> simp [h1, h2]
    all_goals decide
  · push_neg at hp
    have h : ∀ S : Finset (Mode A), p ∉ S.image (fun j : Mode A => Sum.inr (j : I)) := by
      intro S hmem
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      exact hp j hj
    rw [if_neg (h _), if_neg (h _), if_neg (h _), add_zero]

theorem xLabel_empty : xLabel (A := A) (∅ : Finset (Mode A)) = 0 := by
  ext p
  rw [xLabel_apply]
  simp

/-- The pure state annihilates every nontrivial `X`-word: this is the statement that the pure
coordinate state is the vacuum state. -/
theorem productExpectation_xLabel (T : Finset (Mode A)) :
    A.productExpectation (xLabel T) = if T = ∅ then 1 else 0 := by
  classical
  by_cases hT : T = ∅
  · subst hT
    rw [xLabel_empty, if_pos rfl]
    exact A.productExpectation_of_mem (Submodule.zero_mem _)
  · rw [if_neg hT]
    refine A.productExpectation_of_not_mem ?_
    intro hmem
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hx := ((A.mem_allowedLabels_iff _).mp hmem).1 (i : I)
    rw [xLabel_apply, if_pos ((mem_image_inr_iff T i).mpr hi)] at hx
    exact one_ne_zero hx

theorem coordForm_xLabel (T : Finset (Mode A)) (d : PauliCoordinateLabels I) :
    coordForm (xLabel (A := A) T) d = 0 := by
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rcases p with j | i
  · rw [xLabel_inl]; ring
  · simp

/-- **The GNS vector of the `X`-word** on a finite set of selected modes: the finite excitation
of the vacuum at those modes. -/
noncomputable def xVec (T : Finset (Mode A)) : PureGNS R :=
  wordVec R (xLabel T) (isPureLabel_xLabel T)

/-- **The finite excitations form an orthonormal family.** -/
theorem inner_xVec (T T' : Finset (Mode A)) :
    ⟪xVec R T, xVec R T'⟫_ℂ = if T = T' then 1 else 0 := by
  classical
  rw [xVec, xVec, inner_wordVec, coordForm_xLabel, coordForm_xLabel, pauliSign_zero,
    xLabel_add, productExpectation_xLabel]
  by_cases h : T = T'
  · subst h
    simp
  · rw [if_neg h, if_neg]
    · ring
    · rw [← Finset.bot_eq_empty, symmDiff_eq_bot]
      exact h

open VacuumRestrictedITP

/-! ### 7c. The vacuum qubit modes and the elementary-tensor vectors

Each selected mode carries a copy of `ℂ²` with the vacuum unit vector `q0`; the P57B
infinite-tensor-product data is instantiated at this family.  The map `elemVec` sends a
vacuum-restricted elementary tensor to the corresponding finite superposition of finite
excitations in the pure GNS space, and it reproduces the P57A kernel exactly. -/

/-- A single coordinate mode carries a qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The vacuum unit vector of a single mode. -/
noncomputable def q0 : Qubit := EuclideanSpace.single 0 1

/-- The excited unit vector of a single mode. -/
noncomputable def q1 : Qubit := EuclideanSpace.single 1 1

theorem inner_q0_q0 : ⟪q0, q0⟫_ℂ = 1 := by simp [q0]

theorem inner_q1_q0 : ⟪q1, q0⟫_ℂ = 0 := by
  rw [q1, q0, EuclideanSpace.inner_single_left]; simp

theorem inner_q0_q1 : ⟪q0, q1⟫_ℂ = 0 := by
  rw [q1, q0, EuclideanSpace.inner_single_left]; simp

theorem inner_q1_q1 : ⟪q1, q1⟫_ℂ = 1 := by simp [q1]

/-- Resolution of the identity of a single mode in the computational basis. -/
theorem inner_qubit_decomp (u w : Qubit) :
    ⟪u, w⟫_ℂ = conj ⟪q1, u⟫_ℂ * ⟪q1, w⟫_ℂ + conj ⟪q0, u⟫_ℂ * ⟪q0, w⟫_ℂ := by
  rw [q0, q1, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **The vacuum family of the infinite tensor product**: the pure vacuum vector at every
selected coordinate mode. -/
noncomputable def vacQ (A : AlphaData L I) : Mode A → Qubit := fun _ => q0

/-- The P57B normalization hypothesis for the vacuum family. -/
theorem inner_vacQ : ∀ i : Mode A, ⟪vacQ A i, vacQ A i⟫_ℂ = 1 := by
  intro _; exact inner_q0_q0

/-- The coefficient of the finite excitation `T` in the expansion of a vacuum-restricted
elementary tensor over the ambient mode set `S`. -/
noncomputable def coefOf (v : VacuumTensor (vacQ A)) (S T : Finset (Mode A)) : ℂ :=
  (∏ i ∈ T, ⟪q1, v.vec i⟫_ℂ) * ∏ i ∈ S \ T, ⟪q0, v.vec i⟫_ℂ

/-- The expansion of a vacuum-restricted elementary tensor in finite excitations, computed
over the ambient mode set `S`. -/
noncomputable def elemVecOn (v : VacuumTensor (vacQ A)) (S : Finset (Mode A)) : PureGNS R :=
  ∑ T ∈ S.powerset, coefOf v S T • xVec R T

theorem coefOf_eq_zero_of_not_subset {v : VacuumTensor (vacQ A)} {S T : Finset (Mode A)}
    (hT : ¬ T ⊆ v.active) : coefOf v S T = 0 := by
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hT
  have hvi : v.vec i = q0 := v.vec_eq_vacuum i hiS
  refine mul_eq_zero_of_left (Finset.prod_eq_zero hiT ?_) _
  rw [hvi]; exact inner_q1_q0

theorem coefOf_mono {v : VacuumTensor (vacQ A)} {S S' T : Finset (Mode A)}
    (hv : v.active ⊆ S) (hSS' : S ⊆ S') : coefOf v S' T = coefOf v S T := by
  rw [coefOf, coefOf]
  congr 1
  refine (Finset.prod_subset (Finset.sdiff_subset_sdiff hSS' (Finset.Subset.refl T)) ?_).symm
  intro i hi hi'
  rw [Finset.mem_sdiff] at hi
  have hiS : i ∉ S := fun h => hi' (Finset.mem_sdiff.mpr ⟨h, hi.2⟩)
  rw [v.vec_eq_vacuum i (fun h => hiS (hv h))]
  exact inner_q0_q0

/-- The expansion does not depend on the ambient mode set, as long as it contains the active
set of the elementary tensor. -/
theorem elemVecOn_mono {v : VacuumTensor (vacQ A)} {S S' : Finset (Mode A)}
    (hv : v.active ⊆ S) (hSS' : S ⊆ S') : elemVecOn R v S' = elemVecOn R v S := by
  classical
  rw [elemVecOn, elemVecOn]
  refine (Finset.sum_subset (Finset.powerset_mono.mpr hSS') ?_).symm.trans ?_
  · intro T _ hT
    rw [Finset.mem_powerset] at hT
    rw [coefOf_eq_zero_of_not_subset (fun h => hT (h.trans hv)), zero_smul]
  · exact Finset.sum_congr rfl (fun T _ => by rw [coefOf_mono hv hSS'])

/-- **The pure GNS vector attached to a vacuum-restricted elementary tensor.** -/
noncomputable def elemVec (v : VacuumTensor (vacQ A)) : PureGNS R := elemVecOn R v v.active

theorem elemVec_eq_elemVecOn {v : VacuumTensor (vacQ A)} {S : Finset (Mode A)}
    (hv : v.active ⊆ S) : elemVec R v = elemVecOn R v S :=
  (elemVecOn_mono R (Finset.Subset.refl _) hv).symm

/-- Orthonormality of the finite excitations, in the form used to compute inner products of
expansions. -/
theorem inner_sum_smul_xVec (s : Finset (Finset (Mode A))) (c d : Finset (Mode A) → ℂ) :
    ⟪∑ T ∈ s, c T • xVec R T, ∑ T ∈ s, d T • xVec R T⟫_ℂ = ∑ T ∈ s, conj (c T) * d T := by
  classical
  rw [sum_inner]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [inner_smul_left, inner_sum]
  have hterm : ∀ T' ∈ s, ⟪xVec R T, d T' • xVec R T'⟫_ℂ = if T' = T then d T' else 0 := by
    intro T' _
    rw [inner_smul_right, inner_xVec]
    by_cases h : T = T'
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s T (fun T' => d T'), if_pos hT]

/-- The binomial expansion of the mode-by-mode inner product. -/
theorem sum_powerset_coefOf (v w : VacuumTensor (vacQ A)) (S : Finset (Mode A)) :
    ∑ T ∈ S.powerset, conj (coefOf v S T) * coefOf w S T
      = ∏ i ∈ S, ⟪v.vec i, w.vec i⟫_ℂ := by
  classical
  have hprod : ∏ i ∈ S, ⟪v.vec i, w.vec i⟫_ℂ
      = ∏ i ∈ S, ((fun i => conj ⟪q1, v.vec i⟫_ℂ * ⟪q1, w.vec i⟫_ℂ) i
        + (fun i => conj ⟪q0, v.vec i⟫_ℂ * ⟪q0, w.vec i⟫_ℂ) i) :=
    Finset.prod_congr rfl fun i _ => inner_qubit_decomp _ _
  rw [hprod, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [coefOf, coefOf, map_mul, map_prod, map_prod, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  ring

/-- **The elementary-tensor vectors reproduce the P57A kernel.** -/
theorem inner_elemVec (v w : VacuumTensor (vacQ A)) :
    ⟪elemVec R v, elemVec R w⟫_ℂ = kern v w := by
  classical
  have hv : v.active ⊆ v.active ∪ w.active := Finset.subset_union_left
  have hw : w.active ⊆ v.active ∪ w.active := Finset.subset_union_right
  rw [elemVec_eq_elemVecOn R hv, elemVec_eq_elemVecOn R hw, elemVecOn, elemVecOn,
    inner_sum_smul_xVec, sum_powerset_coefOf, kern]

end PureGNSFactor
end AristotleCandidates
