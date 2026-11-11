import Mathlib
import AristotleCandidates.FiniteCornerTrace
import AristotleCandidates.KaplanskyDensity

/-!
# P50 — the faithful normal tracial state on the von Neumann corner `q M_Γ q`

**Source basis:** `main.tex:1265-1417` (Proposition `prop:normal-trace` and
Proposition `prop:faithful`).

**Plan alignment.**  Package `P50`, lane `G`.  Predecessors used: `P49`
(`AristotleCandidates.FiniteCornerTrace`) for the C⋆-level cyclicity of the
compressed vector functional, and `P49C`
(`AristotleCandidates.KaplanskyDensity`) for the *proved* Kaplansky bounded
approximation and the bounded compressed product convergence.  Through those,
`P47`, `P48`, `P49A` and `P49B` are used transitively.

The gate discharged here is exactly the manuscript's Propositions
`prop:normal-trace` and `prop:faithful`: the compressed vector functional
`tau_q` extends from the compressed quasi-local C⋆-algebra to the whole von
Neumann corner `q M_Γ q`, and is there a **faithful normal finite tracial
state** — unital and positive, hence a state and not merely a weight.

**Forbidden downstream claims, not made anywhere in this file.**  No fullness
of `q`, no finiteness of `q` as a projection, no statement about central
summands or central supports, no global trace or weight on `M_Γ`, and no
type-III exclusion.

## What is proved

* `cornerTau_continuous_wot`, `tauVec_tendsto_of_stronglyTendsto`,
  `cornerTau_tendsto_of_stronglyTendsto`, `cornerTau_continuous_sot`, and
  `cornerTau_tendsto_sum_of_stronglyTendsto` — **normality**.  The compressed
  functional is continuous for the weak operator topology, hence ultraweakly
  continuous in this vector-functional form; the additional strong-operator
  results carry strong limits and partial sums to limits.  This is the
  manuscript's "since `tau_q` is a restriction of a vector functional it is
  normal", turned into proved statements about that realization.
* `cornerTracialOn_bicommutant`, `cornerTracialOn_vonNeumannGenerated` —
  **traciality on the von Neumann corner**.  Cyclicity of `tau_q` on the
  compressions of a norm-closed unital star algebra `A` propagates to the
  compressions of its bicommutant `M = A''`, using the P49C bounded compressed
  approximants and bounded product convergence.  This is `main.tex:1265-1315`.
* `norm_star_apply_eq_of_cornerTracial`, `apply_apply_eq_zero_of_apply_eq_zero`,
  `cornerTau_faithful` — **faithfulness**, from the manuscript's
  dense-vector/commuting-complement argument (`main.tex:1352-1417`).  The
  square-root step of the manuscript is replaced by the equivalent and simpler
  consequence `‖x* Ω‖ = ‖x Ω‖` of traciality; this is a change of proof route
  only, and it proves the same statement.
* `IsFaithfulNormalTracialCorner` — the packaged conclusion: `q` is a
  projection of `M`, and `tau_q` is a unital, positive, tracial, normal and
  faithful functional on the corner `q M q`.
* `normal_faithful_corner_trace` — the **exported P50 theorem**.  It takes the
  P49 compatible finite-codespace system, its decreasing projection tower, the
  represented C⋆-algebra `A` with its norm-density data, the commuting
  complement and the dense-vector premise, and produces
  `IsFaithfulNormalTracialCorner (A'') q Ω` for `q` the tower's `limitProj`.
  C⋆-level cyclicity is *derived* by instantiating
  `CompatibleFiniteCodespaceSystem.finite_corner_trace` of P49; it is not an
  assumption, and neither `CornerTracialOn` nor a Kaplansky-density or
  bicommutant interface appears among the hypotheses: those are used as proved
  results of P49/P49B/P49C.

## The remaining non-analytic premises of the exported theorem

1. the finite codespace data `D` of P49 (finite-stage star representations,
   hermitian idempotent code projections, densities `rho_n = weight n • P_n` of
   trace one, and the GNS vector-state identity `⟪Ω, pi n x Ω⟫ = Tr(rho_n x)`),
   together with the stage inclusions;
2. `hp`: `IsDecreasingProjTower` for the stage projections (`main.tex` Lemma
   `lema:proj_inequality`) — the same premise as in P49;
3. `hAclosed`: the represented regional algebra `A = pi_omega(A_Γ)` is a
   norm-closed unital star subalgebra of `B(H)`, i.e. a represented C⋆-algebra;
4. `hlocal` and `hAdense`: the finite-stage operators lie in `A`, and `A` is
   contained in their norm closure — i.e. `A` *is* the quasi-local C⋆-algebra.
   This is exactly the norm-density input P49 already requires, and which the
   packet explicitly permits to remain explicit;
5. `hB`: the represented complementary algebra `B = pi_omega(A_{Γᶜ})` commutes
   with `A` (`main.tex` eq. `eq:M-commutes-complement`); and
6. `hdense`: the vectors `pi_omega(b) pi_omega(a) Ω` with `a ∈ A`, `b ∈ B` span
   a dense subspace of the GNS space (`main.tex` eq. `eq:dense_states`, i.e.
   cyclicity of the global GNS vector).

Strong closedness of commutants, the double commutant theorem and Kaplansky
density are *used as theorems* (P49A, P49B, P49C), never as hypotheses.
-/

universe u v

open Filter Topology

namespace AristotleCandidates
namespace NormalFaithfulCornerTrace

open FiniteCornerTrace ProjectionTower
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §1  Normality: the vector-functional realization -/

section Normality

omit [CompleteSpace H] in
/-- A strongly convergent net is carried to a convergent net by the vector functional. -/
theorem tauVec_tendsto_of_stronglyTendsto {α : Type v} {l : Filter α}
    {f : α → H →L[ℂ] H} {x : H →L[ℂ] H} (Ω : H)
    (h : StrongOperator.StronglyTendsto l f x) :
    Tendsto (fun i => tauVec Ω (f i)) l (𝓝 (tauVec Ω x)) := by
  have h0 : Tendsto (fun i => f i Ω) l (𝓝 (x Ω)) := h Ω
  exact ((innerSL ℂ Ω).continuous.tendsto _).comp h0

/-- **Normality, net form.**  The compressed functional `tau_q` carries strong limits of nets to
limits.  This is the manuscript's "`tau_q` is the restriction of a vector functional, hence
normal", proved from that realization. -/
theorem cornerTau_tendsto_of_stronglyTendsto {α : Type v} {l : Filter α}
    {f : α → H →L[ℂ] H} {x : H →L[ℂ] H} (q : H →L[ℂ] H) (Ω : H)
    (h : StrongOperator.StronglyTendsto l f x) :
    Tendsto (fun i => cornerTau q Ω (f i)) l (𝓝 (cornerTau q Ω x)) :=
  tauVec_tendsto_of_stronglyTendsto Ω (h.compress q q)

/-- **Normality, topological form.**  `tau_q` is continuous for the strong operator topology;
a strong-operator continuous linear functional is in particular σ-weakly continuous. -/
theorem cornerTau_continuous_sot (q : H →L[ℂ] H) (Ω : H) :
    Continuous fun T : StrongOperator.SOT H => cornerTau q Ω (StrongOperator.ofSOT T) := by
  have h1 : Continuous fun T : StrongOperator.SOT H => (StrongOperator.ofSOT T) (q Ω) :=
    continuous_eval_const (q Ω)
  exact (innerSL ℂ Ω).continuous.comp (q.continuous.comp h1)

/-- **Normality, weak-operator form.**  The compressed vector functional is
continuous for the weak operator topology.  In particular it is an ultraweakly
continuous, hence normal, functional on every represented von Neumann corner. -/
theorem cornerTau_continuous_wot (q : H →L[ℂ] H) (Ω : H) :
    Continuous fun T : H →WOT[ℂ] H =>
      cornerTau q Ω ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).symm T) := by
  have h : Continuous fun T : H →WOT[ℂ] H =>
      ((innerSL ℂ Ω).comp q) (T (q Ω)) :=
    ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id ℂ) (E := H) (F := H)
      (q Ω) ((innerSL ℂ Ω).comp q)
  simpa [cornerTau_apply, ContinuousLinearMap.toWOT_apply] using h

/-- **Normality, countable-additivity form.**  If the partial sums of a sequence of operators
converge strongly, then the values of `tau_q` sum to its value at the limit. -/
theorem cornerTau_tendsto_sum_of_stronglyTendsto {e : ℕ → H →L[ℂ] H} {x : H →L[ℂ] H}
    (q : H →L[ℂ] H) (Ω : H)
    (h : StrongOperator.StronglyTendsto atTop (fun n => ∑ i ∈ Finset.range n, e i) x) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, cornerTau q Ω (e i)) atTop
      (𝓝 (cornerTau q Ω x)) := by
  refine (cornerTau_tendsto_of_stronglyTendsto q Ω h).congr fun n => ?_
  exact map_sum (cornerTau q Ω) e (Finset.range n)

end Normality

/-! ## §2  Traciality on the von Neumann corner -/

section Tracial

open KaplanskyDensity

variable {q : H →L[ℂ] H} {Ω : H}

/-- **`main.tex:1265-1315`, Proposition `prop:normal-trace`, cyclicity part.**

If the compressed vector functional is cyclic on the compressions of a norm-closed unital star
algebra `A`, then it is cyclic on the compressions of the whole von Neumann algebra `M = A''`.

The proof is the manuscript's: by the *proved* Kaplansky density theorem of P49C every `x ∈ A''`
is the strong limit of a uniformly norm-bounded net in `A`; compressions of a uniformly bounded
net converge strongly to the compression of the limit; and products of two such nets converge
strongly by joint strong continuity of multiplication on bounded sets. -/
theorem cornerTracialOn_bicommutant {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) (hq1 : star q = q) (hq2 : q * q = q)
    (h : CornerTracialOn q Ω (A : Set (H →L[ℂ] H))) :
    CornerTracialOn q Ω (Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) := by
  intro x hx y hy
  obtain ⟨l, hne, hc1, hc2⟩ := exists_net_compression_product hA hq1 hq2 hx hy
  haveI := hne
  have t1 := tauVec_tendsto_of_stronglyTendsto Ω hc1
  have t2 := tauVec_tendsto_of_stronglyTendsto Ω hc2
  have heq : (fun p : {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ ‖x‖} ×
      {b : H →L[ℂ] H | b ∈ A ∧ ‖b‖ ≤ ‖y‖} =>
        tauVec Ω ((q * (p.1 : H →L[ℂ] H) * q) * (q * (p.2 : H →L[ℂ] H) * q))) =
      fun p => tauVec Ω ((q * (p.2 : H →L[ℂ] H) * q) * (q * (p.1 : H →L[ℂ] H) * q)) := by
    funext p
    exact h _ p.1.2.1 _ p.2.2.1
  rw [heq] at t1
  exact tendsto_nhds_unique t1 t2

/-- The same statement for the concrete von Neumann algebra `A''` of the bicommutant core. -/
theorem cornerTracialOn_vonNeumannGenerated {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) (hq1 : star q = q) (hq2 : q * q = q)
    (h : CornerTracialOn q Ω (A : Set (H →L[ℂ] H))) :
    CornerTracialOn q Ω ((StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H) :
      Set (H →L[ℂ] H)) := by
  rw [StarSubalgebra.coe_vonNeumannGenerated]
  exact cornerTracialOn_bicommutant hA hq1 hq2 h

end Tracial

/-! ## §3  Faithfulness -/

section Faithful

variable {q : H →L[ℂ] H} {Ω : H}

theorem tauVec_star_mul_self (Ω : H) (u : H →L[ℂ] H) :
    tauVec Ω (star u * u) = ((‖u Ω‖ : ℝ) : ℂ) ^ 2 := by
  have h : ((star u * u) Ω) = (star u) (u Ω) := rfl
  rw [tauVec_apply, h, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem tauVec_mul_star_self (Ω : H) (u : H →L[ℂ] H) :
    tauVec Ω (u * star u) = ((‖(star u) Ω‖ : ℝ) : ℂ) ^ 2 := by
  have h := tauVec_star_mul_self Ω (star u)
  rwa [star_star] at h

omit [CompleteSpace H] in
/-- A corner element is fixed by the compression. -/
theorem compress_eq_self {x : H →L[ℂ] H} (hqx : q * x = x) (hxq : x * q = x) :
    q * x * q = x := by rw [hqx, hxq]

/-- The star of a corner element is again a corner element. -/
theorem star_corner {x : H →L[ℂ] H} (hq1 : star q = q) (hqx : q * x = x) (hxq : x * q = x) :
    q * star x = star x ∧ star x * q = star x := by
  refine ⟨?_, ?_⟩
  · have h := congrArg star hxq
    rwa [star_mul, hq1] at h
  · have h := congrArg star hqx
    rwa [star_mul, hq1] at h

/-- **Key consequence of traciality.**  On the corner, `‖x* Ω‖ = ‖x Ω‖`.

This replaces the manuscript's square-root computation: it is the special case
`tau_q(x* x) = tau_q(x x*)` of cyclicity, and it is all that the faithfulness argument needs. -/
theorem norm_star_apply_eq_of_cornerTracial {M : VonNeumannAlgebra H}
    (htr : CornerTracialOn q Ω (M : Set (H →L[ℂ] H))) (hq1 : star q = q)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hqx : q * x = x) (hxq : x * q = x) :
    ‖(star x) Ω‖ = ‖x Ω‖ := by
  obtain ⟨hs1, hs2⟩ := star_corner hq1 hqx hxq
  have hcx : q * x * q = x := compress_eq_self hqx hxq
  have hcs : q * star x * q = star x := compress_eq_self hs1 hs2
  have hkey := htr (star x) (star_mem hx) x hx
  rw [hcx, hcs, tauVec_star_mul_self, tauVec_mul_star_self] at hkey
  have hr : (‖x Ω‖ : ℝ) ^ 2 = (‖(star x) Ω‖ : ℝ) ^ 2 := by exact_mod_cast hkey
  nlinarith [norm_nonneg (x Ω), norm_nonneg ((star x) Ω)]

/-- **`main.tex` eq. `eq:xyOmega_zero`.**  A corner element annihilating `Ω` annihilates `y Ω`
for every corner element `y`. -/
theorem apply_apply_eq_zero_of_apply_eq_zero {M : VonNeumannAlgebra H}
    (htr : CornerTracialOn q Ω (M : Set (H →L[ℂ] H))) (hq1 : star q = q)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hqx : q * x = x) (hxq : x * q = x) (hx0 : x Ω = 0)
    {y : H →L[ℂ] H} (hy : y ∈ M) (hyq : y * q = y) :
    x (y Ω) = 0 := by
  have hxs : (star x) Ω = 0 := by
    have h := norm_star_apply_eq_of_cornerTracial htr hq1 hx hqx hxq
    rw [hx0] at h
    exact norm_eq_zero.1 (by simpa using h)
  have hxy : x * y ∈ M := mul_mem hx hy
  have h1 : q * (x * y) = x * y := by rw [← mul_assoc, hqx]
  have h2 : (x * y) * q = x * y := by rw [mul_assoc, hyq]
  have hnorm := norm_star_apply_eq_of_cornerTracial htr hq1 hxy h1 h2
  have hstar : (star (x * y)) Ω = 0 := by
    rw [star_mul]
    show (star y) ((star x) Ω) = 0
    rw [hxs, map_zero]
  rw [hstar] at hnorm
  exact norm_eq_zero.1 (by simpa using hnorm.symm)

/-- **`main.tex:1352-1417`, Proposition `prop:faithful`.**

Let `q` be a projection of `M = A''` fixing `Ω`, let the compressed vector functional be cyclic
on `M`, let `B` commute with `A`, and let the vectors `b a Ω` with `a ∈ A`, `b ∈ B` span a dense
subspace.  Then `tau_q` is faithful on the corner `q M q`. -/
theorem cornerTau_faithful {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {B : Set (H →L[ℂ] H)} (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hq1 : star q = q) (hq2 : q * q = q) (hqΩ : q Ω = Ω)
    (hqM : q ∈ (StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H))
    (htr : CornerTracialOn q Ω
      ((StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H) : Set (H →L[ℂ] H)))
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H))
    {x : H →L[ℂ] H} (hx : x ∈ (StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H))
    (hqx : q * x = x) (hxq : x * q = x) (h0 : cornerTau q Ω (star x * x) = 0) :
    x = 0 := by
  have hsa : IsSelfAdjoint q := hq1
  -- `tau_q(x* x) = ‖x Ω‖²`, so `x Ω = 0`.
  have hx0 : x Ω = 0 := by
    have h := cornerTau_star_mul_self hsa Ω x
    rw [h0, hqΩ] at h
    have h3 : (‖x Ω‖ : ℝ) ^ 2 = 0 := by exact_mod_cast h.symm
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (x Ω)])
  -- `x` annihilates `a Ω` for every `a ∈ A`.
  have hxa : ∀ a ∈ (A : Set (H →L[ℂ] H)), x (a Ω) = 0 := by
    intro a ha
    have haM : a ∈ (StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H) :=
      StarSubalgebra.mem_vonNeumannGenerated_of_mem ha
    have hy : q * a * q ∈ (StarSubalgebra.vonNeumannGenerated A : VonNeumannAlgebra H) :=
      mul_mem (mul_mem hqM haM) hqM
    have h2 : (q * a * q) * q = q * a * q := by
      calc (q * a * q) * q = q * a * (q * q) := by noncomm_ring
        _ = q * a * q := by rw [hq2]
    have hzero := apply_apply_eq_zero_of_apply_eq_zero htr hq1 hx hqx hxq hx0 hy h2
    have hval : (q * a * q) Ω = q (a Ω) := by
      show q (a (q Ω)) = q (a Ω)
      rw [hqΩ]
    rw [hval] at hzero
    have hxq' : ∀ z : H, x (q z) = x z := fun z =>
      congrArg (fun t : H →L[ℂ] H => t z) hxq
    rwa [hxq'] at hzero
  -- `x` commutes with the complementary algebra `B`.
  have hxc : ∀ b ∈ B, b * x = x * b := fun b hb =>
    StarSubalgebra.mem_vonNeumannGenerated_iff.1 hx b (hB hb)
  -- `x` annihilates a dense set of vectors, hence vanishes.
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro ξ ⟨a, ha, b, hb, rfl⟩
  have hval : x ((b * a) Ω) = (x * b) (a Ω) := rfl
  have : x ((b * a) Ω) = 0 := by
    rw [hval, ← hxc b hb]
    show b (x (a Ω)) = 0
    rw [hxa a ha, map_zero]
  simpa using this

end Faithful

/-! ## §4  The packaged conclusion and the exported P50 theorem -/

/-- **A faithful normal finite tracial state on the corner `q M q`.**

The fields are exactly the manuscript's assertions about `tau_q` in Propositions
`prop:normal-trace` and `prop:faithful`:

* `isStarProjection`, `mem` — `q` is a projection of `M`, so `q M q` is a von Neumann algebra
  with unit `q`;
* `unital`, `positive` — `tau_q` is a *state* (finite and normalized), not a weight;
* `tracial` — cyclicity `tau_q(xy) = tau_q(yx)` on the compressions of `M`;
* `normal` — strong-operator (hence σ-weak) continuity of `tau_q`;
* `faithful` — `tau_q(x* x) = 0` forces `x = 0` for `x` in the corner. -/
structure IsFaithfulNormalTracialCorner (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) (Ω : H) :
    Prop where
  /-- `q` is a self-adjoint idempotent. -/
  isStarProjection : IsStarProjection q
  /-- `q` belongs to `M`, so that `q M q` is a von Neumann algebra on `q H`. -/
  mem : q ∈ M
  /-- Normalization: `tau_q(1) = 1`, the unit of the corner being `q`. -/
  unital : cornerTau q Ω 1 = 1
  /-- Positivity of `tau_q`. -/
  positive : ∀ x : H →L[ℂ] H, 0 ≤ (cornerTau q Ω (star x * x)).re
  /-- Traciality on the compressions of `M`, i.e. on `q M q`. -/
  tracial : CornerTracialOn q Ω (M : Set (H →L[ℂ] H))
  /-- Normality, encoded as weak-operator continuity of the vector functional. -/
  normal : Continuous fun T : H →WOT[ℂ] H =>
    cornerTau q Ω ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).symm T)
  /-- Faithfulness on the corner. -/
  faithful : ∀ x ∈ M, q * x = x → x * q = x → cornerTau q Ω (star x * x) = 0 → x = 0

namespace IsFaithfulNormalTracialCorner

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H}

/-- **Traciality read on the corner algebra `q M q` of P47.**  For genuine corner elements the
cyclicity field is literally `tau_q(x y) = tau_q(y x)`. -/
theorem tracial_corner (h : IsFaithfulNormalTracialCorner M q Ω) {x y : H →L[ℂ] H}
    (hx : x ∈ M.corner h.isStarProjection.isSelfAdjoint)
    (hy : y ∈ M.corner h.isStarProjection.isSelfAdjoint) :
    tauVec Ω (x * y) = tauVec Ω (y * x) := by
  have hcx : q * x * q = x := compress_eq_self hx.2.1 hx.2.2
  have hcy : q * y * q = y := compress_eq_self hy.2.1 hy.2.2
  have hkey := h.tracial x hx.1 y hy.1
  rwa [hcx, hcy] at hkey

/-- **Faithfulness read on the corner algebra `q M q` of P47.** -/
theorem faithful_corner (h : IsFaithfulNormalTracialCorner M q Ω) {x : H →L[ℂ] H}
    (hx : x ∈ M.corner h.isStarProjection.isSelfAdjoint)
    (h0 : cornerTau q Ω (star x * x) = 0) : x = 0 :=
  h.faithful x hx.1 hx.2.1 hx.2.2 h0

/-- The value of `tau_q` at the unit `q` of the corner is `1`. -/
theorem apply_unit (h : IsFaithfulNormalTracialCorner M q Ω) : tauVec Ω q = 1 := by
  have h1 := h.unital
  rw [cornerTau_apply, mul_one] at h1
  have h2 : (q * q) Ω = q Ω :=
    congrArg (fun t : H →L[ℂ] H => t Ω) h.isStarProjection.isIdempotentElem
  rw [tauVec_apply, ← h2]
  exact h1

end IsFaithfulNormalTracialCorner

section Export

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **Exported P50 theorem** (`main.tex:1265-1417`, Propositions `prop:normal-trace` and
`prop:faithful`).

Input data:

* `D`, the compatible finite-codespace system of P49, with GNS vector `Ω`;
* `hp`, the decreasing projection tower of its stage projections (P48/P49 premise);
* `A`, the represented regional C⋆-algebra `pi_omega(A_Γ)`, assumed norm closed, containing all
  finite-stage operators (`hlocal`) and contained in their norm closure (`hAdense`) — the
  norm-density input of P49;
* `B`, the represented complementary algebra, assumed to commute with `A` (`hB`), and the
  dense-vector premise `hdense` of `main.tex` eq. `eq:dense_states`.

Conclusion: for `q` the strong limit of the stage projections and `M = A''`, the compressed
vector functional `tau_q` is a faithful normal finite tracial state on `q M q`.

C⋆-level cyclicity is *not* assumed: it is obtained by instantiating
`CompatibleFiniteCodespaceSystem.finite_corner_trace` of P49.  Kaplansky density and the
bicommutant theorem are used as the proved results P49C and P49B. -/
theorem normal_faithful_corner_trace {Ω : H} (D : CompatibleFiniteCodespaceSystem Ω ι)
    (hp : IsDecreasingProjTower D.toFiniteCodespaceSystem.stageProj)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hlocal : ∀ n, Set.range (D.pi n) ⊆ (A : Set (H →L[ℂ] H)))
    (hAdense : (A : Set (H →L[ℂ] H)) ⊆ closure (⋃ n, Set.range (D.pi n)))
    (B : Set (H →L[ℂ] H)) (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H)) :
    IsFaithfulNormalTracialCorner (StarSubalgebra.vonNeumannGenerated A)
      (limitProj D.toFiniteCodespaceSystem.stageProj) Ω := by
  set p := D.toFiniteCodespaceSystem.stageProj with hpdef
  set q := limitProj p with hqdef
  set M : VonNeumannAlgebra H := StarSubalgebra.vonNeumannGenerated A with hMdef
  have hqsp : IsStarProjection q := limitProj_isStarProjection p
  have hq1 : star q = q := hqsp.isSelfAdjoint.star_eq
  have hq2 : q * q = q := hqsp.isIdempotentElem
  have hΩfix : ∀ n, p n Ω = Ω := fun n => D.toFiniteCodespaceSystem.stageProj_apply_self n
  have hqΩ : q Ω = Ω := limitProj_apply_self hΩfix
  -- `q ∈ M`: every stage projection lies in `A ⊆ M`, and `M` is closed under strong limits.
  have hstageA : ∀ n, p n ∈ M := by
    intro n
    exact StarSubalgebra.mem_vonNeumannGenerated_of_mem
      (hlocal n ⟨D.toFiniteCodespaceSystem.codeProj n, rfl⟩)
  have hqM : q ∈ M := hp.limitProj_mem_vonNeumannAlgebra M hstageA
  -- P49 supplies cyclicity on the represented C⋆-algebra `A`.
  obtain ⟨hcstar, hone, hpos⟩ :=
    D.finite_corner_trace hp (A : Set (H →L[ℂ] H)) hAdense
  -- P49C transports it to the bicommutant.
  have htr : CornerTracialOn q Ω (M : Set (H →L[ℂ] H)) :=
    cornerTracialOn_vonNeumannGenerated hAclosed hq1 hq2 hcstar
  refine
    { isStarProjection := hqsp
      mem := hqM
      unital := hone
      positive := hpos
      tracial := htr
      normal := cornerTau_continuous_wot q Ω
      faithful := ?_ }
  intro x hx hqx hxq h0
  exact cornerTau_faithful hB hq1 hq2 hqΩ hqM htr hdense hx hqx hxq h0

end Export

/-! ## §5  Non-vacuity of the exported hypotheses

The exported theorem bundles several premises at once (finite codespace data, a decreasing
projection tower, a norm-closed represented algebra squeezed between the finite stages and their
closure, a commuting complement, and a dense-vector premise).  The following witness shows they
are simultaneously satisfiable, using the one-dimensional sanity system of P49.  It is a
consistency check only and carries no manuscript content. -/

section Sanity

open FiniteCornerTrace

/-- The one-dimensional sanity representation of P49 is surjective. -/
theorem sanity_range_pi (n : ℕ) :
    Set.range (sanitySystem.pi n) = Set.univ := by
  ext T
  simp only [Set.mem_univ, iff_true, Set.mem_range]
  obtain ⟨M, hM⟩ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)).surjective T
  exact ⟨M, hM⟩

/-- **Non-vacuity.**  Every hypothesis of the exported P50 theorem is satisfied by the
one-dimensional sanity system, with `A = ⊤`, complementary algebra `{1}`, and the GNS vector
`EuclideanSpace.single 0 1`. -/
theorem sanity_isFaithfulNormalTracialCorner :
    IsFaithfulNormalTracialCorner
      (StarSubalgebra.vonNeumannGenerated
        (⊤ : StarSubalgebra ℂ (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))))
      (limitProj sanitySystem.toFiniteCodespaceSystem.stageProj)
      (EuclideanSpace.single 0 1) := by
  classical
  set Ω : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1 with hΩ
  refine normal_faithful_corner_trace sanitySystem sanitySystem_isDecreasingProjTower ⊤ ?_ ?_ ?_
    {1} ?_ ?_
  · simp
  · intro n
    simp
  · intro T _
    refine subset_closure (Set.mem_iUnion.2 ⟨0, ?_⟩)
    rw [sanity_range_pi]
    exact Set.mem_univ T
  · intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    intro c _
    simp
  · have hinner : ⟪Ω, Ω⟫_ℂ = 1 := sanitySystem.toFiniteCodespaceSystem.inner_self_eq_one
    have hspan : Submodule.span ℂ
        {ξ : EuclideanSpace ℂ (Fin 1) |
          ∃ a ∈ ((⊤ : StarSubalgebra ℂ
                (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) :
              Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))),
            ∃ b ∈ ({1} : Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))),
              ξ = (b * a) Ω} = ⊤ := by
      rw [eq_top_iff]
      intro ξ _
      refine Submodule.subset_span ⟨(innerSL ℂ Ω).smulRight ξ, by simp,
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)), rfl, ?_⟩
      show ξ = (1 * (innerSL ℂ Ω).smulRight ξ) Ω
      rw [one_mul]
      show ξ = ⟪Ω, Ω⟫_ℂ • ξ
      rw [hinner, one_smul]
    rw [hspan]
    simp

end Sanity

end NormalFaithfulCornerTrace
end AristotleCandidates
