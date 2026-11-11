import Mathlib
import AristotleCandidates.FullFiniteCornerCentralExclusion
import AristotleCandidates.UltraweakNormality

/-!
# P60R — a global faithful normal semifinite weight from a full finite corner

**Infrastructure only.**  This file formalizes no manuscript claim.  It is the
*optional* Lane-G strengthening: it does not assert that the manuscript's
no-central-type-III conclusion needs a global weight, and it does not claim that
P51 already produced one.  It does not alter the accepted no-central-type-III
result of P51.

**Plan alignment.**  Package `P60R`, lane `G` (optional recovery of the
retired P60 attempt).  Predecessors used, both integrated and locally audited:
`P51` (`AristotleCandidates.FullFiniteCornerCentralExclusion`) for the full
finite corner and its comparison vocabulary — P51 is accepted, see
`reviews/P51-full-finite-corner-central-exclusion-recovery.md`, so the earlier
provenance objection against it is withdrawn — and `P50U`
(`AristotleCandidates.UltraweakNormality`) for the *literally ultraweak-normal*
faithful tracial corner state `IsFaithfulUltraweakNormalTracialCorner`.
Through those, `P47`–`P50` are used transitively.  The older WOT field name of
P50 is never used as the normality input: the normality hypothesis consumed
here is P50U's `normal_ultraweak`.

**What P60R changes.**  The retired P60 attempt exported a *finite-compression*
certificate under the name of semifiniteness.  That certificate is retained,
under the honest name `globalWeight_finite_compressions`, and the exported
bundle now carries the **standard positive-cone semifiniteness statement**
(§8b): for every nonzero positive `x ∈ M` there is a nonzero positive `y ∈ M`
with `y ≤ x` in the operator order and `W y < ⊤`.  The public domain of the
weight is the positive cone `positiveCone M`, and every exported law is stated
there; the extended weight is never presented as a linear functional on
arbitrary operators.

**Forbidden downstream claims, none of which appear here.**  No claim that
fullness alone produces the comparison family or the global weight, no
direct-integral theorem, no Lane-H factorization or factor statement, and no
assertion that a compression certificate by itself is standard semifiniteness.

## What is assumed and what is proved

The construction needs one piece of comparison data which is *not* proved here,
and which is named explicitly as the structure `ComparisonFamily`:

* a sequence `v : ℕ → B(H)` of partial isometries of `M`;
* their source projections `v n ^* v n` lie **below `q`**;
* their range projections `v n v n ^*` are **pairwise orthogonal** and their
  partial sums converge **strongly to `1`**; and
* the **normalization** `v 0 ^* v 0 = v 0 v 0 ^* = q` for the distinguished
  zeroth member.

Every one of these premises is an explicit field.  *Nothing about the resulting
weight is assumed*: additivity, positive homogeneity, monotonicity, traciality,
faithfulness, normality (the monotone-supremum law) and semifiniteness are all
proved from the displayed construction.  In particular the positive square root
used in §8b is *constructed* from the pinned Mathlib continuous functional
calculus and proved to lie in `M`; it is not a hypothesis or a supplied
interface.

The global extended-positive weight is

`globalWeight q Ω v x = ∑' n, ENNReal.ofReal (Re (tau_q (v n ^* x v n)))`,

a monotone `ℝ≥0∞`-valued series of transported P50U corner traces.  Because it
is `ℝ≥0∞`-valued it is not a bounded linear functional, so its normality is
*not* stated as ultraweak continuity on `M`; it is stated as the
monotone-supremum law `⨆ k, W (x k) = W y` for an increasing sequence `x k`
converging ultraweakly to `y`, and that law is proved by feeding P50U's
ultraweak-normal bounded corner functional through the ultraweak continuity of
the conjugation `T ↦ a T b` (proved here, §2).

## Contents

* §1 `ComparisonFamily` — the explicit comparison/orthogonality/normalization
  premises, and their elementary partial-isometry consequences.
* §2 `UltraweakCoeff.conj`, `continuous_conjUltraweak` — the extra P50U-style
  ultraweak API needed for the normality proof.
* §3 `globalWeight` — the definition, and its evaluation as a sum of vector
  states `∑' n, ⟪v n Ω, x (v n Ω)⟫`.
* §4 additivity, positive homogeneity, monotonicity.
* §5 traciality `W (a^* a) = W (a a^*)`.
* §6 faithfulness.
* §7 normality: the monotone-supremum law, in the ultraweak form (using P50U)
  and in the strong-convergence form.
* §8 the value on finite partial sums, the restriction to the P50U corner trace
  on `q M q`, and the finite-compression certificate
  `globalWeight_finite_compressions`.
* §8b `posSqrt` — the proved positive square root inside `M` — the compressed
  subelement `compressedSub v N x = x^{1/2} p_N x^{1/2}`, its positivity, its
  order inequality `≤ x`, its finite weight, positive-cone faithfulness, order
  monotonicity, and the standard semifiniteness theorem
  `globalWeight_semifinite_positiveCone`.
* §9 the conditional production of a comparison family from an orthogonal
  decomposition of `1` by projections subequivalent to `q`, plus non-vacuity
  witnesses.  The σ-finite comparison theorem itself is **not** available in
  pinned Mathlib and is **not** proved here; it is exactly the named hypothesis
  of that theorem, so no global weight is claimed to follow from fullness alone.
* §10 `positiveCone`, `IsGlobalFaithfulNormalSemifiniteTrace` and the exported
  theorem `full_corner_global_semifinite_weight` collecting all the weight laws
  on the positive cone.
* §11 `full_finite_corner_globalized_weight`: the same conclusion from the P51 /
  P50U input data, recording P51's finiteness and fullness of `q` alongside the
  global weight laws.

## Status classification

1. *Checked infrastructure developed here*: the extended-positive weight
   `globalWeight`, its `ℝ≥0∞` API, the ultraweak conjugation continuity, the
   positive square root inside a von Neumann algebra, and all the weight laws
   including standard positive-cone semifiniteness.
2. *Conditional results*: everything is conditional on the explicitly named
   `ComparisonFamily` premises (and, in §11, on the P51/P50U input data).
3. *Open source obstruction*: the σ-finite comparison theorem producing the
   orthogonal decomposition of `1` from fullness of `q` is not available in
   pinned Mathlib and is not proved here; §9 reduces the comparison family to
   that decomposition but does not derive the decomposition itself.
-/

universe u v

namespace AristotleCandidates
namespace FullCornerSemifiniteWeight

open Filter Topology
open FiniteCornerTrace ProjectionTower NormalFaithfulCornerTrace UltraweakNormality
open scoped InnerProductSpace ENNReal

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §1  The explicit comparison family -/

/-- The **source projection** `v n ^* v n` of the `n`-th comparison partial isometry. -/
noncomputable def srcProj (v : ℕ → H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H := star (v n) * v n

/-- The **range projection** `v n v n ^*` of the `n`-th comparison partial isometry. -/
noncomputable def rngProj (v : ℕ → H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H := v n * star (v n)

/-- The finite partial sums `∑_{m < N} v m v m ^*` of the range projections. -/
noncomputable def partialProj (v : ℕ → H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  ∑ m ∈ Finset.range N, rngProj v m

/-- **The explicit comparison premises of P60.**

A *normalized countable comparison family* for the projection `q` of `M` is a sequence of
partial isometries of `M` whose source projections lie below `q`, whose range projections are
pairwise orthogonal with partial sums converging strongly to `1`, and whose zeroth member has
source and range projection exactly `q`.

This is the only assumption of the packet beyond the P50U corner data; no property of the
global weight constructed from it is assumed. -/
structure ComparisonFamily (M : VonNeumannAlgebra H) (q : H →L[ℂ] H)
    (v : ℕ → H →L[ℂ] H) : Prop where
  /-- Each comparison operator lies in `M`. -/
  mem : ∀ n, v n ∈ M
  /-- Each `v n` is a partial isometry: its source `v n ^* v n` is idempotent. -/
  idem_src : ∀ n, IsIdempotentElem (srcProj v n)
  /-- Comparison: every source projection lies below `q`. -/
  src_le : ∀ n, VonNeumannAlgebra.ProjLe (srcProj v n) q
  /-- The range projections are pairwise orthogonal. -/
  orthogonal : ∀ m n, m ≠ n → rngProj v m * rngProj v n = 0
  /-- Convergence: the partial sums of the range projections converge strongly to `1`. -/
  sum_strong : ∀ ξ : H, Tendsto (fun N => partialProj v N ξ) atTop (𝓝 ξ)
  /-- Normalization of the distinguished zeroth member: its source projection is `q`.
  (Required by the specification of a normalized family; the proofs below use it only
  through `src_le 0`.) -/
  src_zero : srcProj v 0 = q
  /-- Normalization of the distinguished zeroth member: its range projection is `q`. -/
  rng_zero : rngProj v 0 = q

namespace ComparisonFamily

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {v : ℕ → H →L[ℂ] H}

theorem srcProj_mem (hf : ComparisonFamily M q v) (n : ℕ) : srcProj v n ∈ M :=
  mul_mem (star_mem (hf.mem n)) (hf.mem n)

theorem rngProj_mem (hf : ComparisonFamily M q v) (n : ℕ) : rngProj v n ∈ M :=
  mul_mem (hf.mem n) (star_mem (hf.mem n))

theorem srcProj_star (v : ℕ → H →L[ℂ] H) (n : ℕ) : star (srcProj v n) = srcProj v n := by
  simp [srcProj, star_mul]

theorem rngProj_star (v : ℕ → H →L[ℂ] H) (n : ℕ) : star (rngProj v n) = rngProj v n := by
  simp [rngProj, star_mul]

theorem mul_srcProj (hf : ComparisonFamily M q v) (n : ℕ) : v n * srcProj v n = v n := by
  have h : IsIdempotentElem (star (v n) * v n) := hf.idem_src n
  exact VonNeumannAlgebra.mul_star_mul_self_eq_self h

theorem srcProj_mul_star (hf : ComparisonFamily M q v) (n : ℕ) :
    srcProj v n * star (v n) = star (v n) := by
  have h := congrArg star (hf.mul_srcProj n)
  rwa [star_mul, srcProj_star] at h

theorem idem_rng (hf : ComparisonFamily M q v) (n : ℕ) : IsIdempotentElem (rngProj v n) := by
  show rngProj v n * rngProj v n = rngProj v n
  calc v n * star (v n) * (v n * star (v n))
      = (v n * srcProj v n) * star (v n) := by simp [srcProj]; noncomm_ring
    _ = v n * star (v n) := by rw [hf.mul_srcProj]

theorem rngProj_mul_self (hf : ComparisonFamily M q v) (n : ℕ) : rngProj v n * v n = v n := by
  have h : IsIdempotentElem (v n * star (v n)) := hf.idem_rng n
  exact VonNeumannAlgebra.star_mul_self_mul_eq_self h

theorem star_mul_rngProj (hf : ComparisonFamily M q v) (n : ℕ) :
    star (v n) * rngProj v n = star (v n) := by
  have h := congrArg star (hf.rngProj_mul_self n)
  rwa [star_mul, rngProj_star] at h

theorem q_mul_star (hf : ComparisonFamily M q v) (n : ℕ) : q * star (v n) = star (v n) := by
  conv_lhs => rw [← hf.srcProj_mul_star n]
  rw [← mul_assoc, (hf.src_le n).2]
  exact hf.srcProj_mul_star n

theorem mul_q (hf : ComparisonFamily M q v) (n : ℕ) : v n * q = v n := by
  conv_lhs => rw [← hf.mul_srcProj n]
  rw [mul_assoc, (hf.src_le n).1]
  exact hf.mul_srcProj n

theorem star_mul_of_ne (hf : ComparisonFamily M q v) {m n : ℕ} (h : m ≠ n) :
    star (v m) * v n = 0 := by
  calc star (v m) * v n = (star (v m) * rngProj v m) * (rngProj v n * v n) := by
        rw [hf.star_mul_rngProj, hf.rngProj_mul_self]
    _ = star (v m) * (rngProj v m * rngProj v n) * v n := by noncomm_ring
    _ = 0 := by rw [hf.orthogonal m n h]; simp

/-- `q` is the zeroth range projection, so `q v m ^* = 0` for `m ≠ 0`. -/
theorem star_mul_q_of_ne (hf : ComparisonFamily M q v) {m : ℕ} (h : m ≠ 0) :
    star (v m) * q = 0 := by
  have h0 : q = rngProj v 0 := hf.rng_zero.symm
  calc star (v m) * q = (star (v m) * rngProj v m) * rngProj v 0 := by
        rw [hf.star_mul_rngProj, ← h0]
    _ = star (v m) * (rngProj v m * rngProj v 0) := by noncomm_ring
    _ = 0 := by rw [hf.orthogonal m 0 h]; simp

theorem q_mul_of_ne (hf : ComparisonFamily M q v) {m : ℕ} (h : m ≠ 0) : q * v m = 0 := by
  have h1 := congrArg star (hf.star_mul_q_of_ne h)
  have hq : star q = q := by
    have : q = rngProj v 0 := hf.rng_zero.symm
    rw [this, rngProj_star]
  rwa [star_mul, hq, star_star, star_zero] at h1

theorem q_isStarProjection (hf : ComparisonFamily M q v) : IsStarProjection q := by
  constructor
  · show q * q = q
    rw [← hf.rng_zero]
    exact hf.idem_rng 0
  · show star q = q
    rw [← hf.rng_zero, rngProj_star]

theorem q_mem (hf : ComparisonFamily M q v) : q ∈ M := by
  rw [← hf.rng_zero]; exact hf.rngProj_mem 0

end ComparisonFamily

/-! ## §2  Ultraweak continuity of conjugation

The P50U ultraweak topology is the topology induced by all absolutely summable
matrix-coefficient series.  The map `T ↦ a T b` is ultraweakly continuous because the
coefficient data can be transported through `a` and `b`.  This is the piece of extra
`UltraweakCoeff` API needed to feed P50U's normal corner functional with a converging net. -/

/-- Transport of an ultraweak coefficient datum through a two-sided multiplication:
`(conjCoeff c a b).eval T = c.eval (a * T * b)`. -/
noncomputable def conjCoeff (c : UltraweakCoeff H) (a b : H →L[ℂ] H) :
    UltraweakCoeff H where
  x := fun n => b (c.x n)
  y := fun n => (c.y n).comp a
  summable_norm := by
    have hsum : Summable fun n => (‖b‖ * ‖a‖) * (‖c.x n‖ * ‖c.y n‖) :=
      c.summable_norm.mul_left (‖b‖ * ‖a‖)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
    have h1 : ‖b (c.x n)‖ ≤ ‖b‖ * ‖c.x n‖ := b.le_opNorm _
    have h2 : ‖(c.y n).comp a‖ ≤ ‖c.y n‖ * ‖a‖ := ContinuousLinearMap.opNorm_comp_le _ _
    calc ‖b (c.x n)‖ * ‖(c.y n).comp a‖ ≤ (‖b‖ * ‖c.x n‖) * (‖c.y n‖ * ‖a‖) := by
          gcongr
      _ = (‖b‖ * ‖a‖) * (‖c.x n‖ * ‖c.y n‖) := by ring

omit [CompleteSpace H] in
@[simp] theorem eval_conjCoeff (c : UltraweakCoeff H) (a b T : H →L[ℂ] H) :
    (conjCoeff c a b).eval T = c.eval (a * T * b) := by
  simp only [UltraweakCoeff.eval, conjCoeff]
  rfl

omit [CompleteSpace H] in
/-- **Ultraweak continuity of conjugation.**  For fixed `a b`, the map `T ↦ a T b` is
continuous for the ultraweak topology of P50U. -/
theorem continuous_conjUltraweak (a b : H →L[ℂ] H) :
    Continuous fun T : UltraweakCLM H => toUltraweak (a * T.toCLM * b) := by
  refine UltraweakCLM.continuous_of_forall_eval fun c => ?_
  have h := UltraweakCLM.continuous_eval (conjCoeff c a b)
  simpa using h

/-! ## §3  The global extended-positive weight -/

section Weight

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- The `n`-th **transported corner trace** `Re (tau_q (v n ^* x v n))`, as an element of
`ℝ≥0∞`.  For positive `x` this is exactly the P50U corner trace of the transported operator,
which lies in `q M q` because the source projection of `v n` is below `q`. -/
noncomputable def weightTerm (q : H →L[ℂ] H) (Ω : H) (v : ℕ → H →L[ℂ] H) (x : H →L[ℂ] H)
    (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((cornerTau q Ω (star (v n) * x * v n)).re)

/-- **The global extended-positive weight.**  `W x = ∑' n, Re (tau_q (v n ^* x v n))`, the
monotone `ℝ≥0∞`-valued series of transported P50U corner traces.

This is a *definition*, not an assumed interface: every weight law below is proved from it. -/
noncomputable def globalWeight (q : H →L[ℂ] H) (Ω : H) (v : ℕ → H →L[ℂ] H)
    (x : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' n, weightTerm q Ω v x n

theorem globalWeight_def (q : H →L[ℂ] H) (Ω : H) (v : ℕ → H →L[ℂ] H) (x : H →L[ℂ] H) :
    globalWeight q Ω v x = ∑' n, weightTerm q Ω v x n := rfl

/-- The transported corner trace is the vector state at `v n Ω`. -/
theorem cornerTau_conj (hf : ComparisonFamily M q v) (x : H →L[ℂ] H) (n : ℕ) :
    cornerTau q Ω (star (v n) * x * v n) = ⟪v n Ω, x (v n Ω)⟫_ℂ := by
  have hcomp : q * (star (v n) * x * v n) * q = star (v n) * x * v n := by
    calc q * (star (v n) * x * v n) * q = (q * star (v n)) * x * (v n * q) := by noncomm_ring
      _ = star (v n) * x * v n := by rw [hf.q_mul_star n, hf.mul_q n]
  rw [cornerTau_apply, hcomp]
  show ⟪Ω, (star (v n)) (x (v n Ω))⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- The weight terms in vector-state form. -/
theorem weightTerm_eq (hf : ComparisonFamily M q v) (x : H →L[ℂ] H) (n : ℕ) :
    weightTerm q Ω v x n = ENNReal.ofReal ((⟪v n Ω, x (v n Ω)⟫_ℂ).re) := by
  rw [weightTerm, cornerTau_conj hf]

/-- The global weight as a sum of vector states. -/
theorem globalWeight_eq (hf : ComparisonFamily M q v) (x : H →L[ℂ] H) :
    globalWeight q Ω v x = ∑' n, ENNReal.ofReal ((⟪v n Ω, x (v n Ω)⟫_ℂ).re) :=
  tsum_congr fun n => weightTerm_eq hf x n

omit [CompleteSpace H] in
/-- The quadratic form of a positive operator is nonnegative in the convention `⟪ξ, x ξ⟫`. -/
theorem reInner_nonneg_of_isPositive {x : H →L[ℂ] H} (hx : x.IsPositive) (ξ : H) :
    0 ≤ (⟪ξ, x ξ⟫_ℂ).re := by
  have h := hx.2 ξ
  rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h
  have hre : (⟪ξ, x ξ⟫_ℂ).re = (⟪x ξ, ξ⟫_ℂ).re := by
    rw [← inner_conj_symm ξ (x ξ), Complex.conj_re]
  rw [hre]
  exact h

/-- `x^* x` is a positive operator. -/
theorem isPositive_star_mul_self (a : H →L[ℂ] H) : (star a * a).IsPositive := by
  refine ⟨?_, fun ξ => ?_⟩
  · have hsa : IsSelfAdjoint (star a * a) := by
      rw [IsSelfAdjoint, star_mul, star_star]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hsa
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have h : (star a * a) ξ = (star a) (a ξ) := rfl
    rw [h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    simpa using inner_self_nonneg (𝕜 := ℂ) (x := a ξ)

theorem inner_star_mul_self (a : H →L[ℂ] H) (ξ : H) :
    (⟪ξ, (star a * a) ξ⟫_ℂ).re = ‖a ξ‖ ^ 2 := by
  have h : (star a * a) ξ = (star a) (a ξ) := rfl
  rw [h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

end Weight

/-! ## §4  Additivity, positive homogeneity and monotonicity -/

section Laws

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- **Additivity of the weight on the positive cone.** -/
theorem globalWeight_add (hf : ComparisonFamily M q v) {x y : H →L[ℂ] H}
    (hx : x.IsPositive) (hy : y.IsPositive) :
    globalWeight q Ω v (x + y) = globalWeight q Ω v x + globalWeight q Ω v y := by
  rw [globalWeight_eq hf, globalWeight_eq hf, globalWeight_eq hf,
    ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  have h : (⟪v n Ω, (x + y) (v n Ω)⟫_ℂ).re
      = (⟪v n Ω, x (v n Ω)⟫_ℂ).re + (⟪v n Ω, y (v n Ω)⟫_ℂ).re := by
    simp
  rw [h, ENNReal.ofReal_add (reInner_nonneg_of_isPositive hx _)
    (reInner_nonneg_of_isPositive hy _)]

/-- **Positive homogeneity of the weight.** -/
theorem globalWeight_smul (hf : ComparisonFamily M q v) {c : ℝ} (hc : 0 ≤ c)
    (x : H →L[ℂ] H) :
    globalWeight q Ω v ((c : ℂ) • x) = ENNReal.ofReal c * globalWeight q Ω v x := by
  rw [globalWeight_eq hf, globalWeight_eq hf, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  have h : (⟪v n Ω, ((c : ℂ) • x) (v n Ω)⟫_ℂ).re = c * (⟪v n Ω, x (v n Ω)⟫_ℂ).re := by
    simp [Complex.mul_re]
  rw [h, ENNReal.ofReal_mul hc]

/-- The weight vanishes at `0`. -/
@[simp] theorem globalWeight_zero (q : H →L[ℂ] H) (Ω : H) (v : ℕ → H →L[ℂ] H) :
    globalWeight q Ω v 0 = 0 := by
  simp [globalWeight, weightTerm]

/-- **Monotonicity** for the quadratic-form order. -/
theorem globalWeight_mono (hf : ComparisonFamily M q v) {x y : H →L[ℂ] H}
    (h : ∀ ξ : H, (⟪ξ, x ξ⟫_ℂ).re ≤ (⟪ξ, y ξ⟫_ℂ).re) :
    globalWeight q Ω v x ≤ globalWeight q Ω v y := by
  rw [globalWeight_eq hf, globalWeight_eq hf]
  exact ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (h _)

end Laws

/-! ## §5  Traciality

The proof is the classical one: expanding `1 = ∑ v m v m ^*` inside each transported corner
trace turns `W (a^* a)` into the double series `∑_{n,m} tau_q (b_{nm}^* b_{nm})` with
`b_{nm} = v m ^* a v n` a genuine element of the corner `q M q`, and the corner traciality of
P50U (in the form of P50's `norm_star_apply_eq_of_cornerTracial`) exchanges `b^* b` with
`b b^*`.  Interchanging the two summations then gives `W (a a^*)`. -/

section Tracial

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- A partial isometry preserves the norm on the range of its adjoint. -/
theorem norm_apply_star (hf : ComparisonFamily M q v) (m : ℕ) (w : H) :
    ‖v m ((star (v m)) w)‖ = ‖(star (v m)) w‖ := by
  set ζ : H := (star (v m)) w with hζdef
  have hζ : (srcProj v m) ζ = ζ := by
    have h1 : (srcProj v m) ζ = (srcProj v m * star (v m)) w := rfl
    rw [h1, hf.srcProj_mul_star]
  have hadj : ((ContinuousLinearMap.adjoint (v m)) (v m ζ)) = ζ := by
    have : ((ContinuousLinearMap.adjoint (v m)) (v m ζ)) = (srcProj v m) ζ := by
      rw [srcProj, ContinuousLinearMap.star_eq_adjoint]
      rfl
    rw [this, hζ]
  have h1 : ⟪v m ζ, v m ζ⟫_ℂ = ⟪ζ, ζ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
  have h2 : (‖v m ζ‖ : ℝ) ^ 2 = (‖ζ‖ : ℝ) ^ 2 := by
    have := congrArg Complex.re h1
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using this
  nlinarith [norm_nonneg (v m ζ), norm_nonneg ζ]

/-- **Countable additivity of the identity along the family.**  For every vector, the squared
norms of its components along the pairwise orthogonal range projections sum to its squared
norm.  This is the only place the strong convergence premise `sum_strong` is used in the
traciality proof. -/
theorem tsum_rngProj_norm_sq (hf : ComparisonFamily M q v) (η : H) :
    ∑' m, ENNReal.ofReal (‖rngProj v m η‖ ^ 2) = ENNReal.ofReal (‖η‖ ^ 2) := by
  have hterm : ∀ m, (⟪η, rngProj v m η⟫_ℂ).re = ‖rngProj v m η‖ ^ 2 := by
    intro m
    have hsa : star (rngProj v m) = rngProj v m := ComparisonFamily.rngProj_star v m
    have hid : rngProj v m * rngProj v m = rngProj v m := hf.idem_rng m
    have h1 : ⟪η, rngProj v m η⟫_ℂ = ⟪rngProj v m η, rngProj v m η⟫_ℂ := by
      have h2 : ⟪rngProj v m η, rngProj v m η⟫_ℂ
          = ⟪η, ((ContinuousLinearMap.adjoint (rngProj v m)) (rngProj v m η))⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      have h3 : ((ContinuousLinearMap.adjoint (rngProj v m)) (rngProj v m η))
          = rngProj v m η := by
        have h4 : (ContinuousLinearMap.adjoint (rngProj v m)) = rngProj v m := by
          rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa
        rw [h4]
        exact congrArg (fun t : H →L[ℂ] H => t η) hid
      rw [h2, h3]
    rw [h1, inner_self_eq_norm_sq_to_K]
    norm_cast
  -- the partial sums of the real series
  set u : ℕ → ℝ := fun N => ∑ m ∈ Finset.range N, ‖rngProj v m η‖ ^ 2 with hudef
  have hpartial : ∀ N, (⟪η, partialProj v N η⟫_ℂ).re = u N := by
    intro N
    have h1 : partialProj v N η = ∑ m ∈ Finset.range N, rngProj v m η := by
      rw [partialProj]
      simp
    rw [h1, inner_sum, hudef]
    simp only [Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => hterm m
  have hlim : Tendsto u atTop (𝓝 (‖η‖ ^ 2)) := by
    have h1 : Tendsto (fun N => ⟪η, partialProj v N η⟫_ℂ) atTop (𝓝 (⟪η, η⟫_ℂ)) :=
      ((innerSL ℂ η).continuous.tendsto _).comp (hf.sum_strong η)
    have h2 : Tendsto (fun N => (⟪η, partialProj v N η⟫_ℂ).re) atTop (𝓝 ((⟪η, η⟫_ℂ).re)) :=
      (Complex.continuous_re.tendsto _).comp h1
    have h3 : (⟪η, η⟫_ℂ).re = ‖η‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [h3] at h2
    exact h2.congr fun N => hpartial N
  -- pass to `ℝ≥0∞`
  have hmono : Monotone fun N => ENNReal.ofReal (u N) := by
    intro N N' hN
    refine ENNReal.ofReal_le_ofReal ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN)
      fun m _ _ => by positivity
  have htends : Tendsto (fun N => ENNReal.ofReal (u N)) atTop (𝓝 (ENNReal.ofReal (‖η‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hlim
  have hsup : (⨆ N, ENNReal.ofReal (u N)) = ENNReal.ofReal (‖η‖ ^ 2) :=
    tendsto_nhds_unique (tendsto_atTop_iSup hmono) htends
  rw [ENNReal.tsum_eq_iSup_nat, ← hsup]
  refine iSup_congr fun N => ?_
  rw [hudef]
  exact (ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity).symm

/-- The `(n, m)` component of `a v n Ω` along the `m`-th range projection has the norm of the
corner element `v m ^* a v n` applied to `Ω`. -/
theorem norm_rngProj_apply (hf : ComparisonFamily M q v) (a : H →L[ℂ] H) (n m : ℕ) :
    ‖rngProj v m (a (v n Ω))‖ = ‖(star (v m) * a * v n) Ω‖ := by
  have h1 : rngProj v m (a (v n Ω)) = v m ((star (v m)) (a (v n Ω))) := rfl
  rw [h1, norm_apply_star hf]
  rfl

/-- **The double-series expansion of the weight at `a^* a`.** -/
theorem globalWeight_star_mul_self (hf : ComparisonFamily M q v) (a : H →L[ℂ] H) :
    globalWeight q Ω v (star a * a)
      = ∑' n, ∑' m, ENNReal.ofReal (‖(star (v m) * a * v n) Ω‖ ^ 2) := by
  rw [globalWeight_eq hf]
  refine tsum_congr fun n => ?_
  rw [inner_star_mul_self, ← tsum_rngProj_norm_sq hf (a (v n Ω))]
  exact tsum_congr fun m => by rw [norm_rngProj_apply hf]

/-- **Traciality of the global weight.**  `W (a^* a) = W (a a^*)` for every `a ∈ M`. -/
theorem globalWeight_tracial (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {a : H →L[ℂ] H} (ha : a ∈ M) :
    globalWeight q Ω v (star a * a) = globalWeight q Ω v (a * star a) := by
  have hq1 : star q = q := hf.q_isStarProjection.isSelfAdjoint.star_eq
  -- the corner elements `b n m = v m ^* a v n`
  have hcorner : ∀ n m : ℕ, ‖(star (star (v n) * a * v m)) Ω‖ = ‖(star (v n) * a * v m) Ω‖ := by
    intro n m
    refine norm_star_apply_eq_of_cornerTracial h.tracial hq1
      (mul_mem (mul_mem (star_mem (hf.mem n)) ha) (hf.mem m)) ?_ ?_
    · calc q * (star (v n) * a * v m) = (q * star (v n)) * a * v m := by noncomm_ring
        _ = star (v n) * a * v m := by rw [hf.q_mul_star n]
    · calc (star (v n) * a * v m) * q = star (v n) * a * (v m * q) := by noncomm_ring
        _ = star (v n) * a * v m := by rw [hf.mul_q m]
  have hstar : ∀ n m : ℕ,
      star (v m) * star a * v n = star (star (v n) * a * v m) := by
    intro n m
    rw [star_mul, star_mul, star_star]
    noncomm_ring
  calc globalWeight q Ω v (star a * a)
      = ∑' n, ∑' m, ENNReal.ofReal (‖(star (v m) * a * v n) Ω‖ ^ 2) :=
        globalWeight_star_mul_self hf a
    _ = ∑' m, ∑' n, ENNReal.ofReal (‖(star (v m) * a * v n) Ω‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' n, ∑' m, ENNReal.ofReal (‖(star (v n) * a * v m) Ω‖ ^ 2) := rfl
    _ = ∑' n, ∑' m, ENNReal.ofReal (‖(star (v m) * star a * v n) Ω‖ ^ 2) := by
        refine tsum_congr fun n => tsum_congr fun m => ?_
        rw [hstar n m, hcorner n m]
    _ = globalWeight q Ω v (a * star a) := by
        have h1 := globalWeight_star_mul_self (Ω := Ω) hf (star a)
        rw [star_star] at h1
        exact h1.symm

end Tracial

/-! ## §6  Faithfulness -/

section Faithful

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- **Faithfulness of the global weight.**  If `a ∈ M` and `W (a^* a) = 0` then `a = 0`.

The argument is: vanishing of the `n`-th term makes the corner element `v n ^* a^* a v n`
annihilate `Ω`, hence vanish by faithfulness of the P50U corner state; the C⋆-identity then
gives `a v n = 0`, so `a` kills every range projection, and therefore `a = 0` by the strong
convergence of the partial sums. -/
theorem globalWeight_faithful (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) (hqΩ : q Ω = Ω)
    {a : H →L[ℂ] H} (ha : a ∈ M) (h0 : globalWeight q Ω v (star a * a) = 0) : a = 0 := by
  have hqsa : IsSelfAdjoint q := hf.q_isStarProjection.isSelfAdjoint
  -- Step 1: every term vanishes.
  have hterm : ∀ n, a (v n Ω) = 0 := by
    intro n
    have h1 : ∑' n, ENNReal.ofReal ((⟪v n Ω, (star a * a) (v n Ω)⟫_ℂ).re) = 0 := by
      rw [← globalWeight_eq hf]; exact h0
    have h2 := (ENNReal.tsum_eq_zero.mp h1) n
    rw [inner_star_mul_self] at h2
    have h3 : ‖a (v n Ω)‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h2
    have h4 : ‖a (v n Ω)‖ = 0 := by nlinarith [norm_nonneg (a (v n Ω))]
    exact norm_eq_zero.mp h4
  -- Step 2: the transported corner element vanishes.
  have hav : ∀ n, a * v n = 0 := by
    intro n
    set y : H →L[ℂ] H := star (a * v n) * (a * v n) with hydef
    have hyM : y ∈ M := mul_mem (star_mem (mul_mem ha (hf.mem n))) (mul_mem ha (hf.mem n))
    have hy1 : q * y = y := by
      rw [hydef, star_mul]
      calc q * (star (v n) * star a * (a * v n))
          = (q * star (v n)) * star a * (a * v n) := by noncomm_ring
        _ = star (v n) * star a * (a * v n) := by rw [hf.q_mul_star n]
    have hy2 : y * q = y := by
      rw [hydef, star_mul]
      calc star (v n) * star a * (a * v n) * q
          = star (v n) * star a * a * (v n * q) := by noncomm_ring
        _ = star (v n) * star a * (a * v n) := by rw [hf.mul_q n]; noncomm_ring
    have hyΩ : y Ω = 0 := by
      have h1 : y Ω = (star (a * v n)) (a (v n Ω)) := rfl
      rw [h1, hterm n, map_zero]
    have hzero : cornerTau q Ω (star y * y) = 0 := by
      rw [cornerTau_star_mul_self hqsa, hqΩ, hyΩ]
      simp
    have hy0 : y = 0 := h.faithful y hyM hy1 hy2 hzero
    exact (CStarRing.star_mul_self_eq_zero_iff (a * v n)).mp hy0
  -- Step 3: `a` annihilates every range projection, hence vanishes.
  have harng : ∀ n, a * rngProj v n = 0 := by
    intro n
    rw [rngProj, ← mul_assoc, hav n, zero_mul]
  refine ContinuousLinearMap.ext fun ξ => ?_
  have h1 : Tendsto (fun N => a (partialProj v N ξ)) atTop (𝓝 (a ξ)) :=
    (a.continuous.tendsto _).comp (hf.sum_strong ξ)
  have h2 : ∀ N, a (partialProj v N ξ) = 0 := by
    intro N
    have h3 : a (partialProj v N ξ) = ∑ m ∈ Finset.range N, (a * rngProj v m) ξ := by
      rw [partialProj]
      simp [ContinuousLinearMap.sum_apply]
    rw [h3]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [harng m]
    simp
  have h4 : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 (a ξ)) := by
    simpa [h2] using h1
  simpa using tendsto_nhds_unique h4 tendsto_const_nhds

end Faithful

/-! ## §7  Normality: the monotone-supremum law

The global weight takes values in `ℝ≥0∞` and is not a bounded linear functional, so its
normality is *not* ultraweak continuity on `M`.  The statement proved here is the standard
weight-theoretic one: for an increasing sequence of operators converging to `y`,
`⨆ k, W (x k) = W y`.

The bounded, ultraweakly continuous object used in the proof is exactly P50U's corner
functional through its field `normal_ultraweak`. -/

section Normal

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

omit [CompleteSpace H] in
/-- Monotone interchange of a supremum and a sum in `ℝ≥0∞`. -/
theorem iSup_tsum_of_monotone {f : ℕ → ℕ → ℝ≥0∞} (hmono : ∀ n, Monotone fun k => f k n) :
    (⨆ k, ∑' n, f k n) = ∑' n, ⨆ k, f k n := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  exact iSup_congr fun s => (ENNReal.finsetSum_iSup_of_monotone fun n => hmono n).symm

/-- **The transported corner trace is ultraweakly continuous.**  This is P50U's
`normal_ultraweak` composed with the ultraweak continuity of `T ↦ v n ^* T v n`. -/
theorem continuous_cornerTau_conj (h : IsFaithfulUltraweakNormalTracialCorner M q Ω)
    (n : ℕ) :
    Continuous fun T : UltraweakCLM H => cornerTau q Ω (star (v n) * T.toCLM * v n) := by
  have h1 := h.normal_ultraweak
  have h2 := continuous_conjUltraweak (H := H) (star (v n)) (v n)
  exact h1.comp h2

/-- Each weight term is ultraweakly continuous as an `ℝ≥0∞`-valued function. -/
theorem tendsto_weightTerm_of_ultraweakTendsto
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) (n : ℕ)
    {x : ℕ → H →L[ℂ] H} {y : H →L[ℂ] H}
    (hconv : Tendsto (fun k => toUltraweak (x k)) atTop (𝓝 (toUltraweak y))) :
    Tendsto (fun k => weightTerm q Ω v (x k) n) atTop (𝓝 (weightTerm q Ω v y n)) := by
  have h1 := (continuous_cornerTau_conj (v := v) h n).tendsto (toUltraweak y)
  have h2 : Tendsto (fun k => cornerTau q Ω (star (v n) * x k * v n)) atTop
      (𝓝 (cornerTau q Ω (star (v n) * y * v n))) := h1.comp hconv
  exact (ENNReal.continuous_ofReal.tendsto _).comp ((Complex.continuous_re.tendsto _).comp h2)

/-- **Normality of the global weight (ultraweak form).**

If `x` is an increasing sequence for the quadratic-form order converging *ultraweakly* to `y`
— the standard hypothesis for normality of a weight — then `W y` is the supremum of the
`W (x k)`.

The only continuity input is P50U's ultraweak-normal bounded corner functional. -/
theorem globalWeight_iSup_of_ultraweakTendsto (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω)
    {x : ℕ → H →L[ℂ] H} {y : H →L[ℂ] H}
    (hmono : ∀ k, ∀ ξ : H, (⟪ξ, x k ξ⟫_ℂ).re ≤ (⟪ξ, x (k + 1) ξ⟫_ℂ).re)
    (hconv : Tendsto (fun k => toUltraweak (x k)) atTop (𝓝 (toUltraweak y))) :
    (⨆ k, globalWeight q Ω v (x k)) = globalWeight q Ω v y := by
  have hmono' : ∀ n, Monotone fun k => weightTerm q Ω v (x k) n := by
    intro n
    refine monotone_nat_of_le_succ fun k => ?_
    rw [weightTerm_eq hf, weightTerm_eq hf]
    exact ENNReal.ofReal_le_ofReal (hmono k (v n Ω))
  have hterm : ∀ n, (⨆ k, weightTerm q Ω v (x k) n) = weightTerm q Ω v y n := by
    intro n
    exact tendsto_nhds_unique (tendsto_atTop_iSup (hmono' n))
      (tendsto_weightTerm_of_ultraweakTendsto (v := v) h n hconv)
  calc (⨆ k, globalWeight q Ω v (x k)) = ∑' n, ⨆ k, weightTerm q Ω v (x k) n :=
        iSup_tsum_of_monotone hmono'
    _ = globalWeight q Ω v y := tsum_congr hterm

/-- **Normality of the global weight (strong-convergence form).**

The same monotone-supremum law for an increasing sequence converging in the strong operator
sense; this version uses the vector-state realization of the corner functional rather than
its ultraweak continuity. -/
theorem globalWeight_iSup_of_stronglyTendsto (hf : ComparisonFamily M q v)
    {x : ℕ → H →L[ℂ] H} {y : H →L[ℂ] H}
    (hmono : ∀ k, ∀ ξ : H, (⟪ξ, x k ξ⟫_ℂ).re ≤ (⟪ξ, x (k + 1) ξ⟫_ℂ).re)
    (hconv : ∀ ξ : H, Tendsto (fun k => x k ξ) atTop (𝓝 (y ξ))) :
    (⨆ k, globalWeight q Ω v (x k)) = globalWeight q Ω v y := by
  have hmono' : ∀ n, Monotone fun k => weightTerm q Ω v (x k) n := by
    intro n
    refine monotone_nat_of_le_succ fun k => ?_
    rw [weightTerm_eq hf, weightTerm_eq hf]
    exact ENNReal.ofReal_le_ofReal (hmono k (v n Ω))
  have hterm : ∀ n, (⨆ k, weightTerm q Ω v (x k) n) = weightTerm q Ω v y n := by
    intro n
    have h1 : Tendsto (fun k => ⟪v n Ω, x k (v n Ω)⟫_ℂ) atTop (𝓝 (⟪v n Ω, y (v n Ω)⟫_ℂ)) :=
      ((innerSL ℂ (v n Ω)).continuous.tendsto _).comp (hconv (v n Ω))
    have h2 : Tendsto (fun k => weightTerm q Ω v (x k) n) atTop
        (𝓝 (weightTerm q Ω v y n)) := by
      have h3 := (ENNReal.continuous_ofReal.tendsto _).comp
        ((Complex.continuous_re.tendsto _).comp h1)
      rw [weightTerm_eq hf]
      exact h3.congr fun k => (weightTerm_eq hf (x k) n).symm
    exact tendsto_nhds_unique (tendsto_atTop_iSup (hmono' n)) h2
  calc (⨆ k, globalWeight q Ω v (x k)) = ∑' n, ⨆ k, weightTerm q Ω v (x k) n :=
        iSup_tsum_of_monotone hmono'
    _ = globalWeight q Ω v y := tsum_congr hterm

end Normal

/-! ## §8  Finite partial sums, the corner restriction, and semifiniteness -/

section Semifinite

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- The transported operator of a range projection: `v m ^* (v n v n ^*) v m` is `v m ^* v m`
when `m = n` and `0` otherwise. -/
theorem conj_rngProj (hf : ComparisonFamily M q v) (n m : ℕ) :
    star (v m) * rngProj v n * v m = if m = n then srcProj v m else 0 := by
  by_cases hmn : m = n
  · subst hmn
    have h1 : star (v m) * rngProj v m * v m = srcProj v m * srcProj v m := by
      rw [rngProj, srcProj]; noncomm_ring
    rw [h1, (hf.idem_src m), if_pos rfl]
  · have h1 : star (v m) * rngProj v n * v m
        = (star (v m) * v n) * (star (v n) * v m) := by rw [rngProj]; noncomm_ring
    rw [h1, hf.star_mul_of_ne hmn, zero_mul, if_neg hmn]

/-- **The value of the weight on a single range projection** is the corner trace of the
corresponding source projection. -/
theorem globalWeight_rngProj (hf : ComparisonFamily M q v) (n : ℕ) :
    globalWeight q Ω v (rngProj v n) = ENNReal.ofReal ((cornerTau q Ω (srcProj v n)).re) := by
  rw [globalWeight_def]
  refine tsum_eq_single n ?_ |>.trans ?_
  · intro m hm
    rw [weightTerm, conj_rngProj hf n m, if_neg hm]
    simp
  · rw [weightTerm, conj_rngProj hf n n, if_pos rfl]

/-- **The value of the weight on the finite partial sums** `∑_{m<N} v m v m ^*`: it is the
finite sum of the corner traces of the source projections, and in particular finite. -/
theorem globalWeight_partialProj (hf : ComparisonFamily M q v) (N : ℕ) :
    globalWeight q Ω v (partialProj v N)
      = ∑ m ∈ Finset.range N, ENNReal.ofReal ((cornerTau q Ω (srcProj v m)).re) := by
  have hconj : ∀ m : ℕ, star (v m) * partialProj v N * v m
      = if m ∈ Finset.range N then srcProj v m else 0 := by
    intro m
    have h1 : star (v m) * partialProj v N * v m
        = ∑ n ∈ Finset.range N, star (v m) * rngProj v n * v m := by
      rw [partialProj, Finset.mul_sum, Finset.sum_mul]
    rw [h1]
    simp only [conj_rngProj hf]
    rw [Finset.sum_ite_eq (Finset.range N) m (fun _ => srcProj v m)]
  rw [globalWeight_def]
  rw [tsum_eq_sum (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [weightTerm, hconj m, if_pos hm]
  · intro m hm
    rw [weightTerm, hconj m, if_neg hm]
    simp

theorem globalWeight_partialProj_lt_top (hf : ComparisonFamily M q v) (N : ℕ) :
    globalWeight q Ω v (partialProj v N) < ⊤ := by
  rw [globalWeight_partialProj hf]
  exact ENNReal.sum_lt_top.2 fun m _ => ENNReal.ofReal_lt_top

/-- The partial sums are projections of `M`. -/
theorem partialProj_isStarProjection (hf : ComparisonFamily M q v) (N : ℕ) :
    IsStarProjection (partialProj v N) := by
  constructor
  · show partialProj v N * partialProj v N = partialProj v N
    rw [partialProj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m]
    · exact hf.idem_rng m
    · intro n _ hnm
      exact hf.orthogonal m n (Ne.symm hnm)
    · intro hm'
      exact absurd hm hm'
  · show star (partialProj v N) = partialProj v N
    rw [partialProj, star_sum]
    exact Finset.sum_congr rfl fun m _ => ComparisonFamily.rngProj_star v m

theorem partialProj_mem (hf : ComparisonFamily M q v) (N : ℕ) : partialProj v N ∈ M := by
  rw [partialProj]
  exact sum_mem fun m _ => hf.rngProj_mem m

/-- **The global weight restricts exactly to the P50U corner trace on `q M q`.** -/
theorem globalWeight_corner (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {x : H →L[ℂ] H} (hx : x ∈ M)
    (hqx : q * x = x) (hxq : x * q = x) :
    globalWeight q Ω v x = ENNReal.ofReal ((cornerTau q Ω x).re) := by
  have hqsa : IsSelfAdjoint q := hf.q_isStarProjection.isSelfAdjoint
  have hqv0 : q * v 0 = v 0 := by
    have h1 : rngProj v 0 * v 0 = v 0 := hf.rngProj_mul_self 0
    rwa [hf.rng_zero] at h1
  -- only the zeroth term survives
  have hother : ∀ m : ℕ, m ≠ 0 → weightTerm q Ω v x m = 0 := by
    intro m hm
    have h1 : star (v m) * x * v m = 0 := by
      have h2 : star (v m) * x = 0 := by
        conv_lhs => rw [← hqx]
        rw [← mul_assoc, hf.star_mul_q_of_ne hm, zero_mul]
      rw [h2, zero_mul]
    rw [weightTerm, h1]
    simp
  -- the zeroth term is the corner trace of `x`
  have hzero : weightTerm q Ω v x 0 = ENNReal.ofReal ((cornerTau q Ω x).re) := by
    have hx' : star (v 0) * x ∈ M.corner hqsa := by
      refine ⟨mul_mem (star_mem (hf.mem 0)) hx, ?_, ?_⟩
      · rw [← mul_assoc, hf.q_mul_star 0]
      · rw [mul_assoc, hxq]
    have hy' : v 0 ∈ M.corner hqsa := ⟨hf.mem 0, hqv0, hf.mul_q 0⟩
    have htr := h.tracial_corner hx' hy'
    have hyx : v 0 * (star (v 0) * x) = x := by
      rw [← mul_assoc]
      have h1 : v 0 * star (v 0) = q := hf.rng_zero
      rw [h1, hqx]
    rw [hyx] at htr
    have hcomp : cornerTau q Ω (star (v 0) * x * v 0)
        = tauVec Ω (star (v 0) * x * v 0) := by
      have h1 : q * (star (v 0) * x * v 0) * q = star (v 0) * x * v 0 := by
        calc q * (star (v 0) * x * v 0) * q = (q * star (v 0)) * x * (v 0 * q) := by
              noncomm_ring
          _ = star (v 0) * x * v 0 := by rw [hf.q_mul_star 0, hf.mul_q 0]
      rw [cornerTau_apply, h1]
      rfl
    have hcx : cornerTau q Ω x = tauVec Ω x := by
      have h1 : q * x * q = x := by rw [hqx, hxq]
      rw [cornerTau_apply, h1]
      rfl
    rw [weightTerm, hcomp, hcx]
    have h2 : star (v 0) * x * v 0 = (star (v 0) * x) * v 0 := by noncomm_ring
    rw [h2, htr]
  rw [globalWeight_def, tsum_eq_single 0 hother, hzero]

/-- The corner elements have finite weight. -/
theorem globalWeight_corner_lt_top (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {x : H →L[ℂ] H} (hx : x ∈ M)
    (hqx : q * x = x) (hxq : x * q = x) :
    globalWeight q Ω v x < ⊤ := by
  rw [globalWeight_corner hf h hx hqx hxq]
  exact ENNReal.ofReal_lt_top

/-- Compression by a projection is dominated by the projection scaled by the operator norm. -/
theorem reInner_compress_le {f x : H →L[ℂ] H} (hf1 : star f = f) (hf2 : f * f = f) (ξ : H) :
    (⟪ξ, (f * x * f) ξ⟫_ℂ).re ≤ (⟪ξ, ((‖x‖ : ℂ) • f) ξ⟫_ℂ).re := by
  have hfsa : IsSelfAdjoint f := hf1
  have h1 : ⟪ξ, (f * x * f) ξ⟫_ℂ = ⟪f ξ, x (f ξ)⟫_ℂ := by
    have h2 : (f * x * f) ξ = f (x (f ξ)) := rfl
    rw [h2, ← inner_isSelfAdjoint hfsa ξ (x (f ξ))]
  have h3 : ⟪ξ, ((‖x‖ : ℂ) • f) ξ⟫_ℂ = (‖x‖ : ℂ) * ⟪ξ, f ξ⟫_ℂ := by
    simp
  have h4 : ⟪ξ, f ξ⟫_ℂ = ((‖f ξ‖ : ℝ) : ℂ) ^ 2 := by
    have h5 : ⟪ξ, f ξ⟫_ℂ = ⟪f ξ, f ξ⟫_ℂ := by
      have h6 : f ξ = f (f ξ) := (congrArg (fun t : H →L[ℂ] H => t ξ) hf2).symm
      conv_lhs => rw [h6]
      rw [← inner_isSelfAdjoint hfsa ξ (f ξ)]
    rw [h5, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1, h3, h4]
  have h7 : (⟪f ξ, x (f ξ)⟫_ℂ).re ≤ ‖f ξ‖ * ‖x (f ξ)‖ := by
    calc (⟪f ξ, x (f ξ)⟫_ℂ).re ≤ ‖⟪f ξ, x (f ξ)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖f ξ‖ * ‖x (f ξ)‖ := norm_inner_le_norm _ _
  have h8 : ‖x (f ξ)‖ ≤ ‖x‖ * ‖f ξ‖ := x.le_opNorm _
  have h9 : ((‖x‖ : ℂ) * ((‖f ξ‖ : ℝ) : ℂ) ^ 2).re = ‖x‖ * ‖f ξ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h9]
  nlinarith [norm_nonneg (f ξ), norm_nonneg x]

/-- **Semifiniteness, compression form.**  Every compression of a bounded operator by a finite
partial sum has finite weight. -/
theorem globalWeight_compress_lt_top (hf : ComparisonFamily M q v) (x : H →L[ℂ] H) (N : ℕ) :
    globalWeight q Ω v (partialProj v N * x * partialProj v N) < ⊤ := by
  have hproj := partialProj_isStarProjection hf N
  have hle : globalWeight q Ω v (partialProj v N * x * partialProj v N)
      ≤ globalWeight q Ω v ((‖x‖ : ℂ) • partialProj v N) :=
    globalWeight_mono hf fun ξ =>
      reInner_compress_le hproj.isSelfAdjoint.star_eq hproj.isIdempotentElem ξ
  refine lt_of_le_of_lt hle ?_
  rw [globalWeight_smul hf (norm_nonneg x)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (globalWeight_partialProj_lt_top hf N)

/-- An operator killed by all the compressions `f_N · f_N` is zero. -/
theorem eq_zero_of_compress_eq_zero (hf : ComparisonFamily M q v) {x : H →L[ℂ] H}
    (h0 : ∀ N, partialProj v N * x * partialProj v N = 0) : x = 0 := by
  have hquad : ∀ ξ : H, ⟪x ξ, ξ⟫_ℂ = 0 := by
    intro ξ
    have hcont : Tendsto (fun N => ⟪x (partialProj v N ξ), partialProj v N ξ⟫_ℂ) atTop
        (𝓝 (⟪x ξ, ξ⟫_ℂ)) := by
      have h1 : Tendsto (fun N => partialProj v N ξ) atTop (𝓝 ξ) := hf.sum_strong ξ
      have h2 : Tendsto (fun N => x (partialProj v N ξ)) atTop (𝓝 (x ξ)) :=
        (x.continuous.tendsto _).comp h1
      exact (continuous_inner.tendsto _).comp (h2.prodMk_nhds h1)
    have hzero : ∀ N, ⟪x (partialProj v N ξ), partialProj v N ξ⟫_ℂ = 0 := by
      intro N
      have hsa : star (partialProj v N) = partialProj v N :=
        (partialProj_isStarProjection hf N).isSelfAdjoint.star_eq
      have h1 : ⟪x (partialProj v N ξ), partialProj v N ξ⟫_ℂ
          = ⟪(partialProj v N * x * partialProj v N) ξ, ξ⟫_ℂ := by
        have h2 : (partialProj v N * x * partialProj v N) ξ
            = partialProj v N (x (partialProj v N ξ)) := rfl
        rw [h2, ← inner_isSelfAdjoint (hsa : IsSelfAdjoint (partialProj v N))
          (x (partialProj v N ξ)) ξ]
      rw [h1, h0 N]
      simp
    have hA := hcont
    simp only [hzero] at hA
    exact tendsto_nhds_unique hA tendsto_const_nhds
  have hlin : (x : H →ₗ[ℂ] H) = 0 := (inner_map_self_eq_zero (x : H →ₗ[ℂ] H)).mp hquad
  exact ContinuousLinearMap.ext fun ξ => congrFun (congrArg (fun t : H →ₗ[ℂ] H => (t : H → H))
    hlin) ξ

/-- **The finite-compression certificate.**

The finite partial sums `f_N = ∑_{m<N} v m v m ^*` are projections of `M` with finite weight,
they converge strongly to `1`, every compression `f_N x f_N` has finite weight, and no nonzero
operator is annihilated by all of these compressions.

This is *not* by itself the standard definition of semifiniteness (the compressions `f_N x f_N`
need not be below `x` in the operator order); the standard positive-cone statement is
`globalWeight_semifinite_positiveCone` in §8b.  The certificate is retained because it is the
quantitative input to that theorem. -/
theorem globalWeight_finite_compressions (hf : ComparisonFamily M q v) :
    (∀ N, IsStarProjection (partialProj v N) ∧ partialProj v N ∈ M ∧
        globalWeight q Ω v (partialProj v N) < ⊤) ∧
      (∀ ξ : H, Tendsto (fun N => partialProj v N ξ) atTop (𝓝 ξ)) ∧
      (∀ x : H →L[ℂ] H, ∀ N, globalWeight q Ω v (partialProj v N * x * partialProj v N) < ⊤) ∧
      (∀ x : H →L[ℂ] H, x ≠ 0 → ∃ N,
        partialProj v N * x * partialProj v N ≠ 0 ∧
        globalWeight q Ω v (partialProj v N * x * partialProj v N) < ⊤) := by
  refine ⟨fun N => ⟨partialProj_isStarProjection hf N, partialProj_mem hf N,
      globalWeight_partialProj_lt_top hf N⟩, hf.sum_strong,
    fun x N => globalWeight_compress_lt_top hf x N, fun x hx0 => ?_⟩
  by_contra hcon
  push_neg at hcon
  refine hx0 (eq_zero_of_compress_eq_zero hf fun N => ?_)
  by_contra hN
  exact absurd (globalWeight_compress_lt_top hf x N) (by simpa using hcon N hN)

end Semifinite

/-! ## §8b  Positive square roots and standard positive-cone semifiniteness

The compression certificate of §8 is not the standard definition of semifiniteness, because a
compression `f_N x f_N` need not lie below `x` in the operator order.  This section proves the
standard statement on the positive cone: for every nonzero positive `x ∈ M` there is a nonzero
positive `y ∈ M` with `y ≤ x` and `W y < ⊤`.

The construction is the classical one.  The positive square root `a = x^{1/2}` is *proved* to
exist inside `M` using the pinned Mathlib continuous functional calculus of the C⋆-algebra
`H →L[ℂ] H` together with the bicommutant characterisation of `M`; it is not a new hypothesis.
With the finite comparison projection `p_N = ∑_{m<N} v m v m ^*` we take

`y_N = a^* p_N a = (p_N a)^* (p_N a)`,

which is positive, lies in `M`, satisfies `x - y_N = ((1 - p_N) a)^* ((1 - p_N) a) ≥ 0`, and has
finite weight because traciality turns `W (y_N)` into `W (p_N (a a^*) p_N) = W (p_N x p_N)`,
which is finite by §8. -/

section PositiveSqrt

variable {M : VonNeumannAlgebra H}

/-- **The positive square root**, defined by the pinned Mathlib continuous functional calculus
of the C⋆-algebra `H →L[ℂ] H`.  Nothing about it is assumed: its defining properties are the
theorems below. -/
noncomputable def posSqrt (x : H →L[ℂ] H) : H →L[ℂ] H := cfc Real.sqrt x

/-- The square root is self-adjoint. -/
theorem posSqrt_isSelfAdjoint (x : H →L[ℂ] H) : IsSelfAdjoint (posSqrt x) :=
  cfc_predicate _ _

theorem posSqrt_star (x : H →L[ℂ] H) : star (posSqrt x) = posSqrt x :=
  (posSqrt_isSelfAdjoint x).star_eq

/-- **The square-root identity** `x^{1/2} x^{1/2} = x` for a positive operator. -/
theorem posSqrt_mul_self {x : H →L[ℂ] H} (hx : x.IsPositive) : posSqrt x * posSqrt x = x := by
  have hx' : (0 : H →L[ℂ] H) ≤ x := (ContinuousLinearMap.nonneg_iff_isPositive x).mpr hx
  rw [posSqrt, ← cfc_mul _ _ x Real.continuous_sqrt.continuousOn
    Real.continuous_sqrt.continuousOn]
  nth_rewrite 2 [← cfc_id ℝ x]
  refine cfc_congr fun t ht => ?_
  simpa using Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hx' ht)

/-- **The square root stays in the von Neumann algebra.**  This uses only the bicommutant
property of `M` and the fact that the continuous functional calculus of `x` commutes with
everything commuting with `x`. -/
theorem posSqrt_mem {x : H →L[ℂ] H} (hx : x ∈ M) : posSqrt x ∈ M := by
  rw [posSqrt, ← VonNeumannAlgebra.commutant_commutant M, VonNeumannAlgebra.mem_commutant_iff]
  intro z hz
  rw [VonNeumannAlgebra.mem_commutant_iff] at hz
  exact ((Commute.cfc_real (hz x hx) Real.sqrt).symm : _)

/-- A nonzero positive operator has a nonzero square root. -/
theorem posSqrt_ne_zero {x : H →L[ℂ] H} (hx : x.IsPositive) (hx0 : x ≠ 0) : posSqrt x ≠ 0 := by
  intro h
  exact hx0 (by rw [← posSqrt_mul_self hx, h, mul_zero])

end PositiveSqrt

section StandardSemifinite

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- An operator killed by all the *left* compressions `p_N ·` is zero. -/
theorem eq_zero_of_partialProj_mul_eq_zero (hf : ComparisonFamily M q v) {a : H →L[ℂ] H}
    (h0 : ∀ N, partialProj v N * a = 0) : a = 0 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  have h1 : Tendsto (fun N => partialProj v N (a ξ)) atTop (𝓝 (a ξ)) := hf.sum_strong (a ξ)
  have h2 : ∀ N, partialProj v N (a ξ) = 0 := by
    intro N
    have := congrArg (fun t : H →L[ℂ] H => t ξ) (h0 N)
    simpa using this
  simp only [h2] at h1
  simpa using tendsto_nhds_unique h1 tendsto_const_nhds

/-- **The compressed positive subelement** `y_N = x^{1/2} p_N x^{1/2}`. -/
noncomputable def compressedSub (v : ℕ → H →L[ℂ] H) (N : ℕ) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  posSqrt x * partialProj v N * posSqrt x

/-- `y_N = (p_N x^{1/2})^* (p_N x^{1/2})`. -/
theorem compressedSub_eq_star_mul_self (hf : ComparisonFamily M q v) (N : ℕ)
    (x : H →L[ℂ] H) :
    compressedSub v N x
      = star (partialProj v N * posSqrt x) * (partialProj v N * posSqrt x) := by
  have hproj := partialProj_isStarProjection hf N
  rw [star_mul, posSqrt_star, hproj.isSelfAdjoint.star_eq, compressedSub]
  calc posSqrt x * partialProj v N * posSqrt x
      = posSqrt x * (partialProj v N * partialProj v N) * posSqrt x := by
        rw [hproj.isIdempotentElem]
    _ = posSqrt x * partialProj v N * (partialProj v N * posSqrt x) := by noncomm_ring

theorem compressedSub_isPositive (hf : ComparisonFamily M q v) (N : ℕ) (x : H →L[ℂ] H) :
    (compressedSub v N x).IsPositive := by
  rw [compressedSub_eq_star_mul_self hf]
  exact isPositive_star_mul_self _

theorem compressedSub_mem (hf : ComparisonFamily M q v) {x : H →L[ℂ] H} (hx : x ∈ M)
    (N : ℕ) : compressedSub v N x ∈ M :=
  mul_mem (mul_mem (posSqrt_mem hx) (partialProj_mem hf N)) (posSqrt_mem hx)

/-- **The order inequality** `y_N ≤ x`. -/
theorem compressedSub_le (hf : ComparisonFamily M q v) {x : H →L[ℂ] H} (hx : x.IsPositive)
    (N : ℕ) : compressedSub v N x ≤ x := by
  have hproj := partialProj_isStarProjection hf N
  set a := posSqrt x with ha
  set p := partialProj v N with hp
  set c := (1 - p) * a with hc
  have hstarc : star c = a * (1 - p) := by
    rw [hc, star_mul, posSqrt_star, star_sub, star_one, hproj.isSelfAdjoint.star_eq]
  have hkey : star c * c = x - compressedSub v N x := by
    rw [hstarc, hc, compressedSub, ← ha, ← hp]
    have hpp : p * p = p := hproj.isIdempotentElem
    calc a * (1 - p) * ((1 - p) * a)
        = a * a - a * p * a - (a * p * a - a * (p * p) * a) := by noncomm_ring
      _ = a * a - a * p * a := by rw [hpp]; abel
      _ = x - a * p * a := by rw [ha, posSqrt_mul_self hx]
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive, ← hkey]
  exact isPositive_star_mul_self c

/-- **The compressed subelement has finite weight.**  This is where the tracial law and the
finite compression `p_N (x^{1/2} x^{1/2}) p_N = p_N x p_N` of §8 are used. -/
theorem globalWeight_compressedSub_lt_top (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {x : H →L[ℂ] H} (hx : x ∈ M)
    (hxpos : x.IsPositive) (N : ℕ) :
    globalWeight q Ω v (compressedSub v N x) < ⊤ := by
  have hb : partialProj v N * posSqrt x ∈ M :=
    mul_mem (partialProj_mem hf N) (posSqrt_mem hx)
  have hproj := partialProj_isStarProjection hf N
  have hstar : star (partialProj v N * posSqrt x) = posSqrt x * partialProj v N := by
    rw [star_mul, posSqrt_star, hproj.isSelfAdjoint.star_eq]
  have hflip : (partialProj v N * posSqrt x) * star (partialProj v N * posSqrt x)
      = partialProj v N * x * partialProj v N := by
    rw [hstar]
    calc partialProj v N * posSqrt x * (posSqrt x * partialProj v N)
        = partialProj v N * (posSqrt x * posSqrt x) * partialProj v N := by noncomm_ring
      _ = partialProj v N * x * partialProj v N := by rw [posSqrt_mul_self hxpos]
  rw [compressedSub_eq_star_mul_self hf, globalWeight_tracial hf h hb, hflip]
  exact globalWeight_compress_lt_top hf x N

/-- For nonzero positive `x`, some compressed subelement is nonzero. -/
theorem exists_compressedSub_ne_zero (hf : ComparisonFamily M q v) {x : H →L[ℂ] H}
    (hx : x.IsPositive) (hx0 : x ≠ 0) : ∃ N, compressedSub v N x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine posSqrt_ne_zero hx hx0 (eq_zero_of_partialProj_mul_eq_zero hf fun N => ?_)
  have hzero := hcon N
  rw [compressedSub_eq_star_mul_self hf] at hzero
  refine ContinuousLinearMap.ext fun ξ => ?_
  have h1 : ‖(partialProj v N * posSqrt x) ξ‖ ^ 2 = 0 := by
    rw [← inner_star_mul_self (partialProj v N * posSqrt x) ξ, hzero]
    simp
  have h2 : ‖(partialProj v N * posSqrt x) ξ‖ = 0 := by
    have hnn := norm_nonneg ((partialProj v N * posSqrt x) ξ)
    nlinarith [h1, hnn]
  simpa using norm_eq_zero.mp h2

/-- **Standard positive-cone semifiniteness of the global weight.**

For every nonzero positive `x ∈ M` there is a nonzero positive `y ∈ M` with `y ≤ x` in the
operator order and `W y < ⊤`.  This is the standard definition of semifiniteness of an
extended-positive weight, not merely a statement about compressions. -/
theorem globalWeight_semifinite_positiveCone (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) :
    ∀ x ∈ M, x.IsPositive → x ≠ 0 → ∃ y ∈ M,
      y.IsPositive ∧ y ≠ 0 ∧ y ≤ x ∧ globalWeight q Ω v y < ⊤ := by
  intro x hx hxpos hx0
  obtain ⟨N, hN⟩ := exists_compressedSub_ne_zero (v := v) hf hxpos hx0
  exact ⟨compressedSub v N x, compressedSub_mem hf hx N, compressedSub_isPositive hf N x, hN,
    compressedSub_le hf hxpos N, globalWeight_compressedSub_lt_top hf h hx hxpos N⟩

/-- **Faithfulness on the positive cone.**  A positive element of `M` of zero weight is zero. -/
theorem globalWeight_faithful_positiveCone (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) (hqΩ : q Ω = Ω) {x : H →L[ℂ] H}
    (hx : x ∈ M) (hxpos : x.IsPositive) (h0 : globalWeight q Ω v x = 0) : x = 0 := by
  have hsq : star (posSqrt x) * posSqrt x = x := by
    rw [posSqrt_star, posSqrt_mul_self hxpos]
  have ha : posSqrt x = 0 :=
    globalWeight_faithful hf h hqΩ (posSqrt_mem hx) (by rw [hsq]; exact h0)
  rw [← posSqrt_mul_self hxpos, ha, mul_zero]

/-- **Monotonicity in the operator order** on the positive cone. -/
theorem globalWeight_mono_le (hf : ComparisonFamily M q v) {x y : H →L[ℂ] H} (hxy : x ≤ y) :
    globalWeight q Ω v x ≤ globalWeight q Ω v y := by
  have hpos : (y - x).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive (y - x)).mp (sub_nonneg.mpr hxy)
  refine globalWeight_mono hf fun ξ => ?_
  have h1 := reInner_nonneg_of_isPositive hpos ξ
  have h2 : (⟪ξ, (y - x) ξ⟫_ℂ).re = (⟪ξ, y ξ⟫_ℂ).re - (⟪ξ, x ξ⟫_ℂ).re := by
    simp
  rw [h2] at h1
  linarith

end StandardSemifinite

/-! ## §9  Where the comparison family comes from

The classical route to the hypothesis of this packet is the σ-finite comparison theorem: for a
full projection `q` of a von Neumann algebra with separable predual, `1` decomposes into a
countable orthogonal family of projections each equivalent to a subprojection of `q`.  That
comparison theorem is a genuine analytic result which pinned Mathlib does **not** provide and
which is **not** proved here.

What *is* proved here is the purely algebraic reduction: once such an orthogonal decomposition
is given, the comparison family of P60 exists.  Fullness of `q` therefore never by itself
produces a global weight anywhere in this file. -/

section Existence

/-- **From an orthogonal decomposition of `1` by projections subequivalent to `q` to a
comparison family.**

The hypotheses `he0`, `horth`, `hsum`, `hequiv` are exactly the output of the σ-finite
comparison theorem; that theorem itself is *not* proved here, so this statement is
conditional. -/
theorem exists_comparisonFamily_of_orthogonal_decomposition {M : VonNeumannAlgebra H}
    {q : H →L[ℂ] H} (hq : M.IsProjection q) (e : ℕ → H →L[ℂ] H) (he0 : e 0 = q)
    (horth : ∀ m n, m ≠ n → e m * e n = 0)
    (hsum : ∀ ξ : H, Tendsto (fun N => (∑ m ∈ Finset.range N, e m) ξ) atTop (𝓝 ξ))
    (hequiv : ∀ n, ∃ p, M.IsProjection p ∧ VonNeumannAlgebra.ProjLe p q ∧ M.MvNEquiv p (e n)) :
    ∃ v : ℕ → H →L[ℂ] H, ComparisonFamily M q v ∧ ∀ n, rngProj v n = e n := by
  classical
  choose p hpproj hple hpequiv using hequiv
  choose w hw using hpequiv
  set v : ℕ → H →L[ℂ] H := fun n => if n = 0 then q else w n with hvdef
  have hv0 : v 0 = q := by simp [hvdef]
  have hvn : ∀ n, n ≠ 0 → v n = w n := fun n hn => by simp [hvdef, hn]
  have hrng : ∀ n, rngProj v n = e n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [rngProj, hv0, hq.star_eq, hq.mul_self, he0]
    · rw [rngProj, hvn n hn]
      exact (hw n).2.2
  have hsrc : ∀ n, srcProj v n = if n = 0 then q else p n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [srcProj, hv0, hq.star_eq, hq.mul_self, if_pos rfl]
    · rw [srcProj, hvn n hn, (hw n).2.1, if_neg hn]
  refine ⟨v, ?_, hrng⟩
  refine
    { mem := ?_, idem_src := ?_, src_le := ?_, orthogonal := ?_, sum_strong := ?_,
      src_zero := ?_, rng_zero := ?_ }
  · intro n
    by_cases hn : n = 0
    · rw [hn, hv0]; exact hq.2
    · rw [hvn n hn]; exact (hw n).1
  · intro n
    rw [hsrc n]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact hq.mul_self
    · rw [if_neg hn]; exact (hpproj n).mul_self
  · intro n
    rw [hsrc n]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact ⟨hq.mul_self, hq.mul_self⟩
    · rw [if_neg hn]; exact hple n
  · intro m n hmn
    rw [hrng m, hrng n]
    exact horth m n hmn
  · intro ξ
    have h1 : ∀ N, partialProj v N = ∑ m ∈ Finset.range N, e m := by
      intro N
      rw [partialProj]
      exact Finset.sum_congr rfl fun m _ => hrng m
    simpa [h1] using hsum ξ
  · rw [hsrc 0, if_pos rfl]
  · rw [hrng 0, he0]

/-- **Non-vacuity of the comparison premises.**  The unit projection of any concrete von
Neumann algebra carries a normalized countable comparison family, namely the one whose zeroth
member is `1` and whose remaining members vanish.  This is a consistency check on the
structure `ComparisonFamily`; it carries no manuscript content. -/
theorem comparisonFamily_one (M : VonNeumannAlgebra H) :
    ComparisonFamily M 1 (fun n => if n = 0 then (1 : H →L[ℂ] H) else 0) := by
  classical
  set v : ℕ → H →L[ℂ] H := fun n => if n = 0 then (1 : H →L[ℂ] H) else 0 with hvdef
  have hrng : ∀ n, rngProj v n = if n = 0 then (1 : H →L[ℂ] H) else 0 := by
    intro n
    by_cases hn : n = 0 <;> simp [rngProj, hvdef, hn]
  have hsrc : ∀ n, srcProj v n = if n = 0 then (1 : H →L[ℂ] H) else 0 := by
    intro n
    by_cases hn : n = 0 <;> simp [srcProj, hvdef, hn]
  refine
    { mem := ?_, idem_src := ?_, src_le := ?_, orthogonal := ?_, sum_strong := ?_,
      src_zero := ?_, rng_zero := ?_ }
  · intro n
    by_cases hn : n = 0
    · simp only [hvdef, if_pos hn]; exact one_mem M
    · simp only [hvdef, if_neg hn]; exact zero_mem M
  · intro n
    rw [hsrc n]
    by_cases hn : n = 0 <;> simp [hn, IsIdempotentElem]
  · intro n
    rw [hsrc n]
    by_cases hn : n = 0 <;> simp [hn, VonNeumannAlgebra.ProjLe]
  · intro m n hmn
    rw [hrng m, hrng n]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have hn : n ≠ 0 := by omega
      simp [hn]
    · have hm' : m ≠ 0 := by omega
      simp [hm']
  · intro ξ
    have h1 : ∀ N, 1 ≤ N → partialProj v N ξ = ξ := by
      intro N hN
      have h2 : partialProj v N = ∑ m ∈ Finset.range N, (if m = 0 then (1 : H →L[ℂ] H) else 0) :=
        Finset.sum_congr rfl fun m _ => hrng m
      rw [h2, Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => (1 : H →L[ℂ] H))]
      simp [Finset.mem_range, Nat.lt_of_lt_of_le Nat.zero_lt_one hN]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (h1 N hN).symm
  · rw [hsrc 0, if_pos rfl]
  · rw [hrng 0, if_pos rfl]

/-- **Non-vacuity of the weight construction.**  For the unit comparison family of
`comparisonFamily_one` the global weight is the vector state at `Ω`, which is neither
identically zero nor identically infinite. -/
theorem globalWeight_one_family (Ω : H) (x : H →L[ℂ] H) :
    globalWeight 1 Ω (fun n => if n = 0 then (1 : H →L[ℂ] H) else 0) x
      = ENNReal.ofReal ((⟪Ω, x Ω⟫_ℂ).re) := by
  classical
  rw [globalWeight_def]
  refine tsum_eq_single 0 ?_ |>.trans ?_
  · intro m hm
    simp [weightTerm, hm]
  · simp [weightTerm, cornerTau_apply]

end Existence

/-! ## §10  The exported P60R theorem -/

section Export

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H} {v : ℕ → H →L[ℂ] H}

/-- **The public domain of the weight**: the positive cone of `M`.

The extended weight is `ℝ≥0∞`-valued and is *not* presented as a linear functional on
arbitrary operators; all of its laws below are stated for elements of this cone. -/
def positiveCone (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ x.IsPositive}

theorem mem_positiveCone_iff {M : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ positiveCone M ↔ x ∈ M ∧ x.IsPositive := Iff.rfl

/-- **The weight laws proved in this file**, bundled as a single predicate on the positive
cone `positiveCone M`.  It is a *conclusion*, never a hypothesis: no theorem of this file
assumes it. -/
structure IsGlobalFaithfulNormalSemifiniteTrace (M : VonNeumannAlgebra H) (q : H →L[ℂ] H)
    (Ω : H) (v : ℕ → H →L[ℂ] H) : Prop where
  /-- Additivity on the positive cone. -/
  additive : ∀ x ∈ positiveCone M, ∀ y ∈ positiveCone M,
    globalWeight q Ω v (x + y) = globalWeight q Ω v x + globalWeight q Ω v y
  /-- Positive homogeneity on the positive cone. -/
  homogeneous : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ positiveCone M,
    globalWeight q Ω v ((c : ℂ) • x) = ENNReal.ofReal c * globalWeight q Ω v x
  /-- Monotonicity for the operator order on the positive cone. -/
  monotone : ∀ x ∈ positiveCone M, ∀ y ∈ positiveCone M, x ≤ y →
    globalWeight q Ω v x ≤ globalWeight q Ω v y
  /-- Traciality: `W (a^* a) = W (a a^*)` for `a ∈ M`.  Both arguments are positive. -/
  tracial : ∀ a ∈ M, globalWeight q Ω v (star a * a) = globalWeight q Ω v (a * star a)
  /-- Faithfulness on the positive cone. -/
  faithful : ∀ x ∈ positiveCone M, globalWeight q Ω v x = 0 → x = 0
  /-- Normality: the monotone-supremum law for increasing ultraweakly convergent sequences
  in the positive cone. -/
  normal : ∀ (x : ℕ → H →L[ℂ] H), (∀ k, x k ∈ positiveCone M) → ∀ y ∈ positiveCone M,
    (∀ k, ∀ ξ : H, (⟪ξ, x k ξ⟫_ℂ).re ≤ (⟪ξ, x (k + 1) ξ⟫_ℂ).re) →
    Tendsto (fun k => toUltraweak (x k)) atTop (𝓝 (toUltraweak y)) →
    (⨆ k, globalWeight q Ω v (x k)) = globalWeight q Ω v y
  /-- The weight restricts to the P50U corner trace on `q M q`. -/
  corner : ∀ x ∈ M, q * x = x → x * q = x →
    globalWeight q Ω v x = ENNReal.ofReal ((cornerTau q Ω x).re)
  /-- The value on the finite partial sums of the comparison family. -/
  partialProj_value : ∀ N : ℕ, globalWeight q Ω v (partialProj v N)
    = ∑ m ∈ Finset.range N, ENNReal.ofReal ((cornerTau q Ω (srcProj v m)).re)
  /-- **Standard semifiniteness on the positive cone**: every nonzero positive element of `M`
  dominates a nonzero positive element of `M` of finite weight. -/
  semifinite : ∀ x ∈ positiveCone M, x ≠ 0 → ∃ y ∈ positiveCone M,
    y ≠ 0 ∧ y ≤ x ∧ globalWeight q Ω v y < ⊤
  /-- The retained finite-compression certificate of §8: the finite partial sums are
  projections of `M` of finite weight converging strongly to `1`, all of whose compressions
  have finite weight and separate nonzero operators. -/
  finite_compressions : (∀ N, IsStarProjection (partialProj v N) ∧ partialProj v N ∈ M ∧
      globalWeight q Ω v (partialProj v N) < ⊤) ∧
    (∀ ξ : H, Tendsto (fun N => partialProj v N ξ) atTop (𝓝 ξ)) ∧
    (∀ x : H →L[ℂ] H, ∀ N,
      globalWeight q Ω v (partialProj v N * x * partialProj v N) < ⊤) ∧
    (∀ x : H →L[ℂ] H, x ≠ 0 → ∃ N,
      partialProj v N * x * partialProj v N ≠ 0 ∧
      globalWeight q Ω v (partialProj v N * x * partialProj v N) < ⊤)

/-- **Exported P60R theorem: the global faithful normal semifinite weight on the positive
cone.**

Input data:

* `hf`, a normalized countable comparison family for `q` in `M` (the explicit optional
  assumption of this packet: partial isometries of `M` with source projections below `q`,
  pairwise orthogonal range projections whose partial sums converge strongly to `1`, and
  `v 0` with source and range projection `q`);
* `h`, P50U's literally ultraweak-normal faithful tracial corner state on `q M q`; and
* `hqΩ`, the corner normalization `q Ω = Ω`.

Conclusion: on the positive cone of `M`, `globalWeight q Ω v` is additive, positively
homogeneous, monotone, tracial, faithful, normal in the monotone-supremum sense, restricts to
the P50U corner trace on `q M q`, and is **semifinite in the standard sense**: every nonzero
positive element of `M` dominates a nonzero positive element of `M` of finite weight.

No weight law is assumed; each one is the corresponding theorem proved above. -/
theorem full_corner_global_semifinite_weight (hf : ComparisonFamily M q v)
    (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) (hqΩ : q Ω = Ω) :
    IsGlobalFaithfulNormalSemifiniteTrace M q Ω v where
  additive := fun _ hx _ hy => globalWeight_add hf hx.2 hy.2
  homogeneous := fun c hc x _ => globalWeight_smul hf hc x
  monotone := fun _ _ _ _ hxy => globalWeight_mono_le hf hxy
  tracial := fun a ha => globalWeight_tracial hf h ha
  faithful := fun _ hx h0 => globalWeight_faithful_positiveCone hf h hqΩ hx.1 hx.2 h0
  normal := fun _ _ _ _ hmono hconv =>
    globalWeight_iSup_of_ultraweakTendsto hf h hmono hconv
  corner := fun x hx hqx hxq => globalWeight_corner hf h hx hqx hxq
  partialProj_value := fun N => globalWeight_partialProj hf N
  semifinite := fun x hx hx0 => by
    obtain ⟨y, hyM, hypos, hy0, hyle, hylt⟩ :=
      globalWeight_semifinite_positiveCone hf h x hx.1 hx.2 hx0
    exact ⟨y, ⟨hyM, hypos⟩, hy0, hyle, hylt⟩
  finite_compressions := globalWeight_finite_compressions hf

end Export

/-! ## §11  The P51 full finite corner, globalized

This is the packet's optional strengthening in the form that uses P51 and P50U directly: the
input is the P51/P50U data (the compatible finite-codespace system, its decreasing projection
tower, the represented regional C⋆-algebra, the commuting complement and the dense-vector
premise) *together with* an explicitly supplied comparison family for the strong-limit
projection `q`.  The conclusion records P51's finiteness and fullness of `q` alongside the new
global weight laws.

The comparison family is a hypothesis, never a consequence of fullness: nothing here claims
that P51 already supplied a global weight. -/

section P51Globalization

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **Optional Lane-G strengthening.**  Under the P51/P50U hypotheses together with a
normalized countable comparison family `v` for the strong-limit projection `q`, the projection
`q` is a full finite projection of `M = A''` (P51) and `globalWeight q Ω v` is a faithful,
normal (monotone-supremum law), tracial extended-positive weight on the positive cone of `M`,
semifinite in the standard sense (every nonzero positive element of `M` dominates a nonzero
positive element of finite weight), restricting to the P50U corner trace on `q M q`. -/
theorem full_finite_corner_globalized_weight {Ω : H}
    (D : CompatibleFiniteCodespaceSystem Ω ι)
    (hp : IsDecreasingProjTower D.toFiniteCodespaceSystem.stageProj)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hlocal : ∀ n, Set.range (D.pi n) ⊆ (A : Set (H →L[ℂ] H)))
    (hAdense : (A : Set (H →L[ℂ] H)) ⊆ closure (⋃ n, Set.range (D.pi n)))
    (B : Set (H →L[ℂ] H)) (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H))
    (v : ℕ → H →L[ℂ] H)
    (hf : ComparisonFamily (StarSubalgebra.vonNeumannGenerated A)
      (limitProj D.toFiniteCodespaceSystem.stageProj) v) :
    (StarSubalgebra.vonNeumannGenerated A).IsFiniteProjection
        (limitProj D.toFiniteCodespaceSystem.stageProj) ∧
      (StarSubalgebra.vonNeumannGenerated A).IsFull
        (limitProj D.toFiniteCodespaceSystem.stageProj) ∧
      IsGlobalFaithfulNormalSemifiniteTrace (StarSubalgebra.vonNeumannGenerated A)
        (limitProj D.toFiniteCodespaceSystem.stageProj) Ω v := by
  obtain ⟨hfin, hfull, -⟩ :=
    FullFiniteCornerCentralExclusion.full_finite_corner_central_exclusion D hp A hAclosed
      hlocal hAdense B hB hdense
  have hcorner := ultraweak_normal_faithful_corner_trace D hp A hAclosed hlocal hAdense B hB
    hdense
  have hqΩ : limitProj D.toFiniteCodespaceSystem.stageProj Ω = Ω :=
    limitProj_apply_self fun n => D.toFiniteCodespaceSystem.stageProj_apply_self n
  exact ⟨hfin, hfull, full_corner_global_semifinite_weight hf hcorner hqΩ⟩

end P51Globalization

end FullCornerSemifiniteWeight
end AristotleCandidates
