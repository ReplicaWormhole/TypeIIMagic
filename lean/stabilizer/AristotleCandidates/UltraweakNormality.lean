import Mathlib
import AristotleCandidates.NormalFaithfulCornerTrace

/-!
# P50U — the ultraweak topology and the normality bridge

**Infrastructure only.**  This file formalizes no manuscript claim.  It develops
the concrete ultraweak (σ-weak) topology on the bounded operators of a complex
Hilbert space `H`, together with the interface needed to state *normality* of a
functional in its standard form, and it upgrades the P50 corner theorem
accordingly.

**Plan alignment.**  Package `P50U`, lane `shared`.  Predecessor: `P50`
(`AristotleCandidates.NormalFaithfulCornerTrace`), whose theorem
`cornerTau_continuous_wot` is the input certificate that is upgraded here.
The gate discharged is exactly the replacement of the informal implication
"WOT-continuous, therefore ultraweakly continuous and normal" by a checked
topology comparison.

**Forbidden downstream claims, none of which appear here.**  No traciality or
faithfulness argument beyond the one already proved in P50, no projection
finiteness or fullness, no central type-III exclusion, no global trace or
weight, and no Lane-H tensor-factor or factor-classification statement.

## Contents

* `UltraweakCoeff H` — the data of two sequences `x : ℕ → H`,
  `y : ℕ → (H →L[ℂ] ℂ)` with `Summable (fun n => ‖x n‖ * ‖y n‖)`; i.e. an
  absolutely summable series of matrix coefficients.
* `UltraweakCoeff.summable_apply`, `UltraweakCoeff.eval` — the associated series
  `T ↦ ∑' n, y n (T (x n))` is absolutely convergent for every bounded operator
  `T`, and `eval` is its (linear) sum.
* `UltraweakCoeff.single`, `UltraweakCoeff.scalarSeries` — the one-term coefficient datum
  realizing a WOT generator, and a genuinely infinite absolutely summable coefficient datum.
* `UltraweakCLM H` — the type copy of `H →L[ℂ] H` carrying the **ultraweak
  topology**, defined as the topology induced by the map
  `T ↦ (fun c : UltraweakCoeff H => c.eval T)` into the product `ℂ`-topology.
  This is by construction the coarsest topology making *all* absolutely
  summable matrix-coefficient series continuous; it is not an alias for WOT,
  SOT or the norm topology.
* `toUltraweak`, `UltraweakCLM.toCLM`, `ultraweakEquiv` — conversion between an
  operator and its ultraweak copy, which does not change the operator.
* `UltraweakCLM.continuous_eval` — every coefficient functional is continuous
  by construction.
* `UltraweakCLM.continuous_toWOT` — **the topology comparison**: the identity
  map from the ultraweak topology to the weak operator topology is continuous.
  Proved by realizing each WOT generator `T ↦ y (T x)` as the one-term
  ultraweak coefficient series `UltraweakCoeff.single x y`.
* `IsUltraweaklyContinuous` — the predicate on complex-linear functionals on
  `B(H)`, and `IsUltraweaklyContinuous.of_wot` deriving it from WOT continuity.
* `cornerTau_ultraweakContinuous` — P50's compressed vector functional is
  ultraweakly continuous.
* `IsFaithfulUltraweakNormalTracialCorner` and
  `ultraweak_normal_faithful_corner_trace` — the exported upgrade of P50's
  `normal_faithful_corner_trace`, whose normality field is *literally*
  ultraweak continuity, under exactly the same hypotheses.
-/

universe u v

open Filter Topology

namespace AristotleCandidates
namespace UltraweakNormality

open FiniteCornerTrace ProjectionTower NormalFaithfulCornerTrace
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## §1  Absolutely summable matrix-coefficient series -/

/-- The data defining an ultraweak coefficient functional: a sequence of vectors `x n : H`
and a sequence of continuous linear functionals `y n : H →L[ℂ] ℂ` whose norms are absolutely
summable against each other. -/
structure UltraweakCoeff (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vectors at which the operator is evaluated. -/
  x : ℕ → H
  /-- The functionals applied to the resulting vectors. -/
  y : ℕ → (H →L[ℂ] ℂ)
  /-- Absolute summability of the coefficient data. -/
  summable_norm : Summable fun n => ‖x n‖ * ‖y n‖

namespace UltraweakCoeff

variable (c : UltraweakCoeff H) (T : H →L[ℂ] H)

/-- The matrix-coefficient series of an ultraweak coefficient datum converges absolutely for
every bounded operator. -/
theorem summable_apply : Summable fun n => c.y n (T (c.x n)) := by
  refine Summable.of_norm_bounded (g := fun n => ‖T‖ * (‖c.x n‖ * ‖c.y n‖))
    (c.summable_norm.mul_left ‖T‖) fun n => ?_
  calc ‖c.y n (T (c.x n))‖ ≤ ‖c.y n‖ * ‖T (c.x n)‖ := (c.y n).le_opNorm _
    _ ≤ ‖c.y n‖ * (‖T‖ * ‖c.x n‖) := by
        gcongr
        exact T.le_opNorm _
    _ = ‖T‖ * (‖c.x n‖ * ‖c.y n‖) := by ring

/-- The value of an ultraweak coefficient functional at a bounded operator:
`T ↦ ∑' n, y n (T (x n))`. -/
noncomputable def eval : ℂ := ∑' n, c.y n (T (c.x n))

theorem eval_def : c.eval T = ∑' n, c.y n (T (c.x n)) := rfl

@[simp] theorem eval_zero : c.eval 0 = 0 := by simp [eval]

theorem eval_add (S T : H →L[ℂ] H) : c.eval (S + T) = c.eval S + c.eval T := by
  simp only [eval]
  rw [← Summable.tsum_add (c.summable_apply S) (c.summable_apply T)]
  simp

theorem eval_smul (a : ℂ) (T : H →L[ℂ] H) : c.eval (a • T) = a * c.eval T := by
  simp only [eval, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [← tsum_mul_left]

/-- The one-term coefficient datum realizing the weak-operator generator `T ↦ y (T x)`. -/
noncomputable def single (x : H) (y : H →L[ℂ] ℂ) : UltraweakCoeff H where
  x := fun n => if n = 0 then x else 0
  y := fun n => if n = 0 then y else 0
  summable_norm := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [hn]

@[simp] theorem eval_single (x : H) (y : H →L[ℂ] ℂ) (T : H →L[ℂ] H) :
    (single x y).eval T = y (T x) := by
  rw [eval_def]
  refine tsum_eq_single 0 ?_ |>.trans ?_
  · intro n hn
    simp [single, hn]
  · simp [single]

/-! ### A genuinely infinite coefficient series

The next construction shows that the definition really does range over infinite absolutely
summable series of matrix coefficients, not only over the finitely supported ones which already
generate WOT. -/

/-- An absolutely summable coefficient datum built from a summable sequence of scalars; all of
its terms are nonzero as soon as `v ≠ 0` and every `a n ≠ 0`. -/
noncomputable def scalarSeries (v : H) {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    UltraweakCoeff H where
  x := fun n => a n • v
  y := fun _ => innerSL ℂ v
  summable_norm := by
    have h := ha.mul_right (‖v‖ * ‖(innerSL ℂ v : H →L[ℂ] ℂ)‖)
    refine h.congr fun n => ?_
    rw [norm_smul]
    ring

@[simp] theorem eval_scalarSeries (v : H) {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (T : H →L[ℂ] H) :
    (scalarSeries v ha).eval T = (∑' n, a n) * ⟪v, T v⟫_ℂ := by
  rw [eval_def]
  have hterm : ∀ n, ((scalarSeries v ha).y n) (T ((scalarSeries v ha).x n))
      = a n * ⟪v, T v⟫_ℂ := by
    intro n
    simp [scalarSeries]
  simp_rw [hterm]
  rw [tsum_mul_right]

end UltraweakCoeff

/-! ## §2  The ultraweak topology as a type copy of `B(H)` -/

/-- The type copy of `H →L[ℂ] H` which carries the **ultraweak topology**. -/
structure UltraweakCLM (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying bounded operator; the copy does not change it. -/
  toCLM : H →L[ℂ] H

namespace UltraweakCLM

/-- The ultraweak copy of a bounded operator. -/
def _root_.AristotleCandidates.UltraweakNormality.toUltraweak (T : H →L[ℂ] H) : UltraweakCLM H :=
  ⟨T⟩

@[simp] theorem toCLM_toUltraweak (T : H →L[ℂ] H) : (toUltraweak T).toCLM = T := rfl

@[simp] theorem toUltraweak_toCLM (T : UltraweakCLM H) : toUltraweak T.toCLM = T := rfl

theorem toCLM_injective : Function.Injective (toCLM : UltraweakCLM H → H →L[ℂ] H) := by
  rintro ⟨S⟩ ⟨T⟩ h
  simpa using h

/-- Passing to the ultraweak copy is a bijection which does not change the underlying
operator. -/
def _root_.AristotleCandidates.UltraweakNormality.ultraweakEquiv :
    (H →L[ℂ] H) ≃ UltraweakCLM H where
  toFun := toUltraweak
  invFun := toCLM
  left_inv _ := rfl
  right_inv _ := rfl

/-- The map inducing the ultraweak topology: an operator is sent to the family of *all* of its
absolutely summable matrix-coefficient series. -/
noncomputable def inducingFn (T : UltraweakCLM H) : UltraweakCoeff H → ℂ :=
  fun c => c.eval T.toCLM

@[simp] theorem inducingFn_apply (T : UltraweakCLM H) (c : UltraweakCoeff H) :
    inducingFn T c = c.eval T.toCLM := rfl

/-- **The ultraweak topology.**  It is the coarsest topology on `B(H)` making every functional
`T ↦ ∑' n, y n (T (x n))`, for `Summable (fun n => ‖x n‖ * ‖y n‖)`, continuous. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (UltraweakCLM H) :=
  .induced inducingFn Pi.topologicalSpace

theorem continuous_inducingFn : Continuous (inducingFn : UltraweakCLM H → _) :=
  continuous_induced_dom

/-- Every absolutely summable matrix-coefficient series is ultraweakly continuous, by
construction of the topology. -/
theorem continuous_eval (c : UltraweakCoeff H) :
    Continuous fun T : UltraweakCLM H => c.eval T.toCLM :=
  (continuous_pi_iff.mp continuous_inducingFn) c

/-- A map into the ultraweak copy is continuous as soon as all coefficient series are. -/
theorem continuous_of_forall_eval {α : Type v} [TopologicalSpace α] {g : α → UltraweakCLM H}
    (h : ∀ c : UltraweakCoeff H, Continuous fun a => c.eval (g a).toCLM) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/-- The identity map from the ultraweak copy to the weak-operator copy. -/
noncomputable def toWOT (T : UltraweakCLM H) : H →WOT[ℂ] H :=
  ContinuousLinearMap.toWOT (RingHom.id ℂ) H H T.toCLM

@[simp] theorem toWOT_apply (T : UltraweakCLM H) (x : H) : toWOT T x = T.toCLM x := rfl

@[simp] theorem toWOT_symm (T : UltraweakCLM H) :
    (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).symm (toWOT T) = T.toCLM := rfl

/-- **Topology comparison.**  The identity map from the ultraweak topology to the weak operator
topology is continuous: the ultraweak topology is finer than WOT.

The proof realizes each WOT generator `T ↦ y (T x)` as the one-term ultraweak coefficient
series `UltraweakCoeff.single x y`. -/
theorem continuous_toWOT : Continuous (toWOT : UltraweakCLM H → H →WOT[ℂ] H) := by
  refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
  intro x y
  have h := continuous_eval (UltraweakCoeff.single x y)
  simpa using h

end UltraweakCLM

/-! ## §3  Ultraweak continuity of functionals, and normality -/

/-- **Normality in its standard form.**  A complex-linear functional on `B(H)` is *ultraweakly
continuous* (equivalently, normal) when it is continuous for the ultraweak topology, i.e. when
the induced function on the ultraweak type copy is continuous. -/
def IsUltraweaklyContinuous (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  Continuous fun T : UltraweakCLM H => φ T.toCLM

namespace IsUltraweaklyContinuous

/-- **The normality bridge.**  A WOT-continuous linear functional is ultraweakly continuous.

The topology direction is represented in the Lean term: the statement composes the assumed
WOT-continuous function with `UltraweakCLM.continuous_toWOT`, the checked continuity of the
identity map from the ultraweak topology to WOT. -/
theorem of_wot {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (h : Continuous fun T : H →WOT[ℂ] H =>
      φ ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).symm T)) :
    IsUltraweaklyContinuous φ :=
  h.comp UltraweakCLM.continuous_toWOT

end IsUltraweaklyContinuous

/-! ## §4  The P50 corner functional is ultraweakly continuous -/

variable [CompleteSpace H]

/-- **P50's compressed vector functional is ultraweakly continuous.**  This upgrades
`NormalFaithfulCornerTrace.cornerTau_continuous_wot` through the checked topology comparison
`UltraweakCLM.continuous_toWOT`. -/
theorem cornerTau_ultraweakContinuous (q : H →L[ℂ] H) (Ω : H) :
    IsUltraweaklyContinuous (cornerTau q Ω).toLinearMap :=
  IsUltraweaklyContinuous.of_wot (φ := (cornerTau q Ω).toLinearMap)
    (cornerTau_continuous_wot q Ω)

/-! ## §5  The exported ultraweak-normal corner state -/

/-- **The ultraweak-normal upgrade of P50's conclusion.**  All fields except `normal_ultraweak`
are those of `NormalFaithfulCornerTrace.IsFaithfulNormalTracialCorner`; the normality field is
here *literally* ultraweak continuity of the corner functional, i.e. normality in its standard
operator-algebraic sense. -/
structure IsFaithfulUltraweakNormalTracialCorner (M : VonNeumannAlgebra H) (q : H →L[ℂ] H)
    (Ω : H) : Prop where
  /-- `q` is a self-adjoint idempotent. -/
  isStarProjection : IsStarProjection q
  /-- `q` belongs to `M`, so that `q M q` is a von Neumann algebra on `q H`. -/
  mem : q ∈ M
  /-- Normalization: `tau_q(1) = 1`. -/
  unital : cornerTau q Ω 1 = 1
  /-- Positivity of `tau_q`. -/
  positive : ∀ x : H →L[ℂ] H, 0 ≤ (cornerTau q Ω (star x * x)).re
  /-- Traciality on the compressions of `M`, i.e. on `q M q`. -/
  tracial : CornerTracialOn q Ω (M : Set (H →L[ℂ] H))
  /-- **Normality**: ultraweak continuity of `tau_q`. -/
  normal_ultraweak : IsUltraweaklyContinuous (cornerTau q Ω).toLinearMap
  /-- Faithfulness on the corner. -/
  faithful : ∀ x ∈ M, q * x = x → x * q = x → cornerTau q Ω (star x * x) = 0 → x = 0

namespace IsFaithfulUltraweakNormalTracialCorner

variable {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {Ω : H}

/-- Every P50 conclusion upgrades to the ultraweak-normal one; the WOT-continuity certificate
of P50 is *stronger*, and is here converted through the checked topology comparison. -/
theorem of_isFaithfulNormalTracialCorner (h : IsFaithfulNormalTracialCorner M q Ω) :
    IsFaithfulUltraweakNormalTracialCorner M q Ω where
  isStarProjection := h.isStarProjection
  mem := h.mem
  unital := h.unital
  positive := h.positive
  tracial := h.tracial
  normal_ultraweak := cornerTau_ultraweakContinuous q Ω
  faithful := h.faithful

/-- Traciality read on the corner algebra `q M q`. -/
theorem tracial_corner (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {x y : H →L[ℂ] H}
    (hx : x ∈ M.corner h.isStarProjection.isSelfAdjoint)
    (hy : y ∈ M.corner h.isStarProjection.isSelfAdjoint) :
    tauVec Ω (x * y) = tauVec Ω (y * x) := by
  have hcx : q * x * q = x := compress_eq_self hx.2.1 hx.2.2
  have hcy : q * y * q = y := compress_eq_self hy.2.1 hy.2.2
  have hkey := h.tracial x hx.1 y hy.1
  rwa [hcx, hcy] at hkey

/-- Faithfulness read on the corner algebra `q M q`. -/
theorem faithful_corner (h : IsFaithfulUltraweakNormalTracialCorner M q Ω) {x : H →L[ℂ] H}
    (hx : x ∈ M.corner h.isStarProjection.isSelfAdjoint)
    (h0 : cornerTau q Ω (star x * x) = 0) : x = 0 :=
  h.faithful x hx.1 hx.2.1 hx.2.2 h0

end IsFaithfulUltraweakNormalTracialCorner

section Export

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **Exported P50U theorem.**  Under exactly the hypotheses of P50's
`normal_faithful_corner_trace` — the compatible finite-codespace system `D`, its decreasing
projection tower, the norm-closed represented C⋆-algebra `A` squeezed between the finite stages
and their closure, the commuting complement `B` and the dense-vector premise — the compressed
vector functional `tau_q` is a faithful, **ultraweakly normal**, finite tracial state on the
corner `q M q` of `M = A''`.

No ultraweak-continuity or normality hypothesis is assumed: normality is obtained from P50's
WOT-continuity certificate through the checked topology comparison
`UltraweakCLM.continuous_toWOT`. -/
theorem ultraweak_normal_faithful_corner_trace {Ω : H}
    (D : CompatibleFiniteCodespaceSystem Ω ι)
    (hp : IsDecreasingProjTower D.toFiniteCodespaceSystem.stageProj)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hlocal : ∀ n, Set.range (D.pi n) ⊆ (A : Set (H →L[ℂ] H)))
    (hAdense : (A : Set (H →L[ℂ] H)) ⊆ closure (⋃ n, Set.range (D.pi n)))
    (B : Set (H →L[ℂ] H)) (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H)) :
    IsFaithfulUltraweakNormalTracialCorner (StarSubalgebra.vonNeumannGenerated A)
      (limitProj D.toFiniteCodespaceSystem.stageProj) Ω :=
  IsFaithfulUltraweakNormalTracialCorner.of_isFaithfulNormalTracialCorner
    (normal_faithful_corner_trace D hp A hAclosed hlocal hAdense B hB hdense)

end Export

end UltraweakNormality
end AristotleCandidates
