import Mathlib
import AristotleCandidates.CenterFiniteProjectionCore
import AristotleCandidates.NormalFaithfulCornerTrace

/-!
# P51 — finiteness and fullness of `q`, and exclusion of type-III central summands

**Source basis:** `main.tex:1418-1539` (Corollary `cor:q_finite`,
Lemma `lem:finite_corner_finite_global`,
Proposition `prop:fullness`, Theorem `thm:finite_projections_exist`).

**Plan alignment.**  Package `P51`, lane `G`.  Predecessors used: `P47`
(`AristotleCandidates.CenterFiniteProjectionCore`) for the algebraic comparison
vocabulary — projections, `ProjLe`, Murray–von Neumann equivalence, finiteness,
corners, central support and fullness — and `P50`
(`AristotleCandidates.NormalFaithfulCornerTrace`) for the faithful normal
tracial state `tau_q` on the von Neumann corner `q M_Γ q`.  Through those,
`P48`, `P49`, `P49A`, `P49B` and `P49C` are used transitively.

The gate discharged here is exactly the manuscript's

* Corollary `cor:q_finite` and Lemma `lem:finite_corner_finite_global`
  (`main.tex:1422-1450`): a faithful
  tracial functional on `q M q` forces `q` to be a **finite projection of `M`**;
* Proposition `prop:fullness` (`main.tex:1473-1499`): `q` is **full** in `M_Γ`;
* Theorem `thm:finite_projections_exist` (`main.tex:1501-1539`): for every
  nonzero central projection `z`, the operator `zq` is a **nonzero finite
  projection lying in the central summand `z M_Γ`**, so that summand is not
  type III.

**Forbidden downstream claims, not made anywhere in this file.**  No direct
integral, no trivial-center claim, no global faithful normal semifinite weight
or trace on `M_Γ`, and no Lane-H tensor factorization.

## The exact theorem containing the nonzero finite projection `zq`

`AristotleCandidates.FullFiniteCornerCentralExclusion.central_summand_nonzero_finite_projection`
is the theorem whose conclusion contains the nonzero finite projection `z * q`:
it asserts simultaneously `z * q ≠ 0`, `M.IsFiniteProjection (z * q)` (finiteness
relative to all of `M`), `z * q ∈ centralSummand M z`, and
`IsFiniteProjectionIn (centralSummand M z) (z * q)` (finiteness relative to the
summand itself).  Its packaged corollary
`not_isTypeIIILike_centralSummand` states the type-III obstruction
`¬ IsTypeIIILike (centralSummand M z)`, and
`full_finite_corner_central_exclusion` is the exported form taking the P50 input
data.

## Auxiliary assumptions

Beyond the P50 data, exactly two premises are used, both already appearing in
P50 and both manuscript clauses:

* `hB : B ⊆ Set.centralizer A` — the represented complementary algebra
  `pi_omega(A_{Γᶜ})` commutes with `A = pi_omega(A_Γ)` (`main.tex`
  eq. `eq:M-commutes-complement`); and
* `hdense` — the vectors `pi_omega(b) pi_omega(a) Ω` span a dense subspace
  (`main.tex` eq. `eq:dense_states`).

No global trace or weight is assumed or manufactured; the only tracial datum is
the P50 corner state `tau_q`.

## Relative finiteness

Mathlib's `VonNeumannAlgebra H` is a *unital* algebra of operators on all of `H`,
so the reduced algebra `z M` (which is unital only on `z H`) is treated here as a
**set** of operators, `centralSummand M z`, with the set-relative comparison
predicates `MvNEquivIn`, `IsFiniteProjectionIn` and the type-III obstruction
`IsTypeIIILike`.  `isFiniteProjectionIn_of_isFiniteProjection` is the general
monotonicity statement corresponding to the manuscript's last step ("`zq` is
finite with respect to `z M_Γ`"): finiteness with respect to a larger set of
partial isometries is the stronger property.
-/

universe u

namespace AristotleCandidates
namespace FullFiniteCornerCentralExclusion

open Filter Topology
open FiniteCornerTrace ProjectionTower NormalFaithfulCornerTrace
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §1  A faithful tracial corner state makes `q` a finite projection

This is `main.tex` Lemma `lem:finite_corner_finite_global`: the manuscript's proof of
finiteness of `q` uses only that `tau_q` is a faithful tracial functional on `q M q`.
-/

section Finiteness

/-- A partial isometry implementing `q ~ r` with `r ≤ q` lies in the corner `q M q`. -/
theorem mem_corner_of_mvNEquiv_projLe {M : VonNeumannAlgebra H} {q r v : H →L[ℂ] H}
    (hqsa : IsSelfAdjoint q) (hqidem : IsIdempotentElem q) (hridem : IsIdempotentElem r)
    (hv : v ∈ M) (hv1 : star v * v = q) (hv2 : v * star v = r)
    (hrq : VonNeumannAlgebra.ProjLe r q) :
    v ∈ M.corner hqsa ∧ star v ∈ M.corner hqsa := by
  have hvq : v * q = v := by
    have := VonNeumannAlgebra.mul_star_mul_self_eq_self (v := v) (by rw [hv1]; exact hqidem)
    rwa [hv1] at this
  have hrv : r * v = v := by
    have := VonNeumannAlgebra.star_mul_self_mul_eq_self (v := v) (by rw [hv2]; exact hridem)
    rwa [hv2] at this
  have hqv : q * v = v := by
    calc q * v = q * (r * v) := by rw [hrv]
      _ = (q * r) * v := by noncomm_ring
      _ = r * v := by rw [hrq.2]
      _ = v := hrv
  refine ⟨⟨hv, hqv, hvq⟩, star_mem hv, ?_, ?_⟩
  · have h := congrArg star hvq
    rwa [star_mul, hqsa.star_eq] at h
  · have h := congrArg star hqv
    rwa [star_mul, hqsa.star_eq] at h

/-- **`main.tex` Corollary `cor:q_finite` and Lemma
`lem:finite_corner_finite_global` / `main.tex:1422-1450`.**

If the compressed vector functional `tau_q` is a faithful tracial state on the corner
`q M q`, then `q` is a *finite projection of `M`*: it is not Murray–von Neumann
equivalent to a proper subprojection of itself.

The manuscript argument is followed verbatim: from `v* v = q`, `v v* = r ≤ q` one gets
`tau_q(r) = tau_q(v v*) = tau_q(v* v) = tau_q(q) = 1`, hence `tau_q(q - r) = 0`, and
faithfulness applied to the projection `q - r` gives `r = q`. -/
theorem isFiniteProjection_of_faithfulNormalTracialCorner {M : VonNeumannAlgebra H}
    {q : H →L[ℂ] H} {Ω : H} (h : IsFaithfulNormalTracialCorner M q Ω) :
    M.IsFiniteProjection q := by
  have hqproj : M.IsProjection q := ⟨h.isStarProjection, h.mem⟩
  have hqsa : IsSelfAdjoint q := h.isStarProjection.isSelfAdjoint
  refine ⟨hqproj, ?_⟩
  intro r hr hrq hequiv
  obtain ⟨v, hv, hv1, hv2⟩ := hequiv
  obtain ⟨hvcorner, hvstarcorner⟩ :=
    mem_corner_of_mvNEquiv_projLe hqsa hqproj.mul_self hr.mul_self hv hv1 hv2 hrq
  -- Traciality of `tau_q` on the corner gives `tau_q(r) = tau_q(q)`.
  have htr : tauVec Ω (v * star v) = tauVec Ω (star v * v) :=
    h.tracial_corner hvcorner hvstarcorner
  rw [hv1, hv2] at htr
  have hq1 : tauVec Ω q = 1 := h.apply_unit
  have hr1 : tauVec Ω r = 1 := by rw [htr, hq1]
  -- `q - r` is a projection of `M` living in the corner, with `tau_q(q - r) = 0`.
  set x : H →L[ℂ] H := q - r with hxdef
  have hx : M.IsProjection x := VonNeumannAlgebra.IsProjection.sub hr hqproj hrq
  have hqx : q * x = x := by rw [hxdef, mul_sub, hqproj.mul_self, hrq.2]
  have hxq : x * q = x := by rw [hxdef, sub_mul, hqproj.mul_self, hrq.1]
  have hstarx : star x * x = x := by rw [hx.star_eq, hx.mul_self]
  have hzero : cornerTau q Ω (star x * x) = 0 := by
    rw [hstarx, cornerTau_apply, hqx, hxq]
    have : ⟪Ω, x Ω⟫_ℂ = tauVec Ω x := rfl
    rw [this, hxdef, map_sub, hq1, hr1, sub_self]
  have hx0 : x = 0 := h.faithful x hx.2 hqx hxq hzero
  have : q - r = 0 := hx0
  exact (sub_eq_zero.mp this).symm

end Finiteness

/-! ## §2  Fullness of `q`

`main.tex` Proposition `prop:fullness` (`main.tex:1473-1499`).  A central projection
`z` of `M = A''` orthogonal to `q` kills `Ω`, hence kills the dense set of vectors
`pi_omega(b) pi_omega(a) Ω`, hence vanishes.
-/

section Fullness

/-- **`main.tex` Proposition `prop:fullness`.**  Let `A` be a represented star algebra,
`B` a set of operators commuting with `A`, and `Ω` a vector fixed by the projection `q`
such that the vectors `b a Ω` (`a ∈ A`, `b ∈ B`) span a dense subspace.  Then `q` is a
**full** projection of the von Neumann algebra `M = A''`: its central support is `1`.

Auxiliary assumptions, both manuscript clauses: `hB` is `main.tex`
eq. `eq:M-commutes-complement` and `hdense` is `main.tex` eq. `eq:dense_states`. -/
theorem isFull_of_dense_cyclic_vectors {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {B : Set (H →L[ℂ] H)} {q : H →L[ℂ] H} {Ω : H}
    (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hqΩ : q Ω = Ω)
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H)) :
    (StarSubalgebra.vonNeumannGenerated A).IsFull q := by
  set M : VonNeumannAlgebra H := StarSubalgebra.vonNeumannGenerated A with hMdef
  refine VonNeumannAlgebra.isFull_of_forall_central ?_
  intro z hz hz0 hzq
  refine hz0 ?_
  -- `z Ω = z q Ω = 0`.
  have hzΩ : z Ω = 0 := by
    have h1 : (z * q) Ω = (0 : H →L[ℂ] H) Ω := by rw [hzq]
    rw [show (z * q) Ω = z (q Ω) from rfl, hqΩ] at h1
    simpa using h1
  have hzM : z ∈ M := VonNeumannAlgebra.mem_of_mem_center hz.2
  have hvanish : ∀ ξ ∈ (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω}), z ξ = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem ξ hξ =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hξ
        have hbz : b * z = z * b :=
          StarSubalgebra.mem_vonNeumannGenerated_iff.mp hzM b (hB hb)
        have haM : a ∈ M := StarSubalgebra.mem_vonNeumannGenerated_of_mem ha
        have haz : z * a = a * z := hz.commute haM
        have hcomm : z * (b * a) = (b * a) * z := by
          rw [← mul_assoc, ← hbz, mul_assoc, haz, ← mul_assoc]
        have h1 : z ((b * a) Ω) = (z * (b * a)) Ω := rfl
        rw [h1, hcomm, show ((b * a) * z) Ω = (b * a) (z Ω) from rfl, hzΩ, map_zero]
    | zero => simp
    | add ξ η _ _ hξ hη => rw [map_add, hξ, hη, add_zero]
    | smul c ξ _ hξ => rw [map_smul, hξ, smul_zero]
  have hfun : (z : H → H) = fun _ => 0 :=
    Continuous.ext_on hdense z.continuous continuous_const fun ξ hξ => hvanish ξ hξ
  exact ContinuousLinearMap.ext fun ξ => congrFun hfun ξ

end Fullness

/-! ## §3  Central summands, relative finiteness, and the type-III obstruction -/

section Summand

/-- The **central summand** `z M` of a concrete von Neumann algebra, as a set of operators.
It is not a `VonNeumannAlgebra H` because its unit `z` is not `1`; the comparison theory
below is therefore phrased relative to a set of operators. -/
def centralSummand (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Set (H →L[ℂ] H) :=
  (fun x => z * x) '' (M : Set (H →L[ℂ] H))

theorem mem_centralSummand_iff {M : VonNeumannAlgebra H} {z y : H →L[ℂ] H} :
    y ∈ centralSummand M z ↔ ∃ x ∈ M, z * x = y := by
  simp [centralSummand, eq_comm]

theorem mul_mem_centralSummand {M : VonNeumannAlgebra H} {z x : H →L[ℂ] H} (hx : x ∈ M) :
    z * x ∈ centralSummand M z := ⟨x, hx, rfl⟩

theorem centralSummand_subset {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) : centralSummand M z ⊆ (M : Set (H →L[ℂ] H)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (VonNeumannAlgebra.mem_of_mem_center hz.2) hx

/-- Murray–von Neumann equivalence **relative to a set** `S` of operators: the implementing
partial isometry is required to lie in `S`. -/
def MvNEquivIn (S : Set (H →L[ℂ] H)) (p r : H →L[ℂ] H) : Prop :=
  ∃ v ∈ S, star v * v = p ∧ v * star v = r

/-- A projection is **finite relative to a set** `S` of operators when it is not equivalent,
by a partial isometry of `S`, to a proper subprojection of itself belonging to `S`. -/
def IsFiniteProjectionIn (S : Set (H →L[ℂ] H)) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ S ∧
    ∀ r, IsStarProjection r → r ∈ S → VonNeumannAlgebra.ProjLe r p →
      MvNEquivIn S p r → r = p

/-- The **type-III obstruction predicate**: a set of operators is *type-III-like* when it
contains no nonzero finite projection.  (For a von Neumann algebra this is precisely the
defining property of type III.)  The Lane-G conclusion is that no nonzero central summand
of `M_Γ` has this property. -/
def IsTypeIIILike (S : Set (H →L[ℂ] H)) : Prop :=
  ∀ p, IsStarProjection p → p ∈ S → p ≠ 0 → ¬ IsFiniteProjectionIn S p

/-- Finiteness with respect to a larger algebra implies finiteness with respect to a smaller
set of operators: there are fewer partial isometries available.  This is the manuscript's
final step, "`zq` is finite with respect to `z M_Γ`". -/
theorem isFiniteProjectionIn_of_isFiniteProjection {M : VonNeumannAlgebra H}
    {S : Set (H →L[ℂ] H)} {p : H →L[ℂ] H} (hSM : S ⊆ (M : Set (H →L[ℂ] H)))
    (hp : M.IsFiniteProjection p) (hpS : p ∈ S) : IsFiniteProjectionIn S p := by
  refine ⟨hp.1.1, hpS, fun r hr hrS hrp hequiv => ?_⟩
  obtain ⟨v, hvS, hv1, hv2⟩ := hequiv
  exact hp.2 r ⟨hr, hSM hrS⟩ hrp ⟨v, hSM hvS, hv1, hv2⟩

/-- A nonzero finite projection in `S` refutes type-III-likeness of `S`. -/
theorem not_isTypeIIILike_of_isFiniteProjectionIn {S : Set (H →L[ℂ] H)} {p : H →L[ℂ] H}
    (hp : IsFiniteProjectionIn S p) (hp0 : p ≠ 0) : ¬ IsTypeIIILike S :=
  fun hS => hS p hp.1 hp.2.1 hp0 hp

end Summand

/-! ## §4  The main theorem: a nonzero finite projection in every nonzero central summand

`main.tex` Theorem `thm:finite_projections_exist` (`main.tex:1501-1539`).
-/

section Main

/-- **`main.tex` Theorem `thm:finite_projections_exist`** — *the theorem whose conclusion
contains the nonzero finite projection* `z * q`.

Let `M` be a concrete von Neumann algebra carrying the P50 faithful normal tracial corner
state `tau_q` at a projection `q`, and assume `q` is full (Proposition `prop:fullness`,
proved above as `isFull_of_dense_cyclic_vectors`).  Then for every nonzero central
projection `z` of `M`:

1. `z * q ≠ 0` — by fullness;
2. `z * q` is a projection of `M`, dominated by `z` and by `q`;
3. `z * q` is a **finite projection of `M`**;
4. `z * q` lies in the central summand `z M`; and
5. `z * q` is **finite relative to the summand** `z M` itself. -/
theorem central_summand_nonzero_finite_projection {M : VonNeumannAlgebra H}
    {q : H →L[ℂ] H} {Ω : H} {z : H →L[ℂ] H}
    (h : IsFaithfulNormalTracialCorner M q Ω) (hfull : M.IsFull q)
    (hz : M.IsCentralProjection z) (hz0 : z ≠ 0) :
    z * q ≠ 0 ∧ M.IsProjection (z * q) ∧
      VonNeumannAlgebra.ProjLe (z * q) z ∧ VonNeumannAlgebra.ProjLe (z * q) q ∧
      M.IsFiniteProjection (z * q) ∧ z * q ∈ centralSummand M z ∧
      IsFiniteProjectionIn (centralSummand M z) (z * q) := by
  have hqproj : M.IsProjection q := ⟨h.isStarProjection, h.mem⟩
  have hqfin : M.IsFiniteProjection q := isFiniteProjection_of_faithfulNormalTracialCorner h
  have hne : z * q ≠ 0 := hfull.mul_ne_zero hz hz0
  have hzqproj : M.IsProjection (z * q) := hz.mul_isProjection hqproj
  have hzqfin : M.IsFiniteProjection (z * q) := hqfin.mul_central hz
  have hmem : z * q ∈ centralSummand M z := mul_mem_centralSummand hqproj.2
  exact ⟨hne, hzqproj, hz.mul_projLe_left hqproj, hz.mul_projLe_right hqproj, hzqfin, hmem,
    isFiniteProjectionIn_of_isFiniteProjection (centralSummand_subset hz) hzqfin hmem⟩

/-- **Type-III exclusion.**  No nonzero central summand of `M` is type-III-like: it always
contains the nonzero finite projection `z * q`. -/
theorem not_isTypeIIILike_centralSummand {M : VonNeumannAlgebra H}
    {q : H →L[ℂ] H} {Ω : H} {z : H →L[ℂ] H}
    (h : IsFaithfulNormalTracialCorner M q Ω) (hfull : M.IsFull q)
    (hz : M.IsCentralProjection z) (hz0 : z ≠ 0) :
    ¬ IsTypeIIILike (centralSummand M z) := by
  obtain ⟨hne, -, -, -, -, -, hfin⟩ :=
    central_summand_nonzero_finite_projection h hfull hz hz0
  exact not_isTypeIIILike_of_isFiniteProjectionIn hfin hne

end Main

/-! ## §5  Exported P51 theorem from the P50 input data -/

section Export

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **Exported P51 theorem** (`main.tex:1418-1539`).

The input data are exactly those of the exported P50 theorem
`NormalFaithfulCornerTrace.normal_faithful_corner_trace`: the compatible finite-codespace
system `D` with GNS vector `Ω`, its decreasing projection tower, the represented regional
C⋆-algebra `A` with its norm-density data, the commuting complementary set `B`, and the
dense-vector premise.

The conclusion collects the three manuscript statements for `M = A''` and `q` the strong
limit of the stage projections:

* `q` is a **finite** projection of `M` (Lemma `lem:finite_corner_finite_global`);
* `q` is **full** in `M` (Proposition `prop:fullness`); and
* every nonzero central projection `z` yields the **nonzero finite projection `z q` inside
  the central summand `z M`**, so that summand is not type III
  (Theorem `thm:finite_projections_exist`).

No global trace or weight on `M` is asserted, no direct integral is used, and the center of
`M` is not claimed to be trivial. -/
theorem full_finite_corner_central_exclusion {Ω : H}
    (D : CompatibleFiniteCodespaceSystem Ω ι)
    (hp : IsDecreasingProjTower D.toFiniteCodespaceSystem.stageProj)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hlocal : ∀ n, Set.range (D.pi n) ⊆ (A : Set (H →L[ℂ] H)))
    (hAdense : (A : Set (H →L[ℂ] H)) ⊆ closure (⋃ n, Set.range (D.pi n)))
    (B : Set (H →L[ℂ] H)) (hB : B ⊆ Set.centralizer (A : Set (H →L[ℂ] H)))
    (hdense : Dense (Submodule.span ℂ
      {ξ : H | ∃ a ∈ (A : Set (H →L[ℂ] H)), ∃ b ∈ B, ξ = (b * a) Ω} : Set H)) :
    (StarSubalgebra.vonNeumannGenerated A).IsFiniteProjection
        (limitProj D.toFiniteCodespaceSystem.stageProj) ∧
      (StarSubalgebra.vonNeumannGenerated A).IsFull
        (limitProj D.toFiniteCodespaceSystem.stageProj) ∧
      ∀ z, (StarSubalgebra.vonNeumannGenerated A).IsCentralProjection z → z ≠ 0 →
        z * limitProj D.toFiniteCodespaceSystem.stageProj ≠ 0 ∧
        IsFiniteProjectionIn
          (centralSummand (StarSubalgebra.vonNeumannGenerated A) z)
          (z * limitProj D.toFiniteCodespaceSystem.stageProj) ∧
        ¬ IsTypeIIILike (centralSummand (StarSubalgebra.vonNeumannGenerated A) z) := by
  set q := limitProj D.toFiniteCodespaceSystem.stageProj with hqdef
  have hcorner :
      IsFaithfulNormalTracialCorner (StarSubalgebra.vonNeumannGenerated A) q Ω :=
    normal_faithful_corner_trace D hp A hAclosed hlocal hAdense B hB hdense
  have hqΩ : q Ω = Ω :=
    limitProj_apply_self fun n => D.toFiniteCodespaceSystem.stageProj_apply_self n
  have hfull : (StarSubalgebra.vonNeumannGenerated A).IsFull q :=
    isFull_of_dense_cyclic_vectors hB hqΩ hdense
  refine ⟨isFiniteProjection_of_faithfulNormalTracialCorner hcorner, hfull, fun z hz hz0 => ?_⟩
  obtain ⟨hne, -, -, -, -, -, hfin⟩ :=
    central_summand_nonzero_finite_projection hcorner hfull hz hz0
  exact ⟨hne, hfin, not_isTypeIIILike_of_isFiniteProjectionIn hfin hne⟩

end Export

/-! ## §6  Non-vacuity of the exported hypotheses

The exported theorem inherits the P50 premises and adds none beyond them.  The following
witness re-instantiates them in the one-dimensional sanity system of P49/P50, showing that
the hypotheses of `full_finite_corner_central_exclusion` are simultaneously satisfiable.  It
is a consistency check only and carries no manuscript content. -/

section Sanity

/-- **Non-vacuity.**  Every hypothesis of the exported P51 theorem is satisfied by the
one-dimensional sanity system, with `A = ⊤`, complementary algebra `{1}`, and GNS vector
`EuclideanSpace.single 0 1`. -/
theorem sanity_full_finite_corner_central_exclusion :
    (StarSubalgebra.vonNeumannGenerated (⊤ : StarSubalgebra ℂ
        (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)))).IsFiniteProjection
        (limitProj sanitySystem.toFiniteCodespaceSystem.stageProj) ∧
      (StarSubalgebra.vonNeumannGenerated (⊤ : StarSubalgebra ℂ
        (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)))).IsFull
        (limitProj sanitySystem.toFiniteCodespaceSystem.stageProj) := by
  classical
  set Ω : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1 with hΩ
  have hAdense : ((⊤ : StarSubalgebra ℂ
        (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) :
        Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) ⊆
      closure (⋃ n, Set.range (sanitySystem.pi n)) := by
    intro T _
    refine subset_closure (Set.mem_iUnion.2 ⟨0, ?_⟩)
    rw [sanity_range_pi]
    exact Set.mem_univ T
  have hB : ({1} : Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) ⊆
      Set.centralizer ((⊤ : StarSubalgebra ℂ
        (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) :
        Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    intro c _
    simp
  have hdense : Dense (Submodule.span ℂ
      {ξ : EuclideanSpace ℂ (Fin 1) |
        ∃ a ∈ ((⊤ : StarSubalgebra ℂ
              (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) :
            Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))),
          ∃ b ∈ ({1} : Set (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))),
            ξ = (b * a) Ω} : Set (EuclideanSpace ℂ (Fin 1))) := by
    have hinner : ⟪Ω, Ω⟫_ℂ = 1 := sanitySystem.toFiniteCodespaceSystem.inner_self_eq_one
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
  obtain ⟨hfin, hfull, -⟩ :=
    full_finite_corner_central_exclusion (Ω := Ω) sanitySystem
      sanitySystem_isDecreasingProjTower ⊤ (by simp) (fun n => by simp) hAdense {1} hB hdense
  exact ⟨hfin, hfull⟩

end Sanity

end FullFiniteCornerCentralExclusion
end AristotleCandidates
