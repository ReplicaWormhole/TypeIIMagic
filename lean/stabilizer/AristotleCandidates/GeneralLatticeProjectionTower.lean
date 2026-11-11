import Mathlib
import AristotleCandidates.FiniteStabilizerProjector
import AristotleCandidates.BicommutantVonNeumannCore

/-!
# P48 — general-lattice local-code projection tower

**Source basis:** `main.tex:1026-1195` (the exhaustion `Γ₁ ⊆ Γ₂ ⊆ ⋯`, the local
projections `Pₙ`, Lemma `lema:proj_inequality` on `pₙ ≥ pₙ₊₁`, and
Lemma `lem:q_exists` on the strong limit `q` with `q Ω = Ω`).

**Plan alignment.** Package `P48`, lane `G`, predecessors: none.  The gate
discharged here is the construction of the decreasing local-code projections and
of their limiting projection `q`, together with the data needed downstream.  No
trace on the corner, no faithfulness, finiteness, fullness, global weight, or
type-III statement is made anywhere in this file.  No hyperbolic basis and no
tensor-factor coordinates are used.

## What is constructed

* `ProjectionTower.IsDecreasingProjTower` — a decreasing tower of star
  projections `p : ℕ → H →L[ℂ] H` on a complex Hilbert space, i.e.
  `pₙ` self-adjoint idempotent and `pₙ pₘ = pₘ` for `n ≤ m`.
* `ProjectionTower.limitProj` — **the projection `q`**, defined as the orthogonal
  projection onto `⋂ₙ {x | pₙ x = x}`.
* `ProjectionTower.IsDecreasingProjTower.tendsto_limitProj` — `pₙ x → q x` for
  every `x`, i.e. `pₙ → q` in the strong operator topology.  This is *proved*,
  not assumed: the pinned Mathlib is sufficient, so no analytic hypothesis is
  isolated as a structure field.
* `ProjectionTower.IsDecreasingProjTower.limitProj_mem_vonNeumannAlgebra` —
  `q ∈ M` for any concrete von Neumann algebra `M` containing every `pₙ`.  This
  uses only strong closedness of a commutant; the (unavailable) double commutant
  theorem is *not* used.
* `LocalCode.SupportSystem`, `LocalCode.LatticeExhaustion` — the general lattice
  data: a support map on the stabilizer group `S` and a countable exhaustion of
  a region `Γ ⊆ L` by finite stages.
* `LocalCode.stageSubgroup` — the finite stabilizer constraints seen at stage
  `n`, namely the subgroup of elements supported inside `Γₙ`.
* `LocalCode.latticeCodeProj` — the local code projection `pₙ`, realized as the
  group average `|Gₙ|⁻¹ ∑_{g ∈ Gₙ} U g` of the unitary representation of the
  stage subgroup.
* `LocalCode.latticeLimitProj` — **the projection `q` for the general lattice
  tower**, with `latticeCodeProj_mul_of_le` (`main.tex` Lemma
  `lema:proj_inequality`), `tendsto_latticeLimitProj`,
  `latticeLimitProj_mem_vonNeumannAlgebra`, and
  `latticeLimitProj_apply_of_invariant` (`q Ω = Ω`).
* `LocalCode.latticeCodeProj_sub_isPositive` and
  `LocalCode.latticeCodeProj_sub_latticeLimitProj_isPositive` — the same order
  relations `pₙ ≥ pₘ` and `pₙ ≥ q` in Loewner (positive-operator) form.

## Source/Mathlib obstructions handled

The pinned Mathlib has no von Neumann double commutant theorem, so `M_Γ` cannot
be described as a strong-operator closure.  This is not needed: `q ∈ M` is
obtained from the elementary fact that a *commutant* is strongly closed, applied
to `M = (M')'`.  Likewise the manuscript derives `pₙ ≥ pₙ₊₁` from a partial-trace
support-projection lemma; here the same inequality is obtained algebraically from
the inclusion of stage stabilizer subgroups, which is the form actually available
from the general-lattice data.

## Auxiliary assumptions (all explicit Lean hypotheses, no axioms)

1. `LatticeExhaustion`: `stage_finite`, `stage_mono`, `stage_subset`,
   `stage_exhausts` — a countable increasing exhaustion of `Γ` by finite sets.
2. `SupportSystem`: `supp_one`, `supp_mul`, `supp_inv` — the support map is
   subadditive, which is what makes the stage constraints a subgroup and makes
   the family of stage subgroups monotone.
3. `[∀ n, Fintype (stageSubgroup E ss n)]` — **local finiteness**: only finitely
   many stabilizer elements are supported in a given finite stage.  For a Pauli
   stabilizer group this holds because the local Pauli group is finite; here it
   is an explicit instance hypothesis.
4. `U : S →* (H →L[ℂ] H)` with `hU : ∀ g, star (U g) = U g⁻¹` — a unitary
   representation of the stabilizer group on the (GNS) Hilbert space.
5. For `q ∈ M`: the hypothesis `∀ n, latticeCodeProj E ss U n ∈ M` that each
   stage projection lies in the ambient von Neumann algebra.
6. For `q Ω = Ω`: the hypothesis that `Ω` is invariant under every stabilizer
   element supported in some stage.

The manuscript-facing statements are therefore conditional on 1–6; nothing is
derived from unstated data.
-/

namespace AristotleCandidates
namespace ProjectionTower

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The fixed-point subspace `{x | a x = x}` of a bounded operator. -/
def fixedSpace (a : H →L[ℂ] H) : Submodule ℂ H :=
  LinearMap.ker ((a - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)

omit [CompleteSpace H] in
lemma mem_fixedSpace {a : H →L[ℂ] H} {x : H} : x ∈ fixedSpace a ↔ a x = x := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

omit [CompleteSpace H] in
lemma isClosed_fixedSpace (a : H →L[ℂ] H) :
    IsClosed ((fixedSpace a : Submodule ℂ H) : Set H) :=
  (a - 1).isClosed_ker

/-- Self-adjointness in inner-product form. -/
lemma inner_isSelfAdjoint {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) (x y : H) :
    ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
  nth_rewrite 2 [← ha]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

section PairIdentity

variable {a b : H →L[ℂ] H}

/-- Pythagoras identity for a nested pair of operators: if `b` is a star
projection and `b a = b` then `‖a x - b x‖² = ‖a x‖² - ‖b x‖²`. -/
lemma norm_sq_apply_sub (hb : IsStarProjection b) (hba : b * a = b) (x : H) :
    ‖a x - b x‖ ^ 2 = ‖a x‖ ^ 2 - ‖b x‖ ^ 2 := by
  have hbc : b (a x - b x) = 0 := by
    have h1 : b (a x) = b x := congrArg (fun t : H →L[ℂ] H => t x) hba
    have h2 : b (b x) = b x := congrArg (fun t : H →L[ℂ] H => t x) hb.isIdempotentElem
    simp [map_sub, h1, h2]
  have hinner : ⟪a x - b x, b x⟫_ℂ = 0 := by
    have h2 : b (b x) = b x := congrArg (fun t : H →L[ℂ] H => t x) hb.isIdempotentElem
    calc ⟪a x - b x, b x⟫_ℂ = ⟪a x - b x, b (b x)⟫_ℂ := by rw [h2]
      _ = ⟪b (a x - b x), b x⟫_ℂ := (inner_isSelfAdjoint hb.isSelfAdjoint _ _).symm
      _ = 0 := by rw [hbc, inner_zero_left]
  have hsum : (a x - b x) + b x = a x := by abel
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a x - b x) (b x) hinner
  rw [hsum] at this
  linarith

/-- The difference of a nested pair of star projections is again a star projection. -/
lemma isStarProjection_sub (ha : IsStarProjection a) (hb : IsStarProjection b)
    (hab : a * b = b) (hba : b * a = b) : IsStarProjection (a - b) := by
  refine ⟨?_, ha.isSelfAdjoint.sub hb.isSelfAdjoint⟩
  have : (a - b) * (a - b) = a * a - a * b - b * a + b * b := by noncomm_ring
  rw [IsIdempotentElem, this, ha.isIdempotentElem, hb.isIdempotentElem, hab, hba]
  abel

end PairIdentity

/-- A star projection is a positive operator. -/
lemma isPositive_of_isStarProjection {c : H →L[ℂ] H} (hc : IsStarProjection c) :
    c.IsPositive := by
  refine ⟨(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 hc.isSelfAdjoint, fun x => ?_⟩
  have hidem : c (c x) = c x := congrArg (fun t : H →L[ℂ] H => t x) hc.isIdempotentElem
  have h : ⟪c x, x⟫_ℂ = ⟪c x, c x⟫_ℂ := by
    conv_lhs => rw [← hidem]
    rw [inner_isSelfAdjoint hc.isSelfAdjoint]
  rw [ContinuousLinearMap.reApplyInnerSelf, h]
  exact inner_self_nonneg

lemma norm_apply_le_of_isStarProjection {a : H →L[ℂ] H} (ha : IsStarProjection a) (x : H) :
    ‖a x‖ ≤ ‖x‖ := by
  have := norm_sq_apply_sub ha (mul_one a) x
  have hx : ((1 : H →L[ℂ] H)) x = x := rfl
  rw [hx] at this
  nlinarith [norm_nonneg (x - a x), norm_nonneg (a x), norm_nonneg x]

/-!
## Decreasing towers of star projections and their strong limit
-/

/-- A decreasing tower of star projections on `H`: each `p n` is a self-adjoint
idempotent and `p m ≤ p n` for `n ≤ m`, expressed algebraically. -/
structure IsDecreasingProjTower (p : ℕ → H →L[ℂ] H) : Prop where
  isStarProjection : ∀ n, IsStarProjection (p n)
  mul_of_le : ∀ {n m : ℕ}, n ≤ m → p n * p m = p m

lemma IsDecreasingProjTower.mul_of_le' {p : ℕ → H →L[ℂ] H} (hp : IsDecreasingProjTower p)
    {n m : ℕ} (h : n ≤ m) : p m * p n = p m := by
  have := congrArg star (hp.mul_of_le h)
  rwa [star_mul, (hp.isStarProjection n).isSelfAdjoint.star_eq,
    (hp.isStarProjection m).isSelfAdjoint.star_eq] at this

variable (p : ℕ → H →L[ℂ] H)

/-- The limiting subspace: the intersection of all the fixed-point subspaces. -/
def limitSpace : Submodule ℂ H := ⨅ n, fixedSpace (p n)

variable {p}

omit [CompleteSpace H] in
lemma mem_limitSpace {x : H} : x ∈ limitSpace p ↔ ∀ n, p n x = x := by
  simp [limitSpace, mem_fixedSpace]

variable (p)

omit [CompleteSpace H] in
lemma isClosed_limitSpace : IsClosed ((limitSpace p : Submodule ℂ H) : Set H) := by
  have hset : ((limitSpace p : Submodule ℂ H) : Set H) =
      ⋂ n, ((fixedSpace (p n) : Submodule ℂ H) : Set H) := by
    ext x
    simp [limitSpace]
  rw [hset]
  exact isClosed_iInter fun n => isClosed_fixedSpace (p n)

instance hasOrthogonalProjection_limitSpace : (limitSpace p).HasOrthogonalProjection := by
  have : CompleteSpace (limitSpace p) := (isClosed_limitSpace p).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The limiting projection `q`** of a tower `p` of projections: the orthogonal
projection onto the intersection of the fixed spaces of the `p n`. -/
noncomputable def limitProj : H →L[ℂ] H := (limitSpace p).starProjection

lemma limitProj_isStarProjection : IsStarProjection (limitProj p) := by
  refine ⟨Submodule.isIdempotentElem_starProjection _, ?_⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

lemma limitProj_apply_mem (x : H) : limitProj p x ∈ limitSpace p :=
  Submodule.starProjection_apply_mem _ _

lemma apply_limitProj (n : ℕ) (x : H) : p n (limitProj p x) = limitProj p x :=
  mem_limitSpace.1 (limitProj_apply_mem p x) n

lemma mul_limitProj (n : ℕ) : p n * limitProj p = limitProj p :=
  ContinuousLinearMap.ext fun x => apply_limitProj p n x

lemma limitProj_mul (hp : IsDecreasingProjTower p) (n : ℕ) :
    limitProj p * p n = limitProj p := by
  have := congrArg star (mul_limitProj p n)
  rwa [star_mul, (hp.isStarProjection n).isSelfAdjoint.star_eq,
    (limitProj_isStarProjection p).isSelfAdjoint.star_eq] at this

namespace IsDecreasingProjTower

variable {p}
variable (hp : IsDecreasingProjTower p)
include hp

/-- **Strong convergence**: `p n x → q x` for every `x`. -/
theorem tendsto_limitProj (x : H) :
    Tendsto (fun n => p n x) atTop (𝓝 (limitProj p x)) := by
  -- the decreasing sequence of squared norms
  set A : ℕ → ℝ := fun n => ‖p n x‖ ^ 2 with hA
  have hAanti : Antitone A := by
    intro n m hnm
    have h : p m x = p m (p n x) := by
      have := congrArg (fun t : H →L[ℂ] H => t x) (hp.mul_of_le' hnm)
      simpa using this.symm
    have := norm_apply_le_of_isStarProjection (hp.isStarProjection m) (p n x)
    rw [← h] at this
    have h0 := norm_nonneg (p m x)
    simp only [hA]
    nlinarith [norm_nonneg (p n x)]
  have hAbdd : ∀ n, (0:ℝ) ≤ A n := fun n => by positivity
  have hAconv : Tendsto A atTop (𝓝 (⨅ n, A n)) :=
    tendsto_atTop_ciInf hAanti ⟨0, fun y hy => by obtain ⟨n, rfl⟩ := hy; exact hAbdd n⟩
  -- the sequence `p n x` is Cauchy
  have hkey : ∀ {n m : ℕ}, n ≤ m → ‖p n x - p m x‖ ^ 2 = A n - A m := fun {n m} h =>
    norm_sq_apply_sub (hp.isStarProjection m) (hp.mul_of_le' h) x
  have hcauchy : CauchySeq (fun n => p n x) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hAcauchy : CauchySeq A := hAconv.cauchySeq
    rw [Metric.cauchySeq_iff'] at hAcauchy
    obtain ⟨N, hN⟩ := hAcauchy (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : A n - A N ≤ 0 := sub_nonpos.2 (hAanti hn)
    have h2 : |A n - A N| < ε ^ 2 := by
      have := hN n hn
      rwa [Real.dist_eq] at this
    have h3 : ‖p N x - p n x‖ ^ 2 = A N - A n := hkey hn
    have h4 : A N - A n < ε ^ 2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h2
      exact h2
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    nlinarith [norm_nonneg (p N x - p n x)]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- identify the limit with `q x`
  have hymem : y ∈ limitSpace p := by
    rw [mem_limitSpace]
    intro n
    have hcl : IsClosed ((fixedSpace (p n) : Submodule ℂ H) : Set H) := isClosed_fixedSpace _
    have hev : ∀ᶠ m in atTop, (fun m => p m x) m ∈ ((fixedSpace (p n) : Submodule ℂ H) : Set H) := by
      filter_upwards [eventually_ge_atTop n] with m hm
      have : p n (p m x) = p m x := congrArg (fun t : H →L[ℂ] H => t x) (hp.mul_of_le hm)
      exact mem_fixedSpace.2 this
    exact mem_fixedSpace.1 (hcl.mem_of_tendsto hy hev)
  have hperp : ∀ w ∈ limitSpace p, ⟪x - y, w⟫_ℂ = 0 := by
    intro w hw
    have hzero : ∀ n, ⟪x - p n x, w⟫_ℂ = 0 := by
      intro n
      have hw' : p n w = w := mem_limitSpace.1 hw n
      rw [inner_sub_left, inner_isSelfAdjoint (hp.isStarProjection n).isSelfAdjoint, hw',
        sub_self]
    have hlim : Tendsto (fun n => ⟪x - p n x, w⟫_ℂ) atTop (𝓝 ⟪x - y, w⟫_ℂ) := by
      have : Tendsto (fun n => x - p n x) atTop (𝓝 (x - y)) := tendsto_const_nhds.sub hy
      exact (continuous_inner.tendsto _).comp (this.prodMk_nhds tendsto_const_nhds)
    have : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 ⟪x - y, w⟫_ℂ) := by
      simpa [hzero] using hlim
    exact tendsto_nhds_unique this tendsto_const_nhds
  have : limitProj p x = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hymem hperp
  rw [this]
  exact hy

/-- The limit projection lies in every von Neumann algebra (indeed in every
commutant) containing all the `p n`. -/
theorem limitProj_mem_centralizer {T : Set (H →L[ℂ] H)}
    (hmem : ∀ n, p n ∈ Set.centralizer T) : limitProj p ∈ Set.centralizer T := by
  intro y hy
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 : Tendsto (fun n => y (p n x)) atTop (𝓝 (y (limitProj p x))) :=
    (y.continuous.tendsto _).comp (tendsto_limitProj hp x)
  have h2 : Tendsto (fun n => p n (y x)) atTop (𝓝 (limitProj p (y x))) :=
    tendsto_limitProj hp (y x)
  have h3 : ∀ n, y (p n x) = p n (y x) := by
    intro n
    have := hmem n y hy
    exact congrArg (fun t : H →L[ℂ] H => t x) this
  simp only [h3] at h1
  exact (tendsto_nhds_unique h2 h1).symm

/-- The limit projection of a decreasing tower belongs to any concrete von Neumann
algebra containing every stage. -/
theorem limitProj_mem_vonNeumannAlgebra (M : VonNeumannAlgebra H) (h : ∀ n, p n ∈ M) :
    limitProj p ∈ M := by
  have hcoe : Set.centralizer ((M.commutant : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) =
      (M : Set (H →L[ℂ] H)) := by
    rw [VonNeumannAlgebra.coe_commutant]
    exact M.centralizer_centralizer
  have hstage : ∀ n, p n ∈ Set.centralizer
      ((M.commutant : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) := by
    intro n
    rw [hcoe]
    exact h n
  have := hp.limitProj_mem_centralizer hstage
  rwa [hcoe] at this

end IsDecreasingProjTower

end ProjectionTower

/-!
## Support systems, lattice exhaustions, and local code projections

This section provides the general-lattice input data of `main.tex:1026-1060`:
a countable exhaustion of a region `Γ ⊆ L` by finite subsets, the *finite
stabilizer constraints* seen at each stage (the subgroup of stabilizer elements
supported inside that stage), and the associated local code projections.
-/

namespace LocalCode

open ProjectionTower

/-- Abstract *support data* for a group `S` of stabilizer elements acting on a
lattice `L`: a support map which is empty on the unit, subadditive under
multiplication, and non-increasing under inversion.  This is the only structure
on `S` used below; in particular no hyperbolic basis and no tensor-factor
coordinates are assumed. -/
structure SupportSystem (L S : Type*) [Group S] where
  /-- The support of a stabilizer element. -/
  supp : S → Set L
  supp_one : supp 1 = ∅
  supp_mul : ∀ g h, supp (g * h) ⊆ supp g ∪ supp h
  supp_inv : ∀ g, supp g⁻¹ ⊆ supp g

namespace SupportSystem

variable {L S : Type*} [Group S] (ss : SupportSystem L S)

/-- The subgroup of stabilizer elements supported inside a given subset `Λ` of the
lattice.  These are the "finite stabilizer constraints seen at stage `Λ`". -/
def localSubgroup (Λ : Set L) : Subgroup S where
  carrier := {g | ss.supp g ⊆ Λ}
  one_mem' := by simp [ss.supp_one]
  mul_mem' := fun {a b} ha hb =>
    (ss.supp_mul a b).trans (Set.union_subset ha hb)
  inv_mem' := fun {a} ha => (ss.supp_inv a).trans ha

@[simp]
lemma mem_localSubgroup {Λ : Set L} {g : S} :
    g ∈ ss.localSubgroup Λ ↔ ss.supp g ⊆ Λ := Iff.rfl

/-- Larger regions see more constraints. -/
lemma localSubgroup_mono {Λ Λ' : Set L} (h : Λ ⊆ Λ') :
    ss.localSubgroup Λ ≤ ss.localSubgroup Λ' :=
  fun _ hg => hg.trans h

end SupportSystem

/-- A countable exhaustion `Γ₁ ⊆ Γ₂ ⊆ ⋯`, `Γ = ⋃ₙ Γₙ`, of a region `Γ` of a
general lattice `L` by finite subsets (`main.tex:1033-1036`). -/
structure LatticeExhaustion (L : Type*) where
  /-- The region being exhausted. -/
  region : Set L
  /-- The `n`-th finite stage. -/
  stage : ℕ → Set L
  stage_finite : ∀ n, (stage n).Finite
  stage_mono : Monotone stage
  stage_subset : ∀ n, stage n ⊆ region
  stage_exhausts : region ⊆ ⋃ n, stage n

namespace LatticeExhaustion

variable {L : Type*} (E : LatticeExhaustion L)

lemma iUnion_stage : ⋃ n, E.stage n = E.region :=
  subset_antisymm (Set.iUnion_subset E.stage_subset) E.stage_exhausts

end LatticeExhaustion

section CodeProjections

variable {S : Type*} [Group S]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : S →* (H →L[ℂ] H)) (G : ℕ → Subgroup S) [∀ n, Fintype (G n)]

/-- The **local code projection** at stage `n`: the group average of the unitary
representation of the finite stabilizer subgroup `G n`. -/
noncomputable def codeProj (n : ℕ) : H →L[ℂ] H :=
  groupAverage (U.comp (G n).subtype)

omit [CompleteSpace H] in
lemma codeProj_def (n : ℕ) :
    codeProj U G n = ((Fintype.card (G n) : ℂ))⁻¹ • ∑ g : (G n), U (g : S) :=
  rfl

variable {U G}

omit [CompleteSpace H] in
lemma mul_codeProj_of_mem {n : ℕ} {g : S} (hg : g ∈ G n) :
    U g * codeProj U G n = codeProj U G n :=
  mul_groupAverage (U.comp (G n).subtype) ⟨g, hg⟩

omit [CompleteSpace H] in
lemma codeProj_mul_of_mem {n : ℕ} {g : S} (hg : g ∈ G n) :
    codeProj U G n * U g = codeProj U G n :=
  groupAverage_mul (U.comp (G n).subtype) ⟨g, hg⟩

omit [CompleteSpace H] in
lemma codeProj_isIdempotentElem (n : ℕ) : IsIdempotentElem (codeProj U G n) :=
  groupAverage_mul_self (U.comp (G n).subtype)

lemma codeProj_isSelfAdjoint (hU : ∀ g : S, star (U g) = U g⁻¹) (n : ℕ) :
    IsSelfAdjoint (codeProj U G n) :=
  star_groupAverage (U.comp (G n).subtype) (fun g => hU (g : S))

lemma codeProj_isStarProjection (hU : ∀ g : S, star (U g) = U g⁻¹) (n : ℕ) :
    IsStarProjection (codeProj U G n) :=
  ⟨codeProj_isIdempotentElem n, codeProj_isSelfAdjoint hU n⟩

omit [CompleteSpace H] in
/-- **Monotonicity of the code-projection tower** (`main.tex:1049-1057`,
Lemma `lema:proj_inequality`): more constraints give a smaller projection.
Here it is obtained algebraically from `G n ≤ G m`, with no partial trace. -/
lemma codeProj_mul_codeProj (hG : Monotone G) {n m : ℕ} (h : n ≤ m) :
    codeProj U G n * codeProj U G m = codeProj U G m := by
  have hcard : ((Fintype.card (G n) : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := (G n)))
  calc codeProj U G n * codeProj U G m
      = ((Fintype.card (G n) : ℂ))⁻¹ • ∑ g : (G n), U (g : S) * codeProj U G m := by
        rw [codeProj_def, smul_mul_assoc, Finset.sum_mul]
    _ = ((Fintype.card (G n) : ℂ))⁻¹ • ∑ _g : (G n), codeProj U G m := by
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        exact mul_codeProj_of_mem (hG h g.2)
    _ = codeProj U G m := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hcard, one_smul]

/-- The local code projections form a decreasing tower of star projections. -/
theorem isDecreasingProjTower_codeProj (hU : ∀ g : S, star (U g) = U g⁻¹)
    (hG : Monotone G) : IsDecreasingProjTower (codeProj U G) :=
  ⟨codeProj_isStarProjection hU, fun h => codeProj_mul_codeProj hG h⟩

variable (U G)

/-- **The limiting local-code projection `q`** of `main.tex:1140-1147`
(Lemma `lem:q_exists`), for a general monotone family `G` of finite stabilizer
subgroups. -/
noncomputable def limitCodeProj : H →L[ℂ] H := limitProj (codeProj U G)

variable {U G}

theorem limitCodeProj_isStarProjection : IsStarProjection (limitCodeProj U G) :=
  limitProj_isStarProjection _

/-- `q ≤ p n` for every stage. -/
theorem codeProj_mul_limitCodeProj (n : ℕ) :
    codeProj U G n * limitCodeProj U G = limitCodeProj U G :=
  mul_limitProj _ n

theorem limitCodeProj_mul_codeProj (hU : ∀ g : S, star (U g) = U g⁻¹) (hG : Monotone G)
    (n : ℕ) : limitCodeProj U G * codeProj U G n = limitCodeProj U G :=
  limitProj_mul _ (isDecreasingProjTower_codeProj hU hG) n

/-- **Strong convergence** `p n → q` (`main.tex:1148-1155`). -/
theorem tendsto_limitCodeProj (hU : ∀ g : S, star (U g) = U g⁻¹) (hG : Monotone G) (x : H) :
    Filter.Tendsto (fun n => codeProj U G n x) Filter.atTop (nhds (limitCodeProj U G x)) :=
  (isDecreasingProjTower_codeProj hU hG).tendsto_limitProj x

/-- `q` belongs to any concrete von Neumann algebra containing all the stage
projections (`main.tex:1156-1161`).  This uses only strong closedness of a
commutant, not the double commutant theorem. -/
theorem limitCodeProj_mem_vonNeumannAlgebra (hU : ∀ g : S, star (U g) = U g⁻¹)
    (hG : Monotone G) (M : VonNeumannAlgebra H) (h : ∀ n, codeProj U G n ∈ M) :
    limitCodeProj U G ∈ M :=
  (isDecreasingProjTower_codeProj hU hG).limitProj_mem_vonNeumannAlgebra M h

omit [CompleteSpace H] in
/-- If a vector is invariant under all constraints of stage `n`, the stage
projection fixes it. -/
theorem codeProj_apply_of_invariant {n : ℕ} {x : H} (hx : ∀ g ∈ G n, U g x = x) :
    codeProj U G n x = x := by
  have hcard : ((Fintype.card (G n) : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := (G n)))
  rw [codeProj_def]
  have hterm : ∀ g ∈ (Finset.univ : Finset (G n)), (U (g : S)) x = x :=
    fun g _ => hx (g : S) g.2
  have hsum : (∑ g : (G n), U (g : S)) x = (Fintype.card (G n) : ℂ) • x := by
    rw [ContinuousLinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [ContinuousLinearMap.smul_apply, hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **`q Ω = Ω`** (`main.tex:1161-1180`): the limiting projection fixes any vector
invariant under all the stabilizer constraints.  In the GNS picture this is the
cyclic vector `Ω`. -/
theorem limitCodeProj_apply_of_invariant {x : H} (hx : ∀ n, ∀ g ∈ G n, U g x = x) :
    limitCodeProj U G x = x := by
  have hmem : x ∈ limitSpace (codeProj U G) :=
    mem_limitSpace.2 fun n => codeProj_apply_of_invariant (hx n)
  show (limitSpace (codeProj U G)).starProjection x = x
  exact Submodule.starProjection_eq_self_iff.2 hmem

end CodeProjections

/-!
## The general-lattice local-code projection tower

Assembling the pieces: a general lattice `L`, a region `Γ` exhausted by finite
stages, a support system on the stabilizer group `S`, and a unitary
representation `U` of `S` on the (GNS) Hilbert space `H`.
-/

section LatticeTower

variable {L S : Type*} [Group S]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (E : LatticeExhaustion L) (ss : SupportSystem L S)

/-- The finite stabilizer constraints seen at stage `n` of the exhaustion. -/
def stageSubgroup (n : ℕ) : Subgroup S := ss.localSubgroup (E.stage n)

variable {E ss}

lemma stageSubgroup_mono : Monotone (stageSubgroup (S := S) E ss) :=
  fun _ _ h => ss.localSubgroup_mono (E.stage_mono h)

variable (E ss)
variable (U : S →* (H →L[ℂ] H)) [∀ n, Fintype (stageSubgroup (S := S) E ss n)]

/-- The local code projection of the region-stage `Γₙ`, i.e. `pₙ = π_ω(P_{Γₙ})`
of `main.tex:1044-1048`. -/
noncomputable def latticeCodeProj (n : ℕ) : H →L[ℂ] H :=
  codeProj U (stageSubgroup E ss) n

/-- **The limiting local-code projection `q`** for a general lattice exhaustion
(`main.tex:1140-1147`). -/
noncomputable def latticeLimitProj : H →L[ℂ] H :=
  limitCodeProj U (stageSubgroup E ss)

variable {E ss U}

theorem latticeCodeProj_isStarProjection (hU : ∀ g : S, star (U g) = U g⁻¹) (n : ℕ) :
    IsStarProjection (latticeCodeProj E ss U n) :=
  codeProj_isStarProjection hU n

omit [CompleteSpace H] in
/-- The tower is decreasing: `pₙ ≥ pₙ₊₁` in the algebraic form `pₙ pₘ = pₘ`
for `n ≤ m` (`main.tex:1049-1057`). -/
theorem latticeCodeProj_mul_of_le {n m : ℕ} (h : n ≤ m) :
    latticeCodeProj E ss U n * latticeCodeProj E ss U m = latticeCodeProj E ss U m :=
  codeProj_mul_codeProj stageSubgroup_mono h

theorem isDecreasingProjTower_latticeCodeProj (hU : ∀ g : S, star (U g) = U g⁻¹) :
    IsDecreasingProjTower (latticeCodeProj E ss U) :=
  isDecreasingProjTower_codeProj hU stageSubgroup_mono

theorem latticeLimitProj_isStarProjection :
    IsStarProjection (latticeLimitProj E ss U) :=
  limitCodeProj_isStarProjection

/-- `q ≤ pₙ`. -/
theorem latticeCodeProj_mul_latticeLimitProj (n : ℕ) :
    latticeCodeProj E ss U n * latticeLimitProj E ss U = latticeLimitProj E ss U :=
  codeProj_mul_limitCodeProj n

theorem latticeLimitProj_mul_latticeCodeProj (hU : ∀ g : S, star (U g) = U g⁻¹) (n : ℕ) :
    latticeLimitProj E ss U * latticeCodeProj E ss U n = latticeLimitProj E ss U :=
  limitCodeProj_mul_codeProj hU stageSubgroup_mono n

/-- The manuscript's `pₙ ≥ pₘ` for `n ≤ m` in Loewner form: `pₙ - pₘ` is a
positive operator (`main.tex:1049-1057`). -/
theorem latticeCodeProj_sub_isPositive (hU : ∀ g : S, star (U g) = U g⁻¹) {n m : ℕ}
    (h : n ≤ m) :
    (latticeCodeProj E ss U n - latticeCodeProj E ss U m).IsPositive :=
  isPositive_of_isStarProjection
    (isStarProjection_sub (latticeCodeProj_isStarProjection hU n)
      (latticeCodeProj_isStarProjection hU m) (latticeCodeProj_mul_of_le h)
      ((isDecreasingProjTower_codeProj hU stageSubgroup_mono).mul_of_le' h))

/-- `q ≤ pₙ` in Loewner form. -/
theorem latticeCodeProj_sub_latticeLimitProj_isPositive (hU : ∀ g : S, star (U g) = U g⁻¹)
    (n : ℕ) :
    (latticeCodeProj E ss U n - latticeLimitProj E ss U).IsPositive :=
  isPositive_of_isStarProjection
    (isStarProjection_sub (latticeCodeProj_isStarProjection hU n)
      latticeLimitProj_isStarProjection (latticeCodeProj_mul_latticeLimitProj n)
      (latticeLimitProj_mul_latticeCodeProj hU n))

/-- **`pₙ → q` strongly** (`main.tex:1148-1155`). -/
theorem tendsto_latticeLimitProj (hU : ∀ g : S, star (U g) = U g⁻¹) (x : H) :
    Filter.Tendsto (fun n => latticeCodeProj E ss U n x) Filter.atTop
      (nhds (latticeLimitProj E ss U x)) :=
  tendsto_limitCodeProj hU stageSubgroup_mono x

/-- **`q ∈ M_Γ`** (`main.tex:1156-1161`), for any concrete von Neumann algebra
containing all stage projections. -/
theorem latticeLimitProj_mem_vonNeumannAlgebra (hU : ∀ g : S, star (U g) = U g⁻¹)
    (M : VonNeumannAlgebra H) (h : ∀ n, latticeCodeProj E ss U n ∈ M) :
    latticeLimitProj E ss U ∈ M :=
  limitCodeProj_mem_vonNeumannAlgebra hU stageSubgroup_mono M h

/-- **`q Ω = Ω`** (`main.tex:1161-1180`) for a vector invariant under every
stabilizer element supported in some stage of the exhaustion. -/
theorem latticeLimitProj_apply_of_invariant {x : H}
    (hx : ∀ g : S, (∃ n, ss.supp g ⊆ E.stage n) → U g x = x) :
    latticeLimitProj E ss U x = x :=
  limitCodeProj_apply_of_invariant fun n g hg => hx g ⟨n, hg⟩

end LatticeTower

end LocalCode

end AristotleCandidates
