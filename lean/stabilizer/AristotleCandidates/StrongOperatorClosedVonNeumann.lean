import Mathlib
import AristotleCandidates.BicommutantVonNeumannCore

/-!
# P49A — strong-operator convergence and strongly closed concrete von Neumann algebras

**Infrastructure only.**  This file makes no manuscript claim.  It develops a reusable
strong-operator-topology (SOT) convergence and closure API for the bounded operators
`H →L[ℂ] H` on a complex Hilbert space `H`, and proves the four core facts required by the
plan for package `P49A`:

1. `StrongOperator.stronglyTendsto_iff_tendsto_sot` — a net (filter-indexed family) of bounded
   operators converges in the strong operator topology exactly when it converges pointwise in
   the norm of `H`;
2. `StrongOperator.isStronglyClosed_centralizer` (with its filter form
   `StrongOperator.mem_centralizer_of_stronglyTendsto`) — the commutant of an *arbitrary* set of
   bounded operators is strongly closed;
3. `StrongOperator.isStronglyClosed_vonNeumannAlgebra` (with
   `StrongOperator.mem_vonNeumannAlgebra_of_stronglyTendsto`) — every concrete
   `M : VonNeumannAlgebra H` is strongly closed, obtained from Mathlib's defining equality
   `M = M''`;
4. `StrongOperator.StronglyTendsto.const_mul`, `StrongOperator.StronglyTendsto.mul_const` and the
   joint bounded-product corollary `StrongOperator.StronglyTendsto.mul_of_bounded`
   (equivalently `StrongOperator.StronglyTendsto.mul_of_norm_le`) — strong limits are stable under
   left/right multiplication by a fixed bounded operator, and, for a *uniformly bounded* family,
   under products of two strongly convergent families.

## Plan alignment

* **Package and lane:** `P49A`, lane `shared`.
* **Predecessors:** `P48` (`AristotleCandidates.GeneralLatticeProjectionTower`), whose
  strong-convergence arguments are generalized here; the file itself only needs the algebraic
  bicommutant material of `AristotleCandidates.BicommutantVonNeumannCore`, so `P48` is not
  imported.
* **Gate discharged:** commutants, and hence Mathlib's concrete von Neumann algebras, are closed
  under strong-operator limits.
* **Forbidden downstream claims, not made here:** no identification of the strong closure of a
  star algebra with its bicommutant (no double commutant theorem), no Kaplansky density, no corner
  trace, no faithfulness, finiteness, fullness, or type classification.

## Formalization notes

Mathlib's `PointwiseConvergenceCLM σ E F`, with notation `E →Lₚₜ[ℂ] F`, *is* the strong operator
topology (its own docstring says so; the name avoids clashing terminology).  We therefore do not
re-define the topology; instead we introduce the abbreviation `StrongOperator.SOT H` for the
strong-operator-topologized copy of `H →L[ℂ] H`, together with the (definitional) transfer maps
`StrongOperator.toSOT` / `StrongOperator.ofSOT`, and the predicate
`StrongOperator.StronglyTendsto`, which expresses pointwise convergence and is the form actually
used in proofs.  Statement (1) is exactly the bridge between the two.

Nothing here is assumed: there is no `sorry`, no new axiom, no `opaque`, and no supplied analytic
interface.
-/

universe u v

open Filter Topology

namespace StrongOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The strong operator topology on `H →L[ℂ] H` -/

/-- The bounded operators on `H`, carrying the **strong operator topology** (the topology of
pointwise convergence).  This is Mathlib's `PointwiseConvergenceCLM`, which is a type synonym of
`H →L[ℂ] H`. -/
abbrev SOT (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →Lₚₜ[ℂ] H

/-- View a bounded operator as an element of the strong-operator-topologized space. -/
def toSOT (T : H →L[ℂ] H) : SOT H := T

/-- View an element of the strong-operator-topologized space as a bounded operator. -/
def ofSOT (T : SOT H) : H →L[ℂ] H := T

@[simp] theorem ofSOT_toSOT (T : H →L[ℂ] H) : ofSOT (toSOT T) = T := rfl

@[simp] theorem toSOT_ofSOT (T : SOT H) : toSOT (ofSOT T) = T := rfl

@[simp] theorem toSOT_apply (T : H →L[ℂ] H) (x : H) : (toSOT T) x = T x := rfl

@[simp] theorem ofSOT_apply (T : SOT H) (x : H) : (ofSOT T) x = T x := rfl

theorem toSOT_injective : Function.Injective (toSOT (H := H)) := fun _ _ h => h

/-- The strong-operator-topologized space is Hausdorff, so strong limits are unique. -/
instance : T2Space (SOT H) := inferInstance

/-! ### Strong convergence of a net of operators -/

/-- **Strong (operator) convergence** of a filter-indexed family: `T i → A` pointwise in the norm
of `H`.  For `l = atTop` this is convergence of a sequence, for a general `l` that of a net. -/
def StronglyTendsto {ι : Type v} (l : Filter ι) (T : ι → (H →L[ℂ] H)) (A : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun i => T i x) l (𝓝 (A x))

/-- **(1) Core conclusion.**  A net of bounded operators converges in the strong operator
topology exactly when it converges pointwise in the norm of `H`. -/
theorem stronglyTendsto_iff_tendsto_sot {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} :
    StronglyTendsto l T A ↔ Tendsto (fun i => toSOT (T i)) l (𝓝 (toSOT A)) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.symm

/-- Restatement of (1) in the direction most often used: SOT convergence gives pointwise
convergence. -/
theorem tendsto_sot_iff_forall_tendsto {ι : Type v} {l : Filter ι} {T : ι → SOT H} {A : SOT H} :
    Tendsto T l (𝓝 A) ↔ ∀ x : H, Tendsto (fun i => (ofSOT (T i)) x) l (𝓝 ((ofSOT A) x)) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto

/-- Strong limits are unique. -/
theorem StronglyTendsto.unique {ι : Type v} {l : Filter ι} [l.NeBot] {T : ι → (H →L[ℂ] H)}
    {A B : H →L[ℂ] H} (hA : StronglyTendsto l T A) (hB : StronglyTendsto l T B) : A = B := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact tendsto_nhds_unique (hA x) (hB x)

theorem stronglyTendsto_const {ι : Type v} (l : Filter ι) (A : H →L[ℂ] H) :
    StronglyTendsto l (fun _ => A) A := fun _ => tendsto_const_nhds

/-- Norm convergence of operators implies strong convergence: the strong operator topology is
coarser than the operator-norm topology. -/
theorem stronglyTendsto_of_tendsto_norm {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} (hT : Tendsto T l (𝓝 A)) : StronglyTendsto l T A := fun x =>
  ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp hT

theorem StronglyTendsto.add {ι : Type v} {l : Filter ι} {T S : ι → (H →L[ℂ] H)}
    {A B : H →L[ℂ] H} (hT : StronglyTendsto l T A) (hS : StronglyTendsto l S B) :
    StronglyTendsto l (fun i => T i + S i) (A + B) := fun x => by
  simpa using (hT x).add (hS x)

theorem StronglyTendsto.sub {ι : Type v} {l : Filter ι} {T S : ι → (H →L[ℂ] H)}
    {A B : H →L[ℂ] H} (hT : StronglyTendsto l T A) (hS : StronglyTendsto l S B) :
    StronglyTendsto l (fun i => T i - S i) (A - B) := fun x => by
  simpa using (hT x).sub (hS x)

theorem StronglyTendsto.smul {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} (c : ℂ) (hT : StronglyTendsto l T A) :
    StronglyTendsto l (fun i => c • T i) (c • A) := fun x => by
  simpa using (hT x).const_smul c

/-! ### Strongly closed sets of operators -/

/-- A set of bounded operators is **strongly closed** when it is closed in the strong operator
topology. -/
def IsStronglyClosed (K : Set (H →L[ℂ] H)) : Prop :=
  IsClosed {A : SOT H | ofSOT A ∈ K}

/-- A strongly closed set contains the strong limit of any of its nets. -/
theorem IsStronglyClosed.mem_of_stronglyTendsto {K : Set (H →L[ℂ] H)} (hK : IsStronglyClosed K)
    {ι : Type v} {l : Filter ι} [l.NeBot] {T : ι → (H →L[ℂ] H)} {A : H →L[ℂ] H}
    (hmem : ∀ᶠ i in l, T i ∈ K) (hT : StronglyTendsto l T A) : A ∈ K := by
  have h : Tendsto (fun i => toSOT (T i)) l (𝓝 (toSOT A)) := stronglyTendsto_iff_tendsto_sot.1 hT
  exact hK.mem_of_tendsto h (by simpa using hmem)

/-- Conversely, a set closed under strong limits of nets is strongly closed.  (Stated with the
canonical neighbourhood filter net, which is the standard way to produce a converging net.) -/
theorem isStronglyClosed_of_mem_of_stronglyTendsto {K : Set (H →L[ℂ] H)}
    (h : ∀ (l : Filter (SOT H)), l.NeBot → ∀ (A : H →L[ℂ] H),
      (∀ᶠ B in l, ofSOT B ∈ K) → StronglyTendsto l (fun B => ofSOT B) A → A ∈ K) :
    IsStronglyClosed K := by
  rw [IsStronglyClosed, ← closure_subset_iff_isClosed]
  intro A hA
  set K' : Set (SOT H) := {B : SOT H | ofSOT B ∈ K} with hK'
  have hne : (𝓝[K'] A).NeBot := mem_closure_iff_clusterPt.1 hA
  have hmem : ∀ᶠ B in 𝓝[K'] A, ofSOT B ∈ K := self_mem_nhdsWithin
  have htend : Tendsto (fun B : SOT H => B) (𝓝[K'] A) (𝓝 A) := nhdsWithin_le_nhds
  have hconv : StronglyTendsto (𝓝[K'] A) (fun B : SOT H => ofSOT B) (ofSOT A) :=
    stronglyTendsto_iff_tendsto_sot.2 (by simpa using htend)
  exact h _ hne _ hmem hconv

/-! ### (2) Commutants are strongly closed -/

/-- **(2) Core conclusion (filter form).**  The commutant of an arbitrary set `S` of bounded
operators is closed under strong limits. -/
theorem mem_centralizer_of_stronglyTendsto {S : Set (H →L[ℂ] H)} {ι : Type v} {l : Filter ι}
    [l.NeBot] {T : ι → (H →L[ℂ] H)} {A : H →L[ℂ] H} (hmem : ∀ᶠ i in l, T i ∈ Set.centralizer S)
    (hT : StronglyTendsto l T A) : A ∈ Set.centralizer S := by
  intro y hy
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 : Tendsto (fun i => y (T i x)) l (𝓝 (y (A x))) := (y.continuous.tendsto _).comp (hT x)
  have h2 : Tendsto (fun i => T i (y x)) l (𝓝 (A (y x))) := hT (y x)
  have h3 : ∀ᶠ i in l, y (T i x) = T i (y x) := by
    filter_upwards [hmem] with i hi
    exact congrArg (fun t : H →L[ℂ] H => t x) (hi y hy)
  have h1' : Tendsto (fun i => T i (y x)) l (𝓝 (y (A x))) := h1.congr' h3
  have := tendsto_nhds_unique h2 h1'
  simpa using this.symm

/-- **(2) Core conclusion (topological form).**  The commutant of an arbitrary set of bounded
operators is strongly closed. -/
theorem isStronglyClosed_centralizer (S : Set (H →L[ℂ] H)) :
    IsStronglyClosed (Set.centralizer S) := by
  have hset : {A : SOT H | ofSOT A ∈ Set.centralizer S}
      = ⋂ y ∈ S, ⋂ x : H, {A : SOT H | y ((ofSOT A) x) = (ofSOT A) (y x)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hA y hy x
      have := congrArg (fun t : H →L[ℂ] H => t x) (hA y hy)
      simpa using this
    · intro h y hy
      refine ContinuousLinearMap.ext fun x => ?_
      simpa using h y hy x
  rw [IsStronglyClosed, hset]
  refine isClosed_biInter fun y _ => isClosed_iInter fun x => ?_
  exact isClosed_eq (y.continuous.comp (continuous_eval_const x)) (continuous_eval_const (y x))

/-! ### (3) Concrete von Neumann algebras are strongly closed -/

section VonNeumann

variable [CompleteSpace H]

/-- The underlying set of a concrete von Neumann algebra is a commutant: this is Mathlib's
defining equality `M = M''`. -/
theorem coe_vonNeumannAlgebra_eq_centralizer (M : VonNeumannAlgebra H) :
    (M : Set (H →L[ℂ] H)) = Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
  (M.centralizer_centralizer).symm

/-- **(3) Core conclusion (filter form).**  A concrete von Neumann algebra contains the strong
limit of any of its nets. -/
theorem mem_vonNeumannAlgebra_of_stronglyTendsto (M : VonNeumannAlgebra H) {ι : Type v}
    {l : Filter ι} [l.NeBot] {T : ι → (H →L[ℂ] H)} {A : H →L[ℂ] H} (hmem : ∀ᶠ i in l, T i ∈ M)
    (hT : StronglyTendsto l T A) : A ∈ M := by
  have hcoe : (M : Set (H →L[ℂ] H)) = Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
    coe_vonNeumannAlgebra_eq_centralizer M
  have hmem' : ∀ᶠ i in l, T i ∈ Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) := by
    filter_upwards [hmem] with i hi
    rw [← hcoe]
    exact hi
  have := mem_centralizer_of_stronglyTendsto hmem' hT
  rw [← hcoe] at this
  exact this

/-- **(3) Core conclusion (topological form).**  Every concrete von Neumann algebra is strongly
closed. -/
theorem isStronglyClosed_vonNeumannAlgebra (M : VonNeumannAlgebra H) :
    IsStronglyClosed (M : Set (H →L[ℂ] H)) := by
  rw [IsStronglyClosed, coe_vonNeumannAlgebra_eq_centralizer M]
  exact isStronglyClosed_centralizer _

/-- The same statement for the commutant of a von Neumann algebra. -/
theorem isStronglyClosed_commutant (M : VonNeumannAlgebra H) :
    IsStronglyClosed ((M.commutant : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) :=
  isStronglyClosed_vonNeumannAlgebra _

/-- Strong closedness of the bicommutant of a star subalgebra (the algebraic bicommutant of
`AristotleCandidates.BicommutantVonNeumannCore`).  No identification of this bicommutant with a
strong closure is claimed. -/
theorem isStronglyClosed_vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsStronglyClosed ((StarSubalgebra.vonNeumannGenerated S : VonNeumannAlgebra H) :
      Set (H →L[ℂ] H)) :=
  isStronglyClosed_vonNeumannAlgebra _

end VonNeumann

/-! ### (4) Multiplicative stability of strong limits -/

/-- **(4a)** Left multiplication by a fixed bounded operator preserves strong limits. -/
theorem StronglyTendsto.const_mul {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} (hT : StronglyTendsto l T A) (B : H →L[ℂ] H) :
    StronglyTendsto l (fun i => B * T i) (B * A) := by
  intro x
  simpa using (B.continuous.tendsto _).comp (hT x)

/-- **(4b)** Right multiplication by a fixed bounded operator preserves strong limits. -/
theorem StronglyTendsto.mul_const {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} (hT : StronglyTendsto l T A) (B : H →L[ℂ] H) :
    StronglyTendsto l (fun i => T i * B) (A * B) := by
  intro x
  simpa using hT (B x)

/-- **(4c) Joint bounded-product corollary.**  If `T i → A` strongly with `‖T i‖` uniformly
bounded, and `S i → B` strongly, then `T i * S i → A * B` strongly.  Uniform boundedness of the
left factor is what makes the product jointly strongly continuous. -/
theorem StronglyTendsto.mul_of_bounded {ι : Type v} {l : Filter ι} {T S : ι → (H →L[ℂ] H)}
    {A B : H →L[ℂ] H} {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C) (hT : StronglyTendsto l T A)
    (hS : StronglyTendsto l S B) : StronglyTendsto l (fun i => T i * S i) (A * B) := by
  intro x
  have hgoal : Tendsto (fun i => ‖(T i * S i) x - (A * B) x‖) l (𝓝 0) := by
    have ha : Tendsto (fun i => ‖S i x - B x‖) l (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hS x)
    have hb : Tendsto (fun i => ‖T i (B x) - A (B x)‖) l (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hT (B x))
    have hsum : Tendsto (fun i => C * ‖S i x - B x‖ + ‖T i (B x) - A (B x)‖) l (𝓝 0) := by
      simpa using (ha.const_mul C).add hb
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hsum
    have hsplit : (T i * S i) x - (A * B) x
        = T i (S i x - B x) + (T i (B x) - A (B x)) := by
      simp [ContinuousLinearMap.mul_apply, map_sub]
    have h1 : ‖T i (S i x - B x)‖ ≤ C * ‖S i x - B x‖ := by
      refine le_trans ((T i).le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
    calc ‖(T i * S i) x - (A * B) x‖
        = ‖T i (S i x - B x) + (T i (B x) - A (B x))‖ := by rw [hsplit]
      _ ≤ ‖T i (S i x - B x)‖ + ‖T i (B x) - A (B x)‖ := norm_add_le _ _
      _ ≤ C * ‖S i x - B x‖ + ‖T i (B x) - A (B x)‖ := by linarith
  exact tendsto_iff_norm_sub_tendsto_zero.2 hgoal

/-- Variant of the joint bounded-product corollary with the uniform bound stated as an
existential. -/
theorem StronglyTendsto.mul_of_norm_le {ι : Type v} {l : Filter ι} {T S : ι → (H →L[ℂ] H)}
    {A B : H →L[ℂ] H} (hbdd : ∃ C : ℝ, ∀ i, ‖T i‖ ≤ C) (hT : StronglyTendsto l T A)
    (hS : StronglyTendsto l S B) : StronglyTendsto l (fun i => T i * S i) (A * B) := by
  obtain ⟨C, hC⟩ := hbdd
  exact hT.mul_of_bounded hC hS

/-- A convenient special case of (4): compression of a uniformly bounded strong limit by two fixed
operators, `B * T i * D → B * A * D` strongly. -/
theorem StronglyTendsto.compress {ι : Type v} {l : Filter ι} {T : ι → (H →L[ℂ] H)}
    {A : H →L[ℂ] H} (hT : StronglyTendsto l T A) (B D : H →L[ℂ] H) :
    StronglyTendsto l (fun i => B * T i * D) (B * A * D) :=
  (hT.const_mul B).mul_const D

end StrongOperator
