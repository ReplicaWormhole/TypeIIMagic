import Mathlib
import AristotleCandidates.VonNeumannBicommutantTheorem

/-!
# P49C — Kaplansky density and the compressed-corner approximation

**Source basis:** `main.tex:1269-1315`.

For a represented unital C⋆-algebra `A ⊆ B(H)` (a norm closed `StarSubalgebra ℂ (H →L[ℂ] H)`)
with bicommutant `M = A''`, this file proves the **bounded (unit-ball) Kaplansky density
theorem**: the unit ball of `A` is strong-operator dense in the unit ball of `M`, together with
its scaled norm-bounded form, the self-adjoint intermediate forms, and the manuscript-facing
corollaries:

* for a projection `q ∈ M` and `x ∈ M`, a uniformly norm-bounded net `(a_i)` in `A` with
  `q a_i q → q x q` strongly (`exists_net_compression`);
* the jointly indexed bounded product convergence `q a_i q b_j q → q x q y q`
  (`exists_net_compression_product`) used to pass cyclicity from `q A q` to `q M q`.

## Plan alignment

* **Package and lane:** `P49C`, lane `shared` (analytic infrastructure used by Lane G).
* **Predecessors:** `P49B` (`AristotleCandidates.VonNeumannBicommutantTheorem`) and, through it,
  `P49A` (`AristotleCandidates.StrongOperatorClosedVonNeumann`) and the algebraic bicommutant
  core.  Nothing from `P50` or later is imported or used.
* **Gate discharged:** unit-ball Kaplansky density and the bounded compressed-corner
  approximation required by `P50`.
* **Forbidden downstream claims, not made here:** nothing is asserted about `tau_q` (no
  traciality, normality or faithfulness), no finiteness or fullness statement, no type-III
  exclusion, and no Lane-H factor claim.

## Hypotheses actually used

* `H` is a complex Hilbert space (`[CompleteSpace H]`).
* `A : StarSubalgebra ℂ (H →L[ℂ] H)` — in Mathlib this is automatically unital — together with
  the explicit C⋆-hypothesis `IsClosed (A : Set (H →L[ℂ] H))`.  Norm closedness is genuinely
  used: it is what makes the resolvent `(1 + b²)⁻¹` of a self-adjoint `b ∈ A` lie again in `A`
  (spectral permanence, `StarSubalgebra.coe_isUnit`).

No density statement is supplied as a structure field or an axiom: every density result below is
proved.  There is no `sorry`, `admit`, `opaque`, `unsafe`, `implemented_by`, or new axiom.

## Method

1. `mem_strongClosure_of_convex_of_weak_approx`: for a **convex** set of operators, approximation
   in the weak sense on arbitrary finite families of vector pairs already gives membership in the
   strong-operator closure.  This is proved by Hilbert-space convex projection in the
   amplification `H^n` (no Hahn–Banach needed).
2. `selfAdjoint_mem_strongClosure`: combining 1 with the `P49B` bicommutant theorem, the
   self-adjoint part of `A` is strongly dense in the self-adjoint part of `M`.
3. The Cayley-type transform `kap b = 2 b (1 + b²)⁻¹` is developed from scratch
   (`isUnit_one_add_sq`, `norm_res_apply_le`, `norm_mul_res_apply_le`, `kap_sub_apply_bound`);
   its norm is at most one, it stays inside `A`, and it is strongly continuous on self-adjoint
   elements.  Together with the continuous functional calculus of `H →L[ℂ] H` this upgrades 2 to
   the self-adjoint unit ball (`selfAdjoint_ball_mem_strongClosure`).
4. A local `2 × 2` matrix algebra over `A` inside `B(H ⊕ H)` (built on the amplification
   machinery of `P49B`) removes the self-adjointness restriction, giving unit-ball density
   `ball_mem_strongClosure` and its scaled form `scaled_ball_mem_strongClosure`.
5. Nets are extracted (`exists_net_of_mem_strongClosure`) and compressed by a projection, using
   the `P49A` product convergence lemmas.
-/

universe u

open Filter Topology
open scoped Pointwise
open VonNeumannBicommutant

namespace KaplanskyDensity

/-! ## Elementary algebraic facts -/

section Elementary

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The commutant of a `star`-closed set is `star`-closed. -/
theorem star_mem_centralizer {S : Set (H →L[ℂ] H)} (hS : ∀ a ∈ S, star a ∈ S)
    {c : H →L[ℂ] H} (hc : c ∈ Set.centralizer S) : star c ∈ Set.centralizer S := by
  intro a ha
  have h := hc (star a) (hS a ha)
  have := congrArg (fun t : H →L[ℂ] H => star t) h
  simpa [star_mul] using this.symm

/-- The bicommutant of a `star`-closed set is `star`-closed. -/
theorem star_mem_centralizer_centralizer {S : Set (H →L[ℂ] H)} (hS : ∀ a ∈ S, star a ∈ S)
    {x : H →L[ℂ] H} (hx : x ∈ Set.centralizer (Set.centralizer S)) :
    star x ∈ Set.centralizer (Set.centralizer S) := by
  intro c hc
  have hc' : star c ∈ Set.centralizer S := star_mem_centralizer hS hc
  have h := hx (star c) hc'
  have := congrArg (fun t : H →L[ℂ] H => star t) h
  simpa [star_mul] using this.symm

theorem star_mem_starSubalgebra_set {A : StarSubalgebra ℂ (H →L[ℂ] H)} :
    ∀ a ∈ (A : Set (H →L[ℂ] H)), star a ∈ (A : Set (H →L[ℂ] H)) := fun _ ha => star_mem ha

omit [CompleteSpace H] in
theorem smul_mem_centralizer_centralizer {S : Set (H →L[ℂ] H)} (c : ℂ) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer S)) :
    c • x ∈ Set.centralizer (Set.centralizer S) := by
  intro y hy
  have h := hx y hy
  simp only [smul_mul_assoc, mul_smul_comm, h]

end Elementary

section ElementaryComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint idempotent has norm at most one. -/
theorem norm_le_one_of_isProjection {q : H →L[ℂ] H} (h1 : star q = q) (h2 : q * q = q) :
    ‖q‖ ≤ 1 := by
  have hq : ‖star q * q‖ = ‖q‖ * ‖q‖ := CStarRing.norm_star_mul_self
  rw [h1, h2] at hq
  nlinarith [norm_nonneg q]

end ElementaryComplete

/-! ## Step 1 — convexity: weak approximation gives strong closure membership -/

section ConvexStep

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] InnerProductSpace.complexToReal

/-- **Convexity step.**  If `C` is a convex set of bounded operators and `x` can be approximated
by elements of `C` *weakly* — i.e. on arbitrary finite families of pairs of vectors, in the sense
of the inner products `⟪wᵢ, (x - a) vᵢ⟫` — then `x` lies in the strong operator closure of `C`.

This is the Hilbert-space form of "for convex sets, the weak and strong operator closures agree".
It is proved by projecting onto the closed convex set of amplified images, so no Hahn–Banach
separation theorem is needed. -/
theorem mem_strongClosure_of_convex_of_weak_approx {C : Set (H →L[ℂ] H)}
    (hconv : Convex ℝ C) {x : H →L[ℂ] H}
    (hw : ∀ (n : ℕ) (v w : Fin n → H) (ε : ℝ), 0 < ε →
      ∃ a ∈ C, ‖∑ i, (inner ℂ (w i) ((x - a) (v i)) : ℂ)‖ < ε) :
    x ∈ strongClosure C := by
  classical
  refine mem_strongClosure_of_approx fun F ε hε => ?_
  set n := F.card with hn
  set e := F.equivFin with he
  set v : Fin n → H := fun i => ((e.symm i : F) : H) with hv
  set Φ : (H →L[ℂ] H) → Amp H n := fun a => (WithLp.toLp 2 (fun i => a (v i)) : Amp H n) with hΦ
  set S : Set (Amp H n) := Φ '' C with hS
  set p : Amp H n := Φ x with hp
  have hΦapp : ∀ (a : H →L[ℂ] H) (i : Fin n), (Φ a) i = a (v i) := fun _ _ => rfl
  have hCne : C.Nonempty := by
    obtain ⟨a, ha, -⟩ := hw 0 (fun i => i.elim0) (fun i => i.elim0) 1 one_pos
    exact ⟨a, ha⟩
  have hSconv : Convex ℝ S := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
    refine ⟨s • a + t • b, hconv ha hb hs ht hst, ?_⟩
    ext i
    simp [hΦapp]
  have hpS : p ∈ closure S := by
    by_contra hc
    have hclne : (closure S).Nonempty := (hCne.image Φ).closure
    have hcompl : IsComplete (closure S) := isClosed_closure.isComplete
    obtain ⟨z, hz, hzmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hclne hcompl hSconv.closure p
    have hproj : ∀ w ∈ closure S, (inner ℝ (p - z) (w - z) : ℝ) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hSconv.closure hz).1 hzmin
    set W : Amp H n := p - z with hW
    have hWne : W ≠ 0 := sub_ne_zero.2 (fun h => hc (h ▸ hz))
    have hδ : 0 < ‖W‖ ^ 2 := by positivity
    obtain ⟨a, haC, hlt⟩ := hw n v (fun i => W i) (‖W‖ ^ 2) hδ
    have hsS : Φ a ∈ closure S := subset_closure ⟨a, haC, rfl⟩
    have hinner : (∑ i, (inner ℂ (W i) ((x - a) (v i)) : ℂ)) = inner ℂ W (p - Φ a) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
    have hsplit : p - Φ a = W - (Φ a - z) := by rw [hW]; abel
    have hre : ‖W‖ ^ 2 ≤ RCLike.re (inner ℂ W (p - Φ a) : ℂ) := by
      rw [hsplit, inner_sub_right, map_sub]
      have h1 : RCLike.re (inner ℂ W W : ℂ) = ‖W‖ ^ 2 := by
        rw [inner_self_eq_norm_sq]
      have h2 : RCLike.re (inner ℂ W (Φ a - z) : ℂ) ≤ 0 := by
        have := hproj (Φ a) hsS
        rwa [real_inner_eq_re_inner ℂ] at this
      linarith
    have hfin : ‖W‖ ^ 2 ≤ ‖(inner ℂ W (p - Φ a) : ℂ)‖ := le_trans hre (RCLike.re_le_norm _)
    rw [hinner] at hlt
    linarith
  rw [Metric.mem_closure_iff] at hpS
  obtain ⟨s, hsS, hs⟩ := hpS ε hε
  obtain ⟨a, haC, rfl⟩ := hsS
  refine ⟨a, haC, fun y hy => ?_⟩
  have hyv : y = v (e ⟨y, hy⟩) := by simp [hv]
  have hbound : ‖(p - Φ a) (e ⟨y, hy⟩)‖ ≤ ‖p - Φ a‖ := PiLp.norm_apply_le _ _
  have hd : ‖p - Φ a‖ < ε := by rwa [dist_eq_norm] at hs
  have hcomp : (p - Φ a) (e ⟨y, hy⟩) = x y - a y := by
    conv_rhs => rw [hyv]
    rfl
  rw [hcomp] at hbound
  linarith

end ConvexStep

/-! ## Step 2 — strong density of the self-adjoint part -/

section SelfAdjointStep

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The self-adjoint part of a star subalgebra is a real-convex set. -/
theorem convex_selfAdjoint_part {A : StarSubalgebra ℂ (H →L[ℂ] H)} :
    Convex ℝ {a : H →L[ℂ] H | a ∈ A ∧ IsSelfAdjoint a} := by
  rintro a ⟨haA, hasa⟩ b ⟨hbA, hbsa⟩ s t hs ht hst
  have h1 : s • a = (s : ℂ) • a := (Complex.coe_smul s a).symm
  have h2 : t • b = (t : ℂ) • b := (Complex.coe_smul t b).symm
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
    exact add_mem (SMulMemClass.smul_mem _ haA) (SMulMemClass.smul_mem _ hbA)
  · rw [h1, h2]
    unfold IsSelfAdjoint
    rw [star_add, star_smul, star_smul, hasa.star_eq, hbsa.star_eq]
    simp

/-- **Self-adjoint Kaplansky density (unbounded form).**  The self-adjoint part of a star
subalgebra `A ⊆ B(H)` is strong-operator dense in the self-adjoint part of its bicommutant. -/
theorem selfAdjoint_mem_strongClosure {A : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint x) :
    x ∈ strongClosure {a : H →L[ℂ] H | a ∈ A ∧ IsSelfAdjoint a} := by
  classical
  refine mem_strongClosure_of_convex_of_weak_approx (convex_selfAdjoint_part) ?_
  intro n v w ε hε
  set N : ℝ := 1 + ∑ i, (‖v i‖ + ‖w i‖) with hN
  have hNpos : 0 < N := by
    have hs : 0 ≤ ∑ i, (‖v i‖ + ‖w i‖) := Finset.sum_nonneg fun i _ => by positivity
    rw [hN]; linarith
  set δ : ℝ := ε / N with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨b, hbA, hb⟩ := exists_mem_approx_on_fin A hx (n + n) (Fin.append v w) hδpos
  have hbv : ∀ i, ‖(x - b) (v i)‖ < δ := by
    intro i
    have := hb (Fin.castAdd n i)
    rwa [Fin.append_left] at this
  have hbw : ∀ i, ‖(x - b) (w i)‖ < δ := by
    intro i
    have := hb (Fin.natAdd n i)
    rwa [Fin.append_right] at this
  refine ⟨(2⁻¹ : ℂ) • (b + star b),
    ⟨SMulMemClass.smul_mem _ (add_mem hbA (star_mem hbA)), ?_⟩, ?_⟩
  · unfold IsSelfAdjoint
    rw [star_smul, star_add, star_star, add_comm]
    norm_num
  · have hxa : x - (2⁻¹ : ℂ) • (b + star b) = (2⁻¹ : ℂ) • ((x - b) + (x - star b)) := by
      module
    have hterm : ∀ i, (inner ℂ (w i) ((x - (2⁻¹ : ℂ) • (b + star b)) (v i)) : ℂ)
        = (2⁻¹ : ℂ) * ((inner ℂ (w i) ((x - b) (v i)) : ℂ)
            + (inner ℂ ((x - b) (w i)) (v i) : ℂ)) := by
      intro i
      rw [hxa]
      have h2 : (inner ℂ (w i) ((x - star b) (v i)) : ℂ) = inner ℂ ((x - b) (w i)) (v i) := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        congr 1
        rw [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_star, hsa.star_eq]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        inner_smul_right, inner_add_right, h2]
    calc ‖∑ i, (inner ℂ (w i) ((x - (2⁻¹ : ℂ) • (b + star b)) (v i)) : ℂ)‖
        ≤ ∑ i, ‖(inner ℂ (w i) ((x - (2⁻¹ : ℂ) • (b + star b)) (v i)) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i, (δ / 2) * (‖v i‖ + ‖w i‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hterm i]
          have e1 : ‖(inner ℂ (w i) ((x - b) (v i)) : ℂ)‖ ≤ ‖w i‖ * δ :=
            le_trans (norm_inner_le_norm _ _)
              (mul_le_mul_of_nonneg_left (le_of_lt (hbv i)) (norm_nonneg _))
          have e2 : ‖(inner ℂ ((x - b) (w i)) (v i) : ℂ)‖ ≤ δ * ‖v i‖ :=
            le_trans (norm_inner_le_norm _ _)
              (mul_le_mul_of_nonneg_right (le_of_lt (hbw i)) (norm_nonneg _))
          have e3 := norm_add_le (inner ℂ (w i) ((x - b) (v i)) : ℂ)
            (inner ℂ ((x - b) (w i)) (v i) : ℂ)
          rw [norm_mul]
          have e4 : ‖(2⁻¹ : ℂ)‖ = 1 / 2 := by norm_num
          rw [e4]
          nlinarith [norm_nonneg ((inner ℂ (w i) ((x - b) (v i)) : ℂ)
            + (inner ℂ ((x - b) (w i)) (v i) : ℂ))]
      _ = (δ / 2) * ∑ i, (‖v i‖ + ‖w i‖) := by rw [Finset.mul_sum]
      _ < ε := by
          have hsum : ∑ i, (‖v i‖ + ‖w i‖) = N - 1 := by rw [hN]; ring
          rw [hsum, hδ]
          have hEq : ε / N * N = ε := by field_simp
          nlinarith [hNpos, hε]

end SelfAdjointStep

/-! ## Step 3 — the transform `b ↦ 2 b (1 + b²)⁻¹` -/

section Transform

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The resolvent `(1 + b²)⁻¹`. -/
noncomputable def res (b : H →L[ℂ] H) : H →L[ℂ] H := Ring.inverse (1 + b * b)

/-- The Cayley-type transform `2 b (1 + b²)⁻¹`, which maps self-adjoint operators into the
self-adjoint unit ball. -/
noncomputable def kap (b : H →L[ℂ] H) : H →L[ℂ] H := (2 : ℂ) • (b * res b)

theorem inner_selfAdjoint {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (x y : H) :
    (inner ℂ x (b y) : ℂ) = inner ℂ (b x) y := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  rw [← ContinuousLinearMap.star_eq_adjoint, hb.star_eq]

theorem re_inner_selfAdjoint_sq {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (x : H) :
    RCLike.re (inner ℂ x (b (b x)) : ℂ) = ‖b x‖ ^ 2 := by
  rw [inner_selfAdjoint hb, inner_self_eq_norm_sq]

/-- `1 + b²` is bounded below by `1` on self-adjoint `b`. -/
theorem norm_le_norm_one_add_sq_apply {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (x : H) :
    ‖x‖ ≤ ‖(1 + b * b) x‖ := by
  have h1 : RCLike.re (inner ℂ x ((1 + b * b) x) : ℂ) = ‖x‖ ^ 2 + ‖b x‖ ^ 2 := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply, inner_add_right, map_add, re_inner_selfAdjoint_sq hb,
      inner_self_eq_norm_sq]
  have h2 : RCLike.re (inner ℂ x ((1 + b * b) x) : ℂ) ≤ ‖x‖ * ‖(1 + b * b) x‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; positivity
  · nlinarith [sq_nonneg ‖b x‖]

/-- The bound `2‖b x‖ ≤ ‖(1 + b²) x‖`, which makes `2 b (1+b²)⁻¹` a contraction. -/
theorem two_norm_apply_le_norm_one_add_sq_apply {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (x : H) :
    2 * ‖b x‖ ≤ ‖(1 + b * b) x‖ := by
  have hexp : ‖(1 + b * b) x‖ ^ 2 = ‖x‖ ^ 2 + 2 * ‖b x‖ ^ 2 + ‖b (b x)‖ ^ 2 := by
    have hx : (1 + b * b) x = x + b (b x) := by simp [ContinuousLinearMap.add_apply]
    rw [hx, @norm_add_sq ℂ, re_inner_selfAdjoint_sq hb]
  have hcs : ‖b x‖ ^ 2 ≤ ‖x‖ * ‖b (b x)‖ := by
    calc ‖b x‖ ^ 2 = RCLike.re (inner ℂ x (b (b x)) : ℂ) := (re_inner_selfAdjoint_sq hb x).symm
      _ ≤ ‖(inner ℂ x (b (b x)) : ℂ)‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖b (b x)‖ := norm_inner_le_norm _ _
  nlinarith [sq_nonneg (‖x‖ - ‖b (b x)‖), norm_nonneg ((1 + b * b) x), norm_nonneg (b x)]

/-- For self-adjoint `b`, the operator `1 + b²` is invertible. -/
theorem isUnit_one_add_sq {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : IsUnit (1 + b * b) := by
  classical
  have hb' : star b * b = b * b := by rw [hb.star_eq]
  rw [← hb', ← spectrum.zero_notMem_iff ℝ]
  intro h0
  have h1 : (0 : ℝ) ∈ ({(1 : ℝ)} : Set ℝ) + spectrum ℝ (star b * b) := by
    rw [spectrum.singleton_add_eq]
    simpa using h0
  obtain ⟨u, hu, s, hs, hsum⟩ := h1
  have hs0 : 0 ≤ s := spectrum_star_mul_self_nonneg s hs
  simp only [Set.mem_singleton_iff] at hu
  subst hu
  linarith

theorem res_mul_cancel {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : res b * (1 + b * b) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_add_sq hb)

theorem mul_res_cancel {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : (1 + b * b) * res b = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_add_sq hb)

theorem commute_res {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : b * res b = res b * b := by
  have h1 := res_mul_cancel hb
  have h2 := mul_res_cancel hb
  calc b * res b = (res b * (1 + b * b)) * (b * res b) := by rw [h1, one_mul]
    _ = res b * ((1 + b * b) * b) * res b := by noncomm_ring
    _ = res b * (b * (1 + b * b)) * res b := by noncomm_ring
    _ = res b * b * ((1 + b * b) * res b) := by noncomm_ring
    _ = res b * b := by rw [h2, mul_one]

theorem commute_res_apply {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (z : H) :
    res b (b z) = b (res b z) := by
  have := congrArg (fun t : H →L[ℂ] H => t z) (commute_res hb)
  simpa [ContinuousLinearMap.mul_apply] using this.symm

theorem res_isSelfAdjoint {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : IsSelfAdjoint (res b) := by
  have h : star (1 + b * b) = 1 + b * b := by
    rw [star_add, star_one, star_mul, hb.star_eq]
  unfold IsSelfAdjoint res
  rw [← Ring.inverse_star, h]

/-- `‖(1 + b²)⁻¹ ξ‖ ≤ ‖ξ‖`. -/
theorem norm_res_apply_le {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (ξ : H) :
    ‖res b ξ‖ ≤ ‖ξ‖ := by
  have h : (1 + b * b) (res b ξ) = ξ := by
    have := congrArg (fun t : H →L[ℂ] H => t ξ) (mul_res_cancel hb)
    simpa [ContinuousLinearMap.mul_apply] using this
  have := norm_le_norm_one_add_sq_apply hb (res b ξ)
  rwa [h] at this

/-- `‖b (1 + b²)⁻¹ ξ‖ ≤ ‖ξ‖ / 2`. -/
theorem norm_mul_res_apply_le {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (ξ : H) :
    ‖b (res b ξ)‖ ≤ ‖ξ‖ / 2 := by
  have h : (1 + b * b) (res b ξ) = ξ := by
    have := congrArg (fun t : H →L[ℂ] H => t ξ) (mul_res_cancel hb)
    simpa [ContinuousLinearMap.mul_apply] using this
  have := two_norm_apply_le_norm_one_add_sq_apply hb (res b ξ)
  rw [h] at this
  linarith

theorem kap_isSelfAdjoint {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : IsSelfAdjoint (kap b) := by
  have hr := res_isSelfAdjoint hb
  unfold IsSelfAdjoint kap
  rw [star_smul, star_mul, hr.star_eq, hb.star_eq, ← commute_res hb]
  norm_num

theorem norm_kap_le_one {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) : ‖kap b‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
  have h : (kap b) ξ = (2 : ℂ) • (b (res b ξ)) := by
    simp [kap]
  rw [h, norm_smul]
  have := norm_mul_res_apply_le hb ξ
  simp only [Complex.norm_ofNat]
  linarith

theorem res_mem {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (hbA : b ∈ A) : res b ∈ A := by
  haveI : IsClosed (A : Set (H →L[ℂ] H)) := hA
  have ht : (1 : H →L[ℂ] H) + b * b ∈ A := add_mem A.one_mem (mul_mem hbA hbA)
  have h : IsUnit (⟨1 + b * b, ht⟩ : A) :=
    A.coe_isUnit.mp (by simpa using isUnit_one_add_sq hb)
  obtain ⟨u, hu'⟩ := h
  set v : A := ((u⁻¹ : Aˣ) : A) with hv
  have h1 : (1 + b * b) * ((v : A) : H →L[ℂ] H) = 1 := by
    have := congrArg (fun z : A => (z : H →L[ℂ] H)) u.mul_inv
    simpa [hu', hv] using this
  have h2 : ((v : A) : H →L[ℂ] H) * (1 + b * b) = 1 := by
    have := congrArg (fun z : A => (z : H →L[ℂ] H)) u.inv_mul
    simpa [hu', hv] using this
  have hEq : res b = ((v : A) : H →L[ℂ] H) := by
    have := Ring.inverse_unit (⟨1 + b * b, ((v : A) : H →L[ℂ] H), h1, h2⟩ : (H →L[ℂ] H)ˣ)
    simpa [res] using this
  rw [hEq]
  exact v.2

theorem kap_mem {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    {b : H →L[ℂ] H} (hb : IsSelfAdjoint b) (hbA : b ∈ A) : kap b ∈ A := by
  exact SMulMemClass.smul_mem (2 : ℂ) (mul_mem hbA (res_mem hA hb hbA))

/-- The algebraic identity underlying strong continuity of `kap`. -/
theorem kap_sub_eq {b y : H →L[ℂ] H} (hb : IsSelfAdjoint b) (hy : IsSelfAdjoint y) :
    kap b - kap y
      = (2 : ℂ) • (res b * (b - y) * res y + res b * b * (y - b) * y * res y) := by
  have hrb := res_mul_cancel hb
  have hry := mul_res_cancel hy
  have key : res b * (b - y) * res y + res b * b * (y - b) * y * res y
      = res b * b * ((1 + y * y) * res y) - (res b * (1 + b * b)) * (y * res y) := by
    noncomm_ring
  rw [key, hrb, hry, mul_one, one_mul, kap, kap, commute_res hb, smul_sub]

/-- **Strong continuity of the transform.**  The pointwise estimate that makes `kap` strongly
continuous on self-adjoint operators, with no uniform bound required. -/
theorem kap_sub_apply_bound {b y : H →L[ℂ] H} (hb : IsSelfAdjoint b) (hy : IsSelfAdjoint y)
    (ξ : H) :
    ‖(kap b - kap y) ξ‖ ≤ 2 * ‖(b - y) (res y ξ)‖ + ‖(b - y) (y (res y ξ))‖ := by
  set u : H := (b - y) (res y ξ) with hu
  set w : H := (b - y) (y (res y ξ)) with hw
  have happ : (kap b - kap y) ξ = (2 : ℂ) • (res b u + b (res b (-w))) := by
    rw [kap_sub_eq hb hy]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, hu, hw, ← commute_res_apply hb]
    congr 2
    congr 1
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [happ]
  have h1 : ‖res b u‖ ≤ ‖u‖ := norm_res_apply_le hb u
  have h2 : ‖b (res b (-w))‖ ≤ ‖w‖ / 2 := by simpa using norm_mul_res_apply_le hb (-w)
  calc ‖(2 : ℂ) • (res b u + b (res b (-w)))‖ = 2 * ‖res b u + b (res b (-w))‖ := by
        rw [norm_smul]; simp
    _ ≤ 2 * (‖res b u‖ + ‖b (res b (-w))‖) := by
        have := norm_add_le (res b u) (b (res b (-w))); linarith
    _ ≤ 2 * (‖u‖ + ‖w‖ / 2) := by linarith
    _ = 2 * ‖u‖ + ‖w‖ := by ring

/-- The real function `t ↦ t / (1 + √(1 - t²))` inverting `t ↦ 2t/(1+t²)` on `[-1,1]`. -/
noncomputable def kapInv (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t ^ 2))

theorem continuous_kapInv : Continuous kapInv := by
  apply Continuous.div continuous_id
  · exact continuous_const.add (Real.continuous_sqrt.comp (by fun_prop))
  · intro t
    have := Real.sqrt_nonneg (1 - t ^ 2)
    linarith

theorem kapInv_spec {t : ℝ} (ht : |t| ≤ 1) : (1 + kapInv t ^ 2) * t = 2 * kapInv t := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  set s := Real.sqrt (1 - t ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  have hne : 1 + s ≠ 0 := by linarith
  have key : (1 + s) ^ 2 + t ^ 2 = 2 * (1 + s) := by nlinarith [hs2]
  unfold kapInv
  rw [← hs]
  field_simp
  linear_combination t * key

end Transform


/-! ## Step 4 — the self-adjoint unit ball -/

section SelfAdjointBall

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Self-adjoint unit-ball Kaplansky density.**  Every self-adjoint element of norm at most one
in the bicommutant `A''` lies in the strong-operator closure of the self-adjoint unit ball
of the C⋆-algebra `A`. -/
theorem selfAdjoint_ball_mem_strongClosure {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint x) (hx1 : ‖x‖ ≤ 1) :
    x ∈ strongClosure {a : H →L[ℂ] H | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1} := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hx0 : x = 0 := by ext ξ; exact Subsingleton.elim _ _
    refine subset_strongClosure _ ?_
    refine ⟨hx0 ▸ zero_mem A, ?_, ?_⟩ <;> simp [hx0, IsSelfAdjoint]
  · obtain ⟨y, hy⟩ : ∃ y : H →L[ℂ] H, y = cfc kapInv x := ⟨_, rfl⟩
    have hysa : IsSelfAdjoint y := hy ▸ cfc_predicate _ _
    have habs : ∀ t ∈ spectrum ℝ x, |t| ≤ 1 := by
      intro t ht
      have h := spectrum.norm_le_norm_of_mem ht
      simp only [Real.norm_eq_abs] at h
      linarith
    have hc : ContinuousOn kapInv (spectrum ℝ x) := continuous_kapInv.continuousOn
    have hkey : (1 + y * y) * x = y + y := by
      have hc2 : ContinuousOn (fun t => 1 + kapInv t * kapInv t) (spectrum ℝ x) :=
        continuousOn_const.add (hc.mul hc)
      have hcid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ x) := continuousOn_id
      have e1 : cfc (fun t => (1 + kapInv t * kapInv t) * t) x
          = (1 + cfc kapInv x * cfc kapInv x) * x := by
        rw [cfc_mul _ _ x hc2 hcid, cfc_id' ℝ x]
        congr 1
        rw [cfc_add x (fun _ => (1 : ℝ)) (fun t => kapInv t * kapInv t) continuousOn_const
            (hc.mul hc), cfc_mul _ _ x hc hc, cfc_const (1 : ℝ) x]
        simp
      have e2 : cfc (fun t => kapInv t + kapInv t) x = cfc kapInv x + cfc kapInv x :=
        cfc_add x _ _ hc hc
      rw [hy, ← e1, ← e2]
      refine cfc_congr fun t ht => ?_
      have h := kapInv_spec (habs t ht)
      nlinarith [h]
    have hxk : x = kap y := by
      have h : res y * ((1 + y * y) * x) = res y * (y + y) := by rw [hkey]
      rw [← mul_assoc, res_mul_cancel hysa, one_mul] at h
      rw [h, kap, mul_add, ← commute_res hysa, two_smul]
    have hyM : y ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
      intro c hc'
      rw [hy]
      exact ((Commute.cfc_real (hx c hc').symm kapInv).symm : c * cfc kapInv x = _)
    refine mem_strongClosure_of_approx fun F ε hε => ?_
    set δ : ℝ := ε / 3 with hδ
    have hδpos : 0 < δ := by positivity
    set F' : Finset H := F.image (res y) ∪ F.image (fun ξ => y (res y ξ)) with hF'
    obtain ⟨b, ⟨hbA, hbsa⟩, hb⟩ :=
      approx_of_mem_strongClosure (selfAdjoint_mem_strongClosure hyM hysa) F' δ hδpos
    refine ⟨kap b, ⟨kap_mem hA hbsa hbA, kap_isSelfAdjoint hbsa, norm_kap_le_one hbsa⟩, ?_⟩
    intro ξ hξ
    have h1 : ‖(b - y) (res y ξ)‖ < δ := by
      have hmem : res y ξ ∈ F' := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hξ)
      have hbb := hb _ hmem
      have heq : (b - y) (res y ξ) = -(y (res y ξ) - b (res y ξ)) := by
        simp [ContinuousLinearMap.sub_apply]
      rw [heq, norm_neg]
      exact hbb
    have h2 : ‖(b - y) (y (res y ξ))‖ < δ := by
      have hmem : y (res y ξ) ∈ F' := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hξ)
      have hbb := hb _ hmem
      have heq : (b - y) (y (res y ξ)) = -(y (y (res y ξ)) - b (y (res y ξ))) := by
        simp [ContinuousLinearMap.sub_apply]
      rw [heq, norm_neg]
      exact hbb
    have hbound := kap_sub_apply_bound hbsa hysa ξ
    have hrw : x ξ - (kap b) ξ = -((kap b - kap y) ξ) := by
      rw [hxk]
      simp [ContinuousLinearMap.sub_apply]
    rw [hrw, norm_neg]
    calc ‖(kap b - kap y) ξ‖ ≤ 2 * ‖(b - y) (res y ξ)‖ + ‖(b - y) (y (res y ξ))‖ := hbound
      _ < 2 * δ + δ := by linarith
      _ = ε := by rw [hδ]; ring

end SelfAdjointBall

/-! ## Step 5 — the `2 × 2` matrix algebra and the general unit ball -/

section Matrix

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- An operator on `H^n` is determined by its matrix entries. -/
theorem ampEntry_sum_apply {n : ℕ} (S : Amp H n →L[ℂ] Amp H n) (x : Amp H n) (i : Fin n) :
    (S x) i = ∑ j, ampEntry n S i j (x j) := by
  classical
  conv_lhs => rw [← sum_ampIn n x]
  rw [map_sum, amp_sum_apply]
  rfl

omit [CompleteSpace H] in
theorem ampEntry_ext {n : ℕ} {S T : Amp H n →L[ℂ] Amp H n}
    (h : ∀ i j, ampEntry n S i j = ampEntry n T i j) : S = T := by
  ext x i
  rw [ampEntry_sum_apply, ampEntry_sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [h i j]

omit [CompleteSpace H] in
theorem norm_ampIn_le {n : ℕ} (j : Fin n) (y : H) : ‖ampIn n j y‖ ≤ ‖y‖ := by
  classical
  rw [PiLp.norm_eq_of_L2]
  have hsum : ∑ i, ‖(ampIn n j y).ofLp i‖ ^ 2 = ‖y‖ ^ 2 := by
    simp only [ampIn_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro h; simp at h
  rw [hsum]
  exact le_of_eq (Real.sqrt_sq (norm_nonneg y))

omit [CompleteSpace H] in
theorem norm_ampEntry_le {n : ℕ} (S : Amp H n →L[ℂ] Amp H n) (i j : Fin n) :
    ‖ampEntry n S i j‖ ≤ ‖S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun y => ?_
  rw [ampEntry_apply]
  calc ‖(S (ampIn n j y)) i‖ ≤ ‖S (ampIn n j y)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖S‖ * ‖ampIn n j y‖ := S.le_opNorm _
    _ ≤ ‖S‖ * ‖y‖ := mul_le_mul_of_nonneg_left (norm_ampIn_le j y) (norm_nonneg S)

omit [CompleteSpace H] in
theorem inner_ampIn {n : ℕ} (i : Fin n) (z : H) (u : Amp H n) :
    (inner ℂ (ampIn n i z) u : ℂ) = inner ℂ z (u i) := by
  classical
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [ampIn_apply, hb]
  · intro h; simp at h

omit [CompleteSpace H] in
theorem inner_ampIn_right {n : ℕ} (i : Fin n) (z : H) (u : Amp H n) :
    (inner ℂ u (ampIn n i z) : ℂ) = inner ℂ (u i) z := by
  rw [← inner_conj_symm, inner_ampIn, inner_conj_symm]

omit [CompleteSpace H] in
theorem ampEntry_mul {n : ℕ} (S T : Amp H n →L[ℂ] Amp H n) (i j : Fin n) :
    ampEntry n (S * T) i j = ∑ k, ampEntry n S i k * ampEntry n T k j := by
  ext y
  rw [ampEntry_apply]
  simp only [ContinuousLinearMap.mul_apply]
  rw [ampEntry_sum_apply S (T (ampIn n j y)) i]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.mul_apply]
  rfl

theorem ampEntry_star {n : ℕ} (S : Amp H n →L[ℂ] Amp H n) (i j : Fin n) :
    ampEntry n (star S) i j = star (ampEntry n S j i) := by
  ext y
  refine ext_inner_left ℂ fun z => ?_
  rw [ampEntry_apply, ← inner_ampIn, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_ampIn_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ampEntry_apply]

omit [CompleteSpace H] in
theorem ampEntry_ampOp (n : ℕ) (a : H →L[ℂ] H) (i j : Fin n) :
    ampEntry n (ampOp n a) i j = if i = j then a else 0 := by
  classical
  ext y
  rw [ampEntry_apply, ampOp_apply, ampIn_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

omit [CompleteSpace H] in
theorem ampEntry_add {n : ℕ} (S T : Amp H n →L[ℂ] Amp H n) (i j : Fin n) :
    ampEntry n (S + T) i j = ampEntry n S i j + ampEntry n T i j := rfl

omit [CompleteSpace H] in
theorem ampEntry_smul {n : ℕ} (c : ℂ) (S : Amp H n →L[ℂ] Amp H n) (i j : Fin n) :
    ampEntry n (c • S) i j = c • ampEntry n S i j := rfl

omit [CompleteSpace H] in
theorem ampEntry_zero {n : ℕ} (i j : Fin n) : ampEntry n (0 : Amp H n →L[ℂ] Amp H n) i j = 0 :=
  rfl

/-- The operator on `H^n` with prescribed matrix entries. -/
noncomputable def ampMat (n : ℕ) (m : Fin n → Fin n → (H →L[ℂ] H)) : Amp H n →L[ℂ] Amp H n :=
  ∑ i, ∑ j, (ampIn n i) ∘L (m i j) ∘L (PiLp.proj 2 (fun _ : Fin n => H) j)

omit [CompleteSpace H] in
theorem ampMat_apply (n : ℕ) (m : Fin n → Fin n → (H →L[ℂ] H)) (u : Amp H n) (k : Fin n) :
    (ampMat n m u) k = ∑ j, m k j (u j) := by
  classical
  simp only [ampMat, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [amp_sum_apply, Finset.sum_eq_single k]
  · rw [amp_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ampIn_apply]
  · intro i _ hik
    rw [amp_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [ampIn_apply, hik]
  · intro h; simp at h

omit [CompleteSpace H] in
theorem ampEntry_ampMat (n : ℕ) (m : Fin n → Fin n → (H →L[ℂ] H)) (i j : Fin n) :
    ampEntry n (ampMat n m) i j = m i j := by
  classical
  ext y
  rw [ampEntry_apply, ampMat_apply, Finset.sum_eq_single j]
  · simp [ampIn_apply]
  · intro b _ hb; simp [ampIn_apply, hb]
  · intro h; simp at h

/-- The `n × n` matrix algebra over `A`, as a star subalgebra of `B(H^n)`. -/
noncomputable def matAlg (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (Amp H n →L[ℂ] Amp H n) where
  carrier := {S | ∀ i j, ampEntry n S i j ∈ A}
  mul_mem' := by
    intro S T hS hT i j
    rw [ampEntry_mul]
    exact sum_mem fun k _ => mul_mem (hS i k) (hT k j)
  one_mem' := by
    intro i j
    rw [show (1 : Amp H n →L[ℂ] Amp H n) = ampOp n 1 from (ampOp_one n).symm, ampEntry_ampOp]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  add_mem' := fun hS hT i j => add_mem (hS i j) (hT i j)
  zero_mem' := fun _ _ => zero_mem A
  algebraMap_mem' := by
    intro r i j
    rw [Algebra.algebraMap_eq_smul_one, show ((r : ℂ) • (1 : Amp H n →L[ℂ] Amp H n))
      = r • ampOp n 1 from by rw [ampOp_one]]
    show r • ampEntry n (ampOp n 1) i j ∈ A
    rw [ampEntry_ampOp]
    split_ifs
    · exact SMulMemClass.smul_mem _ (one_mem A)
    · exact SMulMemClass.smul_mem _ (zero_mem A)
  star_mem' := by
    intro S hS i j
    rw [ampEntry_star]
    exact star_mem (hS j i)

theorem mem_matAlg {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)} {S : Amp H n →L[ℂ] Amp H n} :
    S ∈ matAlg n A ↔ ∀ i j, ampEntry n S i j ∈ A := Iff.rfl

theorem ampOp_mem_matAlg {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)} {a : H →L[ℂ] H}
    (ha : a ∈ A) : ampOp n a ∈ matAlg n A := by
  intro i j
  rw [ampEntry_ampOp]
  split_ifs
  · exact ha
  · exact zero_mem A

theorem isClosed_matAlg {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) :
    IsClosed ((matAlg n A : StarSubalgebra ℂ (Amp H n →L[ℂ] Amp H n)) :
      Set (Amp H n →L[ℂ] Amp H n)) := by
  have hset : ((matAlg n A : StarSubalgebra ℂ (Amp H n →L[ℂ] Amp H n)) :
      Set (Amp H n →L[ℂ] Amp H n))
      = ⋂ i : Fin n, ⋂ j : Fin n, (fun S => ampEntry n S i j) ⁻¹' (A : Set (H →L[ℂ] H)) := by
    ext S
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact Iff.rfl
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.preimage ?_ hA
  have hlip : LipschitzWith 1 (fun S : Amp H n →L[ℂ] Amp H n => ampEntry n S i j) := by
    refine LipschitzWith.of_dist_le_mul fun S T => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : ampEntry n S i j - ampEntry n T i j = ampEntry n (S - T) i j := rfl
    rw [hsub]
    simp only [NNReal.coe_one, one_mul]
    exact norm_ampEntry_le (S - T) i j
  exact hlip.continuous

/-- Elements of the commutant of the matrix algebra are diagonal amplifications of elements of
the commutant of `A`. -/
theorem eq_ampOp_of_mem_centralizer_matAlg {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {T : Amp H 2 →L[ℂ] Amp H 2}
    (hT : T ∈ Set.centralizer ((matAlg 2 A : StarSubalgebra ℂ (Amp H 2 →L[ℂ] Amp H 2)) :
      Set (Amp H 2 →L[ℂ] Amp H 2))) :
    ∃ c ∈ Set.centralizer (A : Set (H →L[ℂ] H)), T = ampOp 2 c := by
  classical
  set U : Fin 2 → Fin 2 → (Amp H 2 →L[ℂ] Amp H 2) :=
    fun k l => ampMat 2 (fun i j => if i = k ∧ j = l then 1 else 0) with hU
  have hUmem : ∀ k l, U k l ∈ matAlg 2 A := by
    intro k l i j
    rw [hU]
    simp only
    rw [ampEntry_ampMat]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  have hE : ∀ k l i j,
      (∑ m, ampEntry 2 T i m * (if m = k ∧ j = l then (1 : H →L[ℂ] H) else 0))
        = ∑ m, (if i = k ∧ m = l then (1 : H →L[ℂ] H) else 0) * ampEntry 2 T m j := by
    intro k l i j
    have h0 := hT _ (hUmem k l)
    have h1 := congrArg (fun S => ampEntry 2 S i j) h0
    simp only [ampEntry_mul, hU, ampEntry_ampMat] at h1
    exact h1.symm
  have h01 : ampEntry 2 T 0 1 = 0 := by
    have h := hE 0 0 0 1
    simp at h
    exact h.symm
  have h10 : ampEntry 2 T 1 0 = 0 := by
    have h := hE 0 0 1 0
    simp at h
    exact h
  have h0011 : ampEntry 2 T 0 0 = ampEntry 2 T 1 1 := by
    have h := hE 0 1 0 1
    simp at h
    exact h
  refine ⟨ampEntry 2 T 0 0, ?_, ?_⟩
  · refine ampEntry_mem_centralizer (A := (A : Set (H →L[ℂ] H))) (S := T) ?_ 0 0
    exact fun a ha => (hT (ampOp 2 a) (ampOp_mem_matAlg ha)).symm
  · refine ampEntry_ext fun i j => ?_
    rw [ampEntry_ampOp]
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h0011]

/-- The off-diagonal self-adjoint `2 × 2` matrix built from `x`. -/
noncomputable def offDiag (x : H →L[ℂ] H) : Amp H 2 →L[ℂ] Amp H 2 :=
  ampMat 2 (fun i j => if i = 0 ∧ j = 1 then x else if i = 1 ∧ j = 0 then star x else 0)

theorem offDiag_apply_zero (x : H →L[ℂ] H) (u : Amp H 2) : (offDiag x u) 0 = x (u 1) := by
  rw [offDiag, ampMat_apply, Fin.sum_univ_two]; simp

theorem offDiag_isSelfAdjoint (x : H →L[ℂ] H) : IsSelfAdjoint (offDiag x) := by
  unfold IsSelfAdjoint
  refine ampEntry_ext fun i j => ?_
  rw [ampEntry_star, offDiag, ampEntry_ampMat, ampEntry_ampMat]
  fin_cases i <;> fin_cases j <;> simp

omit [CompleteSpace H] in
theorem norm_amp_two_sq (u : Amp H 2) : ‖u‖ ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := by
  rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (by positivity), Fin.sum_univ_two]

theorem norm_offDiag_le (x : H →L[ℂ] H) : ‖offDiag x‖ ≤ ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun u => ?_
  have h0 : (offDiag x u) 0 = x (u 1) := by
    rw [offDiag, ampMat_apply, Fin.sum_univ_two]; simp
  have h1 : (offDiag x u) 1 = (star x) (u 0) := by
    rw [offDiag, ampMat_apply, Fin.sum_univ_two]; simp
  have hu := norm_amp_two_sq u
  have hsq : ‖offDiag x u‖ ^ 2 ≤ (‖x‖ * ‖u‖) ^ 2 := by
    rw [norm_amp_two_sq, h0, h1, mul_pow, hu]
    have e1 : ‖x (u 1)‖ ≤ ‖x‖ * ‖u 1‖ := x.le_opNorm _
    have e2 : ‖(star x) (u 0)‖ ≤ ‖x‖ * ‖u 0‖ := by
      have h := (star x).le_opNorm (u 0)
      rwa [norm_star] at h
    nlinarith [norm_nonneg (x (u 1)), norm_nonneg ((star x) (u 0)), norm_nonneg (u 0),
      norm_nonneg (u 1), norm_nonneg x]
  nlinarith [norm_nonneg (offDiag x u), mul_nonneg (norm_nonneg x) (norm_nonneg u)]

theorem offDiag_mem_bicommutant {A : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    offDiag x ∈ Set.centralizer (Set.centralizer
      ((matAlg 2 A : StarSubalgebra ℂ (Amp H 2 →L[ℂ] Amp H 2)) :
        Set (Amp H 2 →L[ℂ] Amp H 2))) := by
  classical
  have hxs : star x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) :=
    star_mem_centralizer_centralizer (fun a ha => star_mem ha) hx
  intro T hT
  obtain ⟨c, hc, rfl⟩ := eq_ampOp_of_mem_centralizer_matAlg hT
  have hcx : c * x = x * c := hx c hc
  have hcxs : c * star x = star x * c := hxs c hc
  refine ampEntry_ext fun i j => ?_
  rw [ampEntry_mul, ampEntry_mul]
  simp only [ampEntry_ampOp, offDiag, ampEntry_ampMat, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [hcx, hcxs]

end Matrix


/-! ## The Kaplansky density theorem -/

section Main

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Kaplansky density theorem, unit-ball form.**  For a norm-closed unital star subalgebra
`A ⊆ B(H)` with bicommutant `M = A''`, the closed unit ball of `A` is strong-operator dense in
the closed unit ball of `M`.

The self-adjointness restriction of `selfAdjoint_ball_mem_strongClosure` is removed by the
`2 × 2` matrix trick: the self-adjoint contraction `[[0, x], [x*, 0]]` lies in the bicommutant of
the matrix algebra `M₂(A)`, and its `(0,1)` entry is an element of the unit ball of `A`
approximating `x`. -/
theorem ball_mem_strongClosure {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) (hx1 : ‖x‖ ≤ 1) :
    x ∈ strongClosure {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ 1} := by
  classical
  refine mem_strongClosure_of_approx fun F ε hε => ?_
  have hX := selfAdjoint_ball_mem_strongClosure (isClosed_matAlg hA)
    (offDiag_mem_bicommutant hx) (offDiag_isSelfAdjoint x)
    (le_trans (norm_offDiag_le x) hx1)
  obtain ⟨S, ⟨hSmem, hSsa, hSnorm⟩, hS⟩ :=
    approx_of_mem_strongClosure hX (F.image (ampIn 2 1)) ε hε
  refine ⟨ampEntry 2 S 0 1, ⟨hSmem 0 1, le_trans (norm_ampEntry_le S 0 1) hSnorm⟩, ?_⟩
  intro ξ hξ
  have hmem : ampIn 2 1 ξ ∈ F.image (ampIn 2 1) := Finset.mem_image_of_mem _ hξ
  have h := hS _ hmem
  have hc : (offDiag x (ampIn 2 1 ξ) - S (ampIn 2 1 ξ)) 0 = x ξ - ampEntry 2 S 0 1 ξ := by
    rw [amp_sub_apply, offDiag_apply_zero, ampEntry_apply]
    congr 2
  calc ‖x ξ - ampEntry 2 S 0 1 ξ‖
      = ‖(offDiag x (ampIn 2 1 ξ) - S (ampIn 2 1 ξ)) 0‖ := by rw [hc]
    _ ≤ ‖offDiag x (ampIn 2 1 ξ) - S (ampIn 2 1 ξ)‖ := PiLp.norm_apply_le _ _
    _ < ε := h

/-- **Kaplansky density theorem, scaled norm-bounded form.**  Every `x ∈ A''` with `‖x‖ ≤ c` is
a strong-operator limit of elements of `A` of norm at most `c`. -/
theorem scaled_ball_mem_strongClosure {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) {c : ℝ} (hc : ‖x‖ ≤ c) :
    x ∈ strongClosure {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ c} := by
  classical
  have hc0 : 0 ≤ c := le_trans (norm_nonneg x) hc
  rcases eq_or_lt_of_le hc0 with h0 | hcpos
  · have hx0 : x = 0 := by
      have hle : ‖x‖ ≤ 0 := by rw [← h0] at hc; exact hc
      exact norm_le_zero_iff.1 hle
    refine subset_strongClosure _ ⟨hx0 ▸ zero_mem A, ?_⟩
    rw [hx0]
    simpa using hc0
  · have hxc : ‖((c⁻¹ : ℝ) : ℂ) • x‖ ≤ 1 := by
      rw [norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
      rw [inv_mul_le_iff₀ hcpos]
      simpa using hc
    have hmem : ((c⁻¹ : ℝ) : ℂ) • x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) :=
      smul_mem_centralizer_centralizer _ hx
    have hball := ball_mem_strongClosure hA hmem hxc
    refine mem_strongClosure_of_approx fun F ε hε => ?_
    obtain ⟨a, ⟨haA, ha1⟩, ha⟩ := approx_of_mem_strongClosure hball F (ε / c) (by positivity)
    refine ⟨((c : ℝ) : ℂ) • a, ⟨SMulMemClass.smul_mem _ haA, ?_⟩, ?_⟩
    · rw [norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      nlinarith
    · intro ξ hξ
      have h := ha ξ hξ
      have hrw : x ξ - (((c : ℝ) : ℂ) • a) ξ
          = ((c : ℝ) : ℂ) • ((((c⁻¹ : ℝ) : ℂ) • x) ξ - a ξ) := by
        simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_smul]
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hcpos)]
        simp
      rw [hrw, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      calc c * ‖(((c⁻¹ : ℝ) : ℂ) • x) ξ - a ξ‖ < c * (ε / c) := mul_lt_mul_of_pos_left h hcpos
        _ = ε := by field_simp

/-- Version phrased with the concrete von Neumann algebra `A''` of the bicommutant core. -/
theorem ball_mem_strongClosure_vonNeumannGenerated {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {x : H →L[ℂ] H}
    (hx : x ∈ StarSubalgebra.vonNeumannGenerated A) (hx1 : ‖x‖ ≤ 1) :
    x ∈ strongClosure {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ 1} :=
  ball_mem_strongClosure hA (StarSubalgebra.mem_vonNeumannGenerated_iff.1 hx) hx1

end Main

/-! ## Nets, compressed corners and bounded product convergence -/

section Nets

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Membership in the strong closure of `K` produces a genuine net in `K` converging strongly. -/
theorem exists_net_of_mem_strongClosure {K : Set (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ strongClosure K) :
    ∃ l : Filter K, l.NeBot ∧
      StrongOperator.StronglyTendsto l (fun a : K => (a : H →L[ℂ] H)) x := by
  rw [strongClosure, Set.mem_setOf_eq, mem_closure_iff_nhds] at hx
  refine ⟨Filter.comap (fun a : K => StrongOperator.toSOT (a : H →L[ℂ] H))
    (𝓝 (StrongOperator.toSOT x)), ?_, ?_⟩
  · refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨B, hBt, hBK⟩ := hx t ht
    exact ⟨⟨StrongOperator.ofSOT B, hBK⟩, hBt⟩
  · have h1 : Tendsto (fun a : K => StrongOperator.toSOT (a : H →L[ℂ] H))
        (Filter.comap (fun a : K => StrongOperator.toSOT (a : H →L[ℂ] H))
          (𝓝 (StrongOperator.toSOT x))) (𝓝 (StrongOperator.toSOT x)) := tendsto_comap
    exact StrongOperator.stronglyTendsto_iff_tendsto_sot.2 h1

/-- **Bounded strong approximation net.**  Every `x ∈ M = A''` is the strong limit of a net in
`A` whose norms are bounded by `‖x‖`. -/
theorem exists_bounded_net {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    ∃ l : Filter {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ ‖x‖}, l.NeBot ∧
      StrongOperator.StronglyTendsto l (fun a => (a : H →L[ℂ] H)) x :=
  exists_net_of_mem_strongClosure (scaled_ball_mem_strongClosure hA hx le_rfl)

theorem norm_compress_le {q a x : H →L[ℂ] H} (hq1 : star q = q) (hq2 : q * q = q)
    (ha : ‖a‖ ≤ ‖x‖) : ‖q * a * q‖ ≤ ‖x‖ := by
  have hq := norm_le_one_of_isProjection hq1 hq2
  calc ‖q * a * q‖ ≤ ‖q * a‖ * ‖q‖ := norm_mul_le _ _
    _ ≤ (‖q‖ * ‖a‖) * ‖q‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 :=
        mul_le_mul (mul_le_mul hq ha (norm_nonneg _) zero_le_one) hq (norm_nonneg _)
          (by positivity)
    _ = ‖x‖ := by ring

/-- **Compressed-corner approximation.**  For a projection `q` and `x ∈ M = A''`, the element
`q x q` of the corner `q M q` is the strong limit of the uniformly norm-bounded net `q aᵢ q`
with `aᵢ ∈ A`; the bound is `‖q aᵢ q‖ ≤ ‖x‖`. -/
theorem exists_net_compression {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {q : H →L[ℂ] H} (hq1 : star q = q) (hq2 : q * q = q)
    {x : H →L[ℂ] H} (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    ∃ (l : Filter {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ ‖x‖}), l.NeBot ∧
      (∀ a : {a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ ‖x‖}, ‖q * (a : H →L[ℂ] H) * q‖ ≤ ‖x‖) ∧
      StrongOperator.StronglyTendsto l (fun a => q * (a : H →L[ℂ] H) * q) (q * x * q) := by
  obtain ⟨l, hne, hconv⟩ := exists_bounded_net hA hx
  exact ⟨l, hne, fun a => norm_compress_le hq1 hq2 a.2.2, hconv.compress q q⟩

/-- **Jointly indexed bounded product convergence.**  With the joint index of the manuscript,
`q aᵢ q b_j q → q x q y q` and `q b_j q a_i q → q y q x q` strongly; this is what transports
cyclicity from `q A q` to `q M q`. -/
theorem exists_net_compression_product {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H))) {q : H →L[ℂ] H} (hq1 : star q = q) (hq2 : q * q = q)
    {x y : H →L[ℂ] H} (hx : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hy : y ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    ∃ (l : Filter ({a : H →L[ℂ] H | a ∈ A ∧ ‖a‖ ≤ ‖x‖} ×
        {b : H →L[ℂ] H | b ∈ A ∧ ‖b‖ ≤ ‖y‖})), l.NeBot ∧
      StrongOperator.StronglyTendsto l
        (fun p => (q * (p.1 : H →L[ℂ] H) * q) * (q * (p.2 : H →L[ℂ] H) * q))
        ((q * x * q) * (q * y * q)) ∧
      StrongOperator.StronglyTendsto l
        (fun p => (q * (p.2 : H →L[ℂ] H) * q) * (q * (p.1 : H →L[ℂ] H) * q))
        ((q * y * q) * (q * x * q)) := by
  obtain ⟨l₁, hne₁, hb₁, hc₁⟩ := exists_net_compression hA hq1 hq2 hx
  obtain ⟨l₂, hne₂, hb₂, hc₂⟩ := exists_net_compression hA hq1 hq2 hy
  haveI := hne₁
  haveI := hne₂
  refine ⟨l₁ ×ˢ l₂, inferInstance, ?_, ?_⟩
  · exact StrongOperator.StronglyTendsto.mul_of_bounded (C := ‖x‖) (fun p => hb₁ p.1)
      (fun z => (hc₁ z).comp tendsto_fst) (fun z => (hc₂ z).comp tendsto_snd)
  · exact StrongOperator.StronglyTendsto.mul_of_bounded (C := ‖y‖) (fun p => hb₂ p.2)
      (fun z => (hc₂ z).comp tendsto_snd) (fun z => (hc₁ z).comp tendsto_fst)

end Nets

end KaplanskyDensity
