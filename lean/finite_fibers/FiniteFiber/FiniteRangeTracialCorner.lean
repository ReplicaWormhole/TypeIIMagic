import FiniteFiber.FiniteRangeSupportCornerConstruction

/-!
# Trace and fullness of the finite-range stabilizer corner

This file (FF22) takes the concrete finite-range support-corner package of FF21
(`FiniteFiber.FiniteRangeStabilizerSystem`, its decreasing local code-space
supports `p n = π_ω(P_{Γ_n})` and their canonical strong limit `q`) and proves,
inside an *explicitly supplied* concrete GNS/von-Neumann representation, the
three substantive premises which FF20 (`FiniteFiber.GNSOrbitConditions`) still
had to assume:

1. the support-corner vector functional `τ_q(x) = ⟪Ω, x Ω⟫` is **tracial** and
   **faithful** on `q M q`;
2. the support projection `q` is **nonzero**;
3. the orbit argument makes `q` **full** (central support `1`).

Everything is stated for the concrete operator model: `M` is a
`VonNeumannAlgebra` on the GNS space `W.GNS`, all limits are the explicit
pointwise strong limits of `FiniteFiber.StrongSupport`, and normality is stated
as an exact strong-convergence continuity statement rather than being hidden in
a typeclass.

## Infrastructure developed here

* `FiniteFiber.exists_mem_norm_sub_apply_lt`: a **von Neumann density theorem**
  (the finite-tuple strong approximation form of the bicommutant theorem),
  proved from scratch by the amplification argument.  Mathlib only has the
  tautological `VonNeumannAlgebra.commutant_commutant`.
* the exact normality, positivity and normalization statements for the corner
  vector functional;
* the passage from corner traciality to *full* faithfulness on `q M q`
  (Proposition `prop:faithful` of the manuscript, for arbitrary corner
  elements, not only projections);
* the finite-volume trace-cyclicity identity for the local code projector and
  its strong-limit consequence, i.e. Lemma `lem:finite-trace` of the
  manuscript.

## Hypotheses

For a *general* von Neumann algebra `M` satisfying the FF21 hypothesis `hM`
(`M` contains the represented finite local algebras), traciality on all of
`q M q` uses exactly one further hypothesis, namely that `M` really is the
manuscript's `M_Γ = 𝒰_Γ''`: every element of `M` commutes with every operator
commuting with the represented local algebra
(`QuasilocalStabilizerState.GeneratedByLocalAlgebra`).  This is a *definitional*
identification of `M`, not an analytic gap, and it cannot simply be deleted: for
a strictly larger `M` (for instance all of `B(H)`, which still satisfies `hM`)
the argument below produces the local symmetry only inside the strong closure of
the local algebra, so the vector state on the corner need not be tracial.

For the **canonical** choice `M = M_Γ`, which is the algebra the manuscript
works with, the hypothesis is *discharged*: `Part I'` constructs the bicommutant
of a star subalgebra of `B(H)` as a von Neumann algebra, and
`QuasilocalStabilizerState.localVonNeumannAlgebra` is exactly
`π_ω(𝒜_loc)''`.  Consequently
`FiniteRangeStabilizerSystem.supportCornerConclusion_localVonNeumannAlgebra`
carries *no* hypothesis beyond the FF21 data `R`, `Q`, `W`.

No no-type-III statement is made here; that is FF23.
-/

namespace FiniteFiber

open scoped InnerProductSpace
open Filter Topology

/-! ## Part I. A von Neumann density theorem

Mathlib does not contain the von Neumann bicommutant/density theorem, only the
definitional `VonNeumannAlgebra.commutant_commutant`.  The finite-tuple strong
approximation statement below is proved here by the standard amplification
argument; it is the only nontrivial operator-topological input to the
traciality proof and it replaces the Kaplansky-density step of the manuscript.
-/

section Density

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `n`-fold diagonal amplification of a bounded operator. -/
noncomputable def amplify (n : ℕ) (a : H →L[ℂ] H) :
    (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i => a ∘L PiLp.proj 2 (fun _ : Fin n => H) i)

omit [CompleteSpace H] in
@[simp] lemma amplify_apply (n : ℕ) (a : H →L[ℂ] H)
    (v : PiLp 2 fun _ : Fin n => H) (i : Fin n) : (amplify n a v) i = a (v i) := rfl

/-- The `j`-th coordinate inclusion into the amplified Hilbert space. -/
noncomputable def amplifyInj (n : ℕ) (j : Fin n) : H →L[ℂ] (PiLp 2 fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j

omit [CompleteSpace H] in
lemma amplifyInj_apply (n : ℕ) (j : Fin n) (v : H) (i : Fin n) :
    (amplifyInj n j v) i = if i = j then v else 0 := by
  classical
  simp [amplifyInj, ContinuousLinearMap.single, Pi.single_apply]

omit [CompleteSpace H] in
lemma sum_amplifyInj (n : ℕ) (v : PiLp 2 fun _ : Fin n => H) :
    ∑ j, amplifyInj n j (v j) = v := by
  classical
  ext i
  simp [amplifyInj, ContinuousLinearMap.single, Pi.single_apply]

omit [CompleteSpace H] in
lemma amplify_one (n : ℕ) : amplify n (1 : H →L[ℂ] H) = 1 := by
  ext v i; rfl

omit [CompleteSpace H] in
lemma amplify_zero (n : ℕ) : amplify n (0 : H →L[ℂ] H) = 0 := by
  ext v i; rfl

omit [CompleteSpace H] in
lemma amplify_add (n : ℕ) (a b : H →L[ℂ] H) :
    amplify n (a + b) = amplify n a + amplify n b := by
  ext v i; rfl

omit [CompleteSpace H] in
lemma amplify_smul (n : ℕ) (c : ℂ) (a : H →L[ℂ] H) :
    amplify n (c • a) = c • amplify n a := by
  ext v i; rfl

omit [CompleteSpace H] in
lemma amplify_mul (n : ℕ) (a b : H →L[ℂ] H) :
    amplify n (a * b) = amplify n a * amplify n b := by
  ext v i; rfl

lemma amplify_star (n : ℕ) (a : H →L[ℂ] H) :
    amplify n (star a) = star (amplify n a) := by
  have hinner : ∀ (u v : PiLp 2 fun _ : Fin n => H),
      ⟪amplify n (star a) u, v⟫_ℂ = ⟪u, amplify n a v⟫_ℂ := by
    intro u v
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ⟪star a (u i), v i⟫_ℂ = ⟪u i, a (v i)⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right (𝕜 := ℂ)
  intro v
  rw [hinner u v, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace H] in
lemma amplify_amplifyInj (n : ℕ) (a : H →L[ℂ] H) (j : Fin n) (v : H) :
    amplify n a (amplifyInj n j v) = amplifyInj n j (a v) := by
  classical
  ext i
  rw [amplify_apply, amplifyInj_apply, amplifyInj_apply]
  by_cases h : i = j <;> simp [h]

/-- The `(i,j)` operator entry of an operator on the amplified Hilbert space. -/
noncomputable def amplifyEntry (n : ℕ)
    (T : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H)) (i j : Fin n) :
    H →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i ∘L T ∘L amplifyInj n j

omit [CompleteSpace H] in
lemma amplifyEntry_apply (n : ℕ)
    (T : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H)) (i j : Fin n)
    (v : H) : amplifyEntry n T i j v = (T (amplifyInj n j v)) i := rfl

omit [CompleteSpace H] in
lemma apply_coord_eq_sum_amplifyEntry (n : ℕ)
    (T : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H))
    (v : PiLp 2 fun _ : Fin n => H) (i : Fin n) :
    (T v) i = ∑ j, amplifyEntry n T i j (v j) := by
  conv_lhs => rw [← sum_amplifyInj n v]
  rw [map_sum]
  simp [amplifyEntry_apply]

omit [CompleteSpace H] in
/-- If `T` commutes with the amplification of every element of a set of operators, then all
its operator entries commute with that set. -/
lemma amplifyEntry_commutes (n : ℕ) (𝒜 : Set (H →L[ℂ] H))
    {T : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H)}
    (hT : ∀ a ∈ 𝒜, amplify n a * T = T * amplify n a) (i j : Fin n) :
    ∀ a ∈ 𝒜, a * amplifyEntry n T i j = amplifyEntry n T i j * a := by
  intro a ha
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun S => S (amplifyInj n j v)) (hT a ha)
  simp only at h
  have h' : (amplify n a (T (amplifyInj n j v))) i = (T (amplify n a (amplifyInj n j v))) i :=
    congrArg (fun w : PiLp 2 fun _ : Fin n => H => w i) h
  rw [amplify_apply, amplify_amplifyInj] at h'
  exact h'

omit [CompleteSpace H] in
/-- If every operator entry of `T` commutes with `x`, then `T` commutes with the amplification
of `x`. -/
lemma amplify_commutes_of_amplifyEntry (n : ℕ) {x : H →L[ℂ] H}
    {T : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H)}
    (h : ∀ i j, x * amplifyEntry n T i j = amplifyEntry n T i j * x) :
    amplify n x * T = T * amplify n x := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  show x ((T v) i) = (T (amplify n x v)) i
  rw [apply_coord_eq_sum_amplifyEntry, apply_coord_eq_sum_amplifyEntry, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun S : H →L[ℂ] H => S (v j)) (h i j)

/--
**The von Neumann density theorem, finite-tuple strong form.**  If `x` commutes with every
operator commuting with a unital `*`-subalgebra `𝒜` of `B(H)` — that is, if `x ∈ 𝒜''` — then
`x` is approximated by an element of `𝒜` on any finite tuple of vectors.

This is the operator-topological input which the manuscript obtains from Kaplansky's density
theorem; Mathlib contains neither statement, so it is proved here by amplification.
-/
theorem exists_mem_norm_sub_apply_lt
    (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → x * t = t * x)
    {n : ℕ} (ξ : Fin n → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ 𝒜, ∀ i, ‖x (ξ i) - u (ξ i)‖ < ε := by
  classical
  set Xi : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 ξ with hXi
  have hXi_apply : ∀ i, Xi i = ξ i := fun i => rfl
  let V : Submodule ℂ (PiLp 2 fun _ : Fin n => H) :=
    { carrier := {v | ∃ a ∈ 𝒜, amplify n a Xi = v}
      add_mem' := by
        rintro u v ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, add_mem ha hb, by rw [amplify_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [amplify_zero]; rfl⟩
      smul_mem' := by
        rintro c v ⟨a, ha, rfl⟩
        exact ⟨c • a, SMulMemClass.smul_mem c ha, by rw [amplify_smul]; rfl⟩ }
  set K := V.topologicalClosure with hK
  set P := K.starProjection with hP
  have hinvV : ∀ a ∈ 𝒜, ∀ v ∈ V, amplify n a v ∈ V := by
    rintro a ha v ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, by rw [amplify_mul]; rfl⟩
  have hinvK : ∀ a ∈ 𝒜, ∀ v ∈ K, amplify n a v ∈ K := by
    intro a ha v hv
    have hmap : (V : Set (PiLp 2 fun _ : Fin n => H)) ⊆ (amplify n a) ⁻¹' (K : Set _) :=
      fun w hw => Submodule.le_topologicalClosure V (hinvV a ha w hw)
    have hclosed : IsClosed ((amplify n a) ⁻¹' (K : Set _)) :=
      (V.isClosed_topologicalClosure).preimage (amplify n a).continuous
    have hsub : (K : Set (PiLp 2 fun _ : Fin n => H)) ⊆ (amplify n a) ⁻¹' (K : Set _) := by
      rw [hK, Submodule.topologicalClosure_coe]
      exact closure_minimal hmap hclosed
    exact hsub hv
  have hPcomm : ∀ a ∈ 𝒜, amplify n a * P = P * amplify n a := by
    have key : ∀ a ∈ 𝒜, P * amplify n a * P = amplify n a * P := by
      intro a ha
      apply ContinuousLinearMap.ext
      intro v
      show P (amplify n a (P v)) = amplify n a (P v)
      exact Submodule.starProjection_eq_self_iff.mpr
        (hinvK a ha _ (K.starProjection_apply_mem v))
    intro a ha
    have h1 := key a ha
    have h2 := key (star a) (star_mem ha)
    have hPsa : star P = P := (isSelfAdjoint_starProjection K).star_eq
    have h2' : P * star (amplify n a) * P = star (amplify n a) * P := by
      rw [← amplify_star]; exact h2
    have h3 : P * amplify n a * P = P * amplify n a := by
      have h4 := congrArg star h2'
      simpa [star_mul, hPsa, star_star, mul_assoc] using h4
    rw [← h1, h3]
  have hentry : ∀ i j, x * amplifyEntry n P i j = amplifyEntry n P i j * x := fun i j =>
    hx _ (amplifyEntry_commutes n (𝒜 : Set (H →L[ℂ] H)) hPcomm i j)
  have hxP : amplify n x * P = P * amplify n x := amplify_commutes_of_amplifyEntry n hentry
  have hXiK : Xi ∈ K := by
    refine Submodule.le_topologicalClosure V ⟨1, one_mem _, ?_⟩
    rw [amplify_one]; rfl
  have hPXi : P Xi = Xi := Submodule.starProjection_eq_self_iff.mpr hXiK
  have hxXi : amplify n x Xi ∈ K := by
    have hrw : amplify n x Xi = P (amplify n x Xi) := by
      conv_lhs => rw [← hPXi]
      exact congrArg (fun S : (PiLp 2 fun _ : Fin n => H) →L[ℂ] (PiLp 2 fun _ : Fin n => H) =>
        S Xi) hxP
    rw [hrw]
    exact K.starProjection_apply_mem _
  have hmem : amplify n x Xi ∈ closure (V : Set (PiLp 2 fun _ : Fin n => H)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hxXi
  obtain ⟨w, hwV, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨u, hu, rfl⟩ := hwV
  refine ⟨u, hu, fun i => ?_⟩
  have hcoord : ‖(amplify n x Xi - amplify n u Xi) i‖ ≤ ‖amplify n x Xi - amplify n u Xi‖ :=
    PiLp.norm_apply_le _ _
  have hval : (amplify n x Xi - amplify n u Xi) i = x (ξ i) - u (ξ i) := by
    show (amplify n x Xi) i - (amplify n u Xi) i = _
    rw [amplify_apply, amplify_apply, hXi_apply]
  rw [hval] at hcoord
  calc ‖x (ξ i) - u (ξ i)‖ ≤ ‖amplify n x Xi - amplify n u Xi‖ := hcoord
    _ = dist (amplify n x Xi) (amplify n u Xi) := (dist_eq_norm _ _).symm
    _ < ε := hdist

/-- The two-vector form of the density theorem, which is what the traciality argument uses. -/
theorem exists_mem_norm_sub_apply_lt_two
    (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → x * t = t * x)
    (v w : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ 𝒜, ‖x v - u v‖ < ε ∧ ‖x w - u w‖ < ε := by
  obtain ⟨u, hu, h⟩ := exists_mem_norm_sub_apply_lt 𝒜 hx ![v, w] hε
  exact ⟨u, hu, by simpa using h 0, by simpa using h 1⟩

end Density

/-! ## Part I'. The bicommutant of a star subalgebra as a von Neumann algebra

Mathlib provides `VonNeumannAlgebra.commutant` only for an algebra that is already known to
be a von Neumann algebra.  What the manuscript needs is the algebra `M_Γ = 𝒜''` *generated*
by the represented local algebra, so the bicommutant of an arbitrary star subalgebra of
`B(H)` is constructed here.
-/

section Bicommutant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_centralizer_coe_subset (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    star (Set.centralizer (𝒜 : Set (H →L[ℂ] H)))
      ⊆ Set.centralizer (𝒜 : Set (H →L[ℂ] H)) := by
  intro x hx
  rw [Set.mem_star] at hx
  rw [Set.mem_centralizer_iff]
  intro a ha
  have h := (Set.mem_centralizer_iff.mp hx) (star a) (star_mem ha)
  have := congrArg star h
  simpa [star_mul] using this.symm

theorem centralizer_union_star_centralizer (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Set.centralizer (𝒜 : Set (H →L[ℂ] H)) ∪ star (Set.centralizer (𝒜 : Set (H →L[ℂ] H)))
      = Set.centralizer (𝒜 : Set (H →L[ℂ] H)) :=
  Set.union_eq_self_of_subset_right (star_centralizer_coe_subset 𝒜)

theorem coe_starSubalgebra_centralizer_centralizer (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ((StarSubalgebra.centralizer ℂ (Set.centralizer (𝒜 : Set (H →L[ℂ] H))) :
        StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = Set.centralizer (Set.centralizer (𝒜 : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.coe_centralizer, centralizer_union_star_centralizer]

/-- The bicommutant `𝒜''` of a star subalgebra of `B(H)`, as a von Neumann algebra. -/
noncomputable def bicommutant (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (Set.centralizer (𝒜 : Set (H →L[ℂ] H)))
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (Set.centralizer (𝒜 : Set (H →L[ℂ] H))) :
        StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)))
      = ((StarSubalgebra.centralizer ℂ (Set.centralizer (𝒜 : Set (H →L[ℂ] H))) :
        StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [coe_starSubalgebra_centralizer_centralizer]
    refine subset_antisymm ?_ Set.subset_centralizer_centralizer
    exact Set.centralizer_subset Set.subset_centralizer_centralizer

theorem coe_bicommutant (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutant 𝒜 : Set (H →L[ℂ] H))
      = Set.centralizer (Set.centralizer (𝒜 : Set (H →L[ℂ] H))) :=
  coe_starSubalgebra_centralizer_centralizer 𝒜

theorem mem_bicommutant_iff (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    x ∈ bicommutant 𝒜 ↔ ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → x * t = t * x := by
  rw [← SetLike.mem_coe, coe_bicommutant, Set.mem_centralizer_iff]
  constructor
  · intro hx t ht
    exact (hx t (Set.mem_centralizer_iff.mpr ht)).symm
  · intro hx t ht
    exact (hx t (fun a ha => Set.mem_centralizer_iff.mp ht a ha)).symm

theorem le_bicommutant (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) {a : H →L[ℂ] H} (ha : a ∈ 𝒜) :
    a ∈ bicommutant 𝒜 :=
  (mem_bicommutant_iff 𝒜 a).mpr (fun _ ht => ht a ha)

end Bicommutant

/-! ## Part II. The corner vector functional: normality, positivity, normalization -/

section CornerFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A star projection is contractive. -/
theorem norm_apply_le_of_isStarProjection {p : H →L[ℂ] H} (hp : IsStarProjection p) (v : H) :
    ‖p v‖ ≤ ‖v‖ := by
  have h : ⟪p v, p v⟫_ℂ = ⟪v, p v⟫_ℂ := by
    calc ⟪p v, p v⟫_ℂ = ⟪v, (star p) (p v)⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪v, p v⟫_ℂ := by
          rw [hp.isSelfAdjoint.star_eq]
          change ⟪v, (p * p) v⟫_ℂ = ⟪v, p v⟫_ℂ
          rw [hp.isIdempotentElem]
  have h2 : ‖p v‖ ^ 2 ≤ ‖v‖ * ‖p v‖ := by
    calc ‖p v‖ ^ 2 = ‖(⟪p v, p v⟫_ℂ)‖ := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; simp
      _ = ‖(⟪v, p v⟫_ℂ)‖ := by rw [h]
      _ ≤ ‖v‖ * ‖p v‖ := norm_inner_le_norm (𝕜 := ℂ) v (p v)
  nlinarith [norm_nonneg (p v), norm_nonneg v]

omit [CompleteSpace H] in
/--
**Normality of the corner vector functional, stated exactly.**  Along any filter, strong
(pointwise) convergence of operators implies convergence of the vector functional.  No
topology on the operator algebra and no typeclass-level normality is used.
-/
theorem vectorFunctional_tendsto_of_strong {ι : Type*} {l : Filter ι} (xi : H)
    {u : ι → H →L[ℂ] H} {x : H →L[ℂ] H}
    (hu : ∀ v : H, Tendsto (fun i => u i v) l (𝓝 (x v))) :
    Tendsto (fun i => vectorFunctional xi (u i)) l (𝓝 (vectorFunctional xi x)) := by
  simp only [vectorFunctional_apply]
  exact ((continuous_const.inner continuous_id).tendsto (x xi)).comp (hu xi)

/-- **Positivity**: the corner functional evaluated at `a^* a` is the squared norm of `a xi`. -/
theorem vectorFunctional_star_mul_self (xi : H) (a : H →L[ℂ] H) :
    vectorFunctional xi (star a * a) = ((‖a xi‖ ^ 2 : ℝ) : ℂ) := by
  rw [vectorFunctional_apply]
  change ⟪xi, (star a) (a xi)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

/-- The corner functional vanishes at `a^* a` exactly when `a` annihilates the vector. -/
theorem vectorFunctional_star_mul_self_eq_zero_iff (xi : H) (a : H →L[ℂ] H) :
    vectorFunctional xi (star a * a) = 0 ↔ a xi = 0 := by
  rw [vectorFunctional_star_mul_self]
  constructor
  · intro h
    have : (‖a xi‖ : ℝ) ^ 2 = 0 := by exact_mod_cast h
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h; simp [h]

omit [CompleteSpace H] in
/-- **Normalization**: the corner functional is a state on the corner, `τ_q(q) = 1`. -/
theorem vectorFunctional_eq_one_of_fixes {q : H →L[ℂ] H} {xi : H}
    (hfix : q xi = xi) (hnorm : ‖xi‖ = 1) : vectorFunctional xi q = 1 := by
  rw [vectorFunctional_apply, hfix, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hnorm]
  norm_num

end CornerFunctional

/-! ## Part III. From corner traciality to faithfulness on `q M q`

The manuscript's Proposition `prop:faithful` is proved here for *arbitrary* corner elements,
strengthening the projection-only faithfulness of `FiniteFiber.VectorCorner`.
-/

section Faithful

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The key tracial step: if a corner element annihilates the distinguished vector, then so does
its product with any other corner element.  This is the manuscript's estimate
`‖x y Ω‖² = τ_q(y^* x^* x y) = τ_q(x^* x y y^*) = 0`, carried out without square roots.
-/
theorem cornerElement_mul_apply_eq_zero_of_tracial
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (hq : IsProjectionIn M q)
    (htracial : ∀ {a b : H →L[ℂ] H}, IsCornerElement M q a → IsCornerElement M q b →
      vectorFunctional xi (a * b) = vectorFunctional xi (b * a))
    {x y : H →L[ℂ] H} (hx : IsCornerElement M q x) (hy : IsCornerElement M q y)
    (hzero : x xi = 0) : (x * y) xi = 0 := by
  have hxstar : IsCornerElement M q (star x) := hx.star_mem hq
  have hystar : IsCornerElement M q (star y) := hy.star_mem hq
  have hcorner₁ : IsCornerElement M q (star y * (star x * x)) :=
    hystar.mul (hxstar.mul hx)
  have htr := htracial hcorner₁ hy
  have hnorm : ((‖(x * y) xi‖ ^ 2 : ℝ) : ℂ) = 0 := by
    have hstar : star (x * y) * (x * y) = (star y * (star x * x)) * y := by
      rw [star_mul]; noncomm_ring
    have h1 : vectorFunctional xi (star (x * y) * (x * y)) =
        vectorFunctional xi (y * (star y * (star x * x))) := by
      rw [hstar, htr]
    rw [vectorFunctional_star_mul_self] at h1
    rw [h1, vectorFunctional_apply]
    change ⟪xi, y ((star y) ((star x) (x xi)))⟫_ℂ = 0
    rw [hzero, map_zero, map_zero, map_zero, inner_zero_right]
  have : ‖(x * y) xi‖ ^ 2 = 0 := by exact_mod_cast hnorm
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/--
**Faithfulness of the corner state (manuscript Proposition `prop:faithful`).**  Under the
regional/complementary product-orbit data of `VectorCornerData` and traciality on the corner,
`τ_q` is faithful on all of `q M q`: `τ_q(x^* x) = 0` forces `x = 0`.
-/
theorem VectorCornerData.cornerElement_eq_zero_of_vectorFunctional_star_mul_self_eq_zero
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi) {x : H →L[ℂ] H} (hx : IsCornerElement M q x)
    (hzero : vectorFunctional xi (star x * x) = 0) : x = 0 := by
  have hxxi : x xi = 0 := (vectorFunctional_star_mul_self_eq_zero_iff xi x).mp hzero
  have horbit_zero : Set.EqOn x (0 : H →L[ℂ] H)
      (productOrbit D.region D.complement xi) := by
    rintro v ⟨a, ha, b, hb, rfl⟩
    have haM : a ∈ M := D.region_mem a ha
    have hcorner : IsCornerElement M q (q * a * q) :=
      isCornerElement_compress D.q_projection haM
    have hxa : (x * (q * a * q)) xi = 0 :=
      cornerElement_mul_apply_eq_zero_of_tracial D.q_projection D.tracial hx hcorner hxxi
    have hxq : x * q = x := hx.2.2
    have hqxi : q xi = xi := D.q_fixes_xi
    have hxaxi : (x * a) xi = 0 := by
      have : (x * (q * a * q)) xi = (x * a) xi := by
        change x (q (a (q xi))) = x (a xi)
        rw [hqxi]
        have : x (q (a xi)) = (x * q) (a xi) := rfl
        rw [this, hxq]
      rw [← this, hxa]
    have hab : a * b = b * a := D.region_commutes_complement a ha b hb
    have hxb : x * b = b * x := D.commutes_complement x hx.1 b hb
    change (x * (a * b)) xi = 0
    calc (x * (a * b)) xi = (b * (x * a)) xi := by
          congr 1
          calc x * (a * b) = x * (b * a) := by rw [hab]
            _ = (x * b) * a := by rw [mul_assoc]
            _ = (b * x) * a := by rw [hxb]
            _ = b * (x * a) := by rw [mul_assoc]
      _ = 0 := by
          change b ((x * a) xi) = 0
          rw [hxaxi, map_zero]
  exact ContinuousLinearMap.ext_on D.product_orbit_dense horbit_zero

end Faithful

/-! ## Part IV. The finite-volume trace identity -/

section FiniteVolume

variable {Site : Type*} [DecidableEq Site]

open scoped FiniteFiber.FiniteRegionQubitMatrix

/-- Trace cyclicity of the compression by a matrix projection. -/
theorem trace_projection_sandwich_comm {n : Type*} [Fintype n] [DecidableEq n]
    {P x y : Matrix n n ℂ} (hP : P * P = P) :
    (P * x * P * y * P).trace = (P * y * P * x * P).trace := by
  have hfac : ∀ a b : Matrix n n ℂ, (P * a * P) * (P * b * P) = P * a * P * b * P := by
    intro a b
    calc (P * a * P) * (P * b * P) = P * a * (P * P) * b * P := by noncomm_ring
      _ = P * a * P * b * P := by rw [hP]
  rw [← hfac x y, ← hfac y x, Matrix.trace_mul_comm]

/-- The local code projector `P_F` of a region, typed on that region. -/
noncomputable def FullPauliStabilizerSystem.regionCodeProjector
    (S : FullPauliStabilizerSystem Site) (F : Finset Site) : finiteRegionQubitAlgebra F :=
  (S.regionStabilizer F).regionProjector

theorem FullPauliStabilizerSystem.regionCodeProjector_isIdempotent
    (S : FullPauliStabilizerSystem Site) (F : Finset Site) :
    S.regionCodeProjector F * S.regionCodeProjector F = S.regionCodeProjector F :=
  (S.regionStabilizer F).regionProjector_isStarProjection.isIdempotentElem

theorem FullPauliStabilizerSystem.regionCodeProjector_isStarProjection
    (S : FullPauliStabilizerSystem Site) (F : Finset Site) :
    IsStarProjection (S.regionCodeProjector F) :=
  (S.regionStabilizer F).regionProjector_isStarProjection

theorem FullPauliStabilizerSystem.regionDensity_eq_smul_regionCodeProjector
    (S : FullPauliStabilizerSystem Site) (F : Finset Site) :
    S.regionDensity F = ((S.regionCodeProjector F).trace)⁻¹ • S.regionCodeProjector F :=
  (S.regionStabilizer F).regionDensity_eq_trace_normalized_regionProjector

/--
**The finite-volume trace identity (manuscript Lemma `lem:finite-trace`, finite stage).**
The local stabilizer state is cyclic on operators compressed by the local code projector
`P_F`, because `ρ_F` is a multiple of `P_F` and the finite matrix trace is cyclic.
-/
theorem FullPauliStabilizerSystem.localState_regionCodeProjector_comm
    (S : FullPauliStabilizerSystem Site) (F : Finset Site)
    (x y : finiteRegionQubitAlgebra F) :
    S.localState F (S.regionCodeProjector F * x * S.regionCodeProjector F * y *
        S.regionCodeProjector F) =
      S.localState F (S.regionCodeProjector F * y * S.regionCodeProjector F * x *
        S.regionCodeProjector F) := by
  set P := S.regionCodeProjector F with hPdef
  have hP : P * P = P := S.regionCodeProjector_isIdempotent F
  have hdens : S.regionDensity F = (P.trace)⁻¹ • P :=
    S.regionDensity_eq_smul_regionCodeProjector F
  have key : ∀ a b : finiteRegionQubitAlgebra F,
      S.localState F (P * a * P * b * P) = (P.trace)⁻¹ * (P * a * P * b * P).trace := by
    intro a b
    rw [S.localState_apply, hdens, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have hcollapse : P * (P * a * P * b * P) = P * a * P * b * P := by
      calc P * (P * a * P * b * P) = (P * P) * a * P * b * P := by noncomm_ring
        _ = P * a * P * b * P := by rw [hP]
    rw [hcollapse]
  rw [key x y, key y x, trace_projection_sandwich_comm hP]

end FiniteVolume

/-! ## Part V. The represented local algebra and the local code supports -/

section Model

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped FiniteFiber.FiniteRegionQubitMatrix

namespace QuasilocalStabilizerState

variable {S : FullPauliStabilizerSystem Site} {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState S Q)

/--
The represented local algebra `𝒰_{Γ,fin} = π_ω(𝒜_loc)` of the manuscript, as a star
subalgebra of the bounded operators on the GNS space.
-/
noncomputable def localOperatorAlgebra : StarSubalgebra ℂ (W.GNS →L[ℂ] W.GNS) :=
  (Q.localStarAlgebra (Set.univ : Set Site)).map W.gnsRepresentation

theorem mem_localOperatorAlgebra_iff (T : W.GNS →L[ℂ] W.GNS) :
    T ∈ W.localOperatorAlgebra ↔ ∃ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) = T := by
  constructor
  · intro hT
    obtain ⟨a, ha, rfl⟩ := StarSubalgebra.mem_map.mp hT
    obtain ⟨F, -, x, rfl⟩ := ha
    exact ⟨F, x, rfl⟩
  · rintro ⟨F, x, rfl⟩
    exact StarSubalgebra.mem_map.mpr
      ⟨Q.embed F x, Q.embed_mem_localSet (by simp) x, rfl⟩

theorem representation_mem_localOperatorAlgebra (F : Finset Site)
    (x : finiteRegionQubitAlgebra F) :
    W.gnsRepresentation (Q.embed F x) ∈ W.localOperatorAlgebra :=
  (W.mem_localOperatorAlgebra_iff _).mpr ⟨F, x, rfl⟩

/-- The represented local algebra sits inside any von Neumann algebra containing the
represented finite local algebras. -/
theorem localOperatorAlgebra_le {M : VonNeumannAlgebra W.GNS}
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    ∀ T ∈ W.localOperatorAlgebra, T ∈ M := by
  intro T hT
  obtain ⟨F, x, rfl⟩ := (W.mem_localOperatorAlgebra_iff T).mp hT
  exact hM F x

/--
**The GNS vector is cyclic already for the represented local algebra.**  This is derived
from Mathlib's GNS cyclicity together with norm density of the local elements in the
quasilocal C-star algebra and contractivity of a star-algebra map of C-star algebras.
-/
theorem dense_localOperatorAlgebra_orbit :
    Dense {v : W.GNS | ∃ T ∈ W.localOperatorAlgebra, T W.gnsVector = v} := by
  letI : CStarAlgebra (W.GNS →L[ℂ] W.GNS) := { }
  rw [Metric.dense_iff]
  intro v r hr
  obtain ⟨w, hwball, a, rfl⟩ :=
    Metric.dense_iff.mp W.denseRange_gnsRepresentation_gnsVector v (r / 2) (by positivity)
  obtain ⟨b, hbball, hbmem⟩ :=
    Metric.dense_iff.mp Q.dense_localStarAlgebra_univ a (r / 2) (by positivity)
  refine ⟨W.gnsRepresentation b W.gnsVector, ?_, ⟨W.gnsRepresentation b, ?_, rfl⟩⟩
  · have h1 : ‖W.gnsRepresentation b W.gnsVector - W.gnsRepresentation a W.gnsVector‖ < r / 2 := by
      have hsub : W.gnsRepresentation b W.gnsVector - W.gnsRepresentation a W.gnsVector
          = W.gnsRepresentation (b - a) W.gnsVector := by
        rw [map_sub]; rfl
      rw [hsub]
      calc ‖W.gnsRepresentation (b - a) W.gnsVector‖
          ≤ ‖W.gnsRepresentation (b - a)‖ * ‖W.gnsVector‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖W.gnsRepresentation (b - a)‖ := by rw [W.norm_gnsVector, mul_one]
        _ ≤ ‖b - a‖ := NonUnitalStarAlgHom.norm_apply_le W.gnsRepresentation _
        _ < r / 2 := by simpa [dist_eq_norm] using hbball
    have h2 : ‖W.gnsRepresentation a W.gnsVector - v‖ < r / 2 := by
      rw [← dist_eq_norm]; simpa [dist_comm] using hwball
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (W.gnsRepresentation b W.gnsVector) (W.gnsRepresentation a W.gnsVector) v
    simp only [Metric.mem_ball, dist_eq_norm]
    linarith
  · exact StarSubalgebra.mem_map.mpr ⟨b, hbmem, rfl⟩

end QuasilocalStabilizerState

end Model

/-! ## Part VI. The local supports are represented local code projectors -/

section Supports

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped FiniteFiber.FiniteRegionQubitMatrix

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}

/-- The finite local stabilizer subgroup of stage `n` is the region stabilizer group of
`Γ_n`; the two descriptions of the same finite group are canonically identified. -/
def localStabilizerEquiv (n : ℕ) :
    ↥(R.localStabilizer n) ≃ ↥(R.stabilizerSystem.regionStabilizer (R.region n)).group where
  toFun s := ⟨((s : ↥R.stabilizerSystem.group) : FullPauliWord Site),
    (R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mpr
      ⟨(s : ↥R.stabilizerSystem.group).2,
        ((R.mem_localStabilizer_iff n _).mp s.2)⟩⟩
  invFun g := ⟨⟨(g : FullPauliWord Site),
      ((R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mp g.2).1⟩,
    (R.mem_localStabilizer_iff n _).mpr
      ((R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mp g.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
**The local support is the represented local code projector.**
`π_ω(P_{Γ_n}) = p_n`: the strong-limit input of FF21 coincides with the represented
finite-volume code projector of the manuscript, which is what makes the finite-volume
trace identity applicable.
-/
theorem supportProjection_eq_representation
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (n : ℕ) :
    R.supportProjection W n =
      W.gnsRepresentation (Q.embed (R.region n)
        (R.stabilizerSystem.regionCodeProjector (R.region n))) := by
  have hRHS : W.gnsRepresentation (Q.embed (R.region n)
        (R.stabilizerSystem.regionCodeProjector (R.region n))) =
      (Fintype.card ↥(R.stabilizerSystem.regionStabilizer (R.region n)).group : ℂ)⁻¹ •
        ∑ g : ↥(R.stabilizerSystem.regionStabilizer (R.region n)).group,
          W.gnsRepresentation (Q.wordElement (g : FullPauliWord Site)) := by
    rw [FullPauliStabilizerSystem.regionCodeProjector,
      FullPauliRegionStabilizer.regionProjector, FullPauliRegionStabilizer.regionSum,
      map_smul, map_smul, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro g _
    simp only [FullPauliStabilizerSystem.regionStabilizer_region]
    rw [Q.embed_eq_wordElement]
    exact (R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mp g.2 |>.2
  rw [hRHS, FiniteRangeStabilizerSystem.supportProjection, stabilizerAverageSequence,
    SelfAdjointFiniteGroupAction.average]
  rw [Fintype.card_congr (R.localStabilizerEquiv n)]
  congr 1
  exact Fintype.sum_equiv (R.localStabilizerEquiv n) _ _ (fun _ => rfl)

end FiniteRangeStabilizerSystem

end Supports

/-! ## Part VII. The corner pairing and the abstract traciality bridge

Traciality of the corner vector functional on `q M q` is equivalent to the symmetry of the
*corner pairing* `Φ(x, y) = τ_q(q x q y q)`, and the manuscript's Kaplansky-density step is
replaced here by the strong-approximation form of the von Neumann density theorem of Part I:
symmetry of `Φ` against the local algebra `𝒜` propagates to all of `𝒜''`.
-/

section Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The corner pairing `Φ(x, y) = τ_q(q x q y q)` of the corner vector functional. -/
noncomputable def cornerPairing (q : H →L[ℂ] H) (xi : H) (x y : H →L[ℂ] H) : ℂ :=
  vectorFunctional xi (q * x * q * y * q)

/-- `Φ(x, y) = ⟪Ω, x (q (y Ω))⟫`: the pairing sees `x` only through its action at the
single vector `q (y Ω)`. -/
theorem cornerPairing_eq_inner_right {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) {xi : H}
    (hqxi : q xi = xi) (x y : H →L[ℂ] H) :
    cornerPairing q xi x y = ⟪xi, x (q (y xi))⟫_ℂ := by
  rw [cornerPairing, vectorFunctional_apply]
  change ⟪xi, q (x (q (y (q xi))))⟫_ℂ = _
  rw [hqxi]
  rw [show ⟪xi, q (x (q (y xi)))⟫_ℂ = ⟪(ContinuousLinearMap.adjoint q) xi, x (q (y xi))⟫_ℂ from
    (ContinuousLinearMap.adjoint_inner_left _ _ _).symm]
  rw [show ContinuousLinearMap.adjoint q = q from
    by rw [← ContinuousLinearMap.star_eq_adjoint]; exact hq.star_eq, hqxi]

/-- `Φ(x, y) = ⟪q (x^* Ω), y Ω⟫`: the pairing sees `y` only through its action at the
single vector `Ω`. -/
theorem cornerPairing_eq_inner_left {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) {xi : H}
    (hqxi : q xi = xi) (x y : H →L[ℂ] H) :
    cornerPairing q xi x y = ⟪q ((star x) xi), y xi⟫_ℂ := by
  have hqadj : ContinuousLinearMap.adjoint q = q := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hq.star_eq
  rw [cornerPairing_eq_inner_right hq hqxi]
  rw [show ⟪xi, x (q (y xi))⟫_ℂ
      = ⟪(ContinuousLinearMap.adjoint x) xi, q (y xi)⟫_ℂ from
    (ContinuousLinearMap.adjoint_inner_left _ _ _).symm]
  rw [show ⟪(ContinuousLinearMap.adjoint x) xi, q (y xi)⟫_ℂ
      = ⟪q ((ContinuousLinearMap.adjoint x) xi), y xi⟫_ℂ from by
    rw [← ContinuousLinearMap.adjoint_inner_left, hqadj]]
  rw [ContinuousLinearMap.star_eq_adjoint]

/--
**The approximation step (replacing Kaplansky density).**  If the corner pairing with a
fixed `c` is symmetric against every element of the star subalgebra `𝒜`, then it is
symmetric against every `z` in the bicommutant `𝒜''`.  Only the two vectors `Ω` and
`q (c Ω)` are involved, so the two-vector density theorem of Part I suffices.
-/
theorem cornerPairing_comm_of_local
    {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) {xi : H} (hqxi : q xi = xi)
    (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) {c z : H →L[ℂ] H}
    (hz : ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → z * t = t * z)
    (hlocal : ∀ u ∈ 𝒜, cornerPairing q xi u c = cornerPairing q xi c u) :
    cornerPairing q xi z c = cornerPairing q xi c z := by
  set d := cornerPairing q xi z c - cornerPairing q xi c z with hd
  set K := ‖xi‖ + ‖q ((star c) xi)‖ + 1 with hK
  have hKpos : 0 < K := by
    have := norm_nonneg xi
    have := norm_nonneg (q ((star c) xi))
    simp only [hK]; linarith
  have key : ∀ ε : ℝ, 0 < ε → ‖d‖ < ε := by
    intro ε hε
    obtain ⟨u, hu, h1, h2⟩ :=
      exists_mem_norm_sub_apply_lt_two 𝒜 hz (q (c xi)) xi (ε := ε / K) (by positivity)
    have e1 : cornerPairing q xi z c - cornerPairing q xi u c
        = ⟪xi, z (q (c xi)) - u (q (c xi))⟫_ℂ := by
      rw [cornerPairing_eq_inner_right hq hqxi, cornerPairing_eq_inner_right hq hqxi,
        ← inner_sub_right]
    have e2 : cornerPairing q xi c z - cornerPairing q xi c u
        = ⟪q ((star c) xi), z xi - u xi⟫_ℂ := by
      rw [cornerPairing_eq_inner_left hq hqxi, cornerPairing_eq_inner_left hq hqxi,
        ← inner_sub_right]
    have b1 : ‖cornerPairing q xi z c - cornerPairing q xi u c‖ ≤ ‖xi‖ * (ε / K) := by
      rw [e1]
      exact le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
        (mul_le_mul_of_nonneg_left h1.le (norm_nonneg xi))
    have b2 : ‖cornerPairing q xi c z - cornerPairing q xi c u‖
        ≤ ‖q ((star c) xi)‖ * (ε / K) := by
      rw [e2]
      exact le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
        (mul_le_mul_of_nonneg_left h2.le (norm_nonneg _))
    have hsplit : d = (cornerPairing q xi z c - cornerPairing q xi u c)
        - (cornerPairing q xi c z - cornerPairing q xi c u) := by
      rw [hd, hlocal u hu]; ring
    have htri := norm_sub_le (cornerPairing q xi z c - cornerPairing q xi u c)
      (cornerPairing q xi c z - cornerPairing q xi c u)
    rw [← hsplit] at htri
    have h3 : (‖xi‖ + ‖q ((star c) xi)‖) * (ε / K) < K * (ε / K) :=
      mul_lt_mul_of_pos_right (by simp only [hK]; linarith) (by positivity)
    have h4 : K * (ε / K) = ε := by field_simp
    linarith [b1, b2, htri]
  by_contra hne
  exact absurd (key ‖d‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (lt_irrefl _)

/--
**Two applications of the approximation step give full symmetry of the corner pairing.**
If `Φ` is symmetric on the local algebra `𝒜`, it is symmetric on the bicommutant `𝒜''`.
-/
theorem cornerPairing_comm_of_localAlgebra
    {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) {xi : H} (hqxi : q xi = xi)
    (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    (hlocal : ∀ u ∈ 𝒜, ∀ w ∈ 𝒜, cornerPairing q xi u w = cornerPairing q xi w u)
    {x y : H →L[ℂ] H}
    (hx : ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → x * t = t * x)
    (hy : ∀ t : H →L[ℂ] H, (∀ a ∈ 𝒜, a * t = t * a) → y * t = t * y) :
    cornerPairing q xi x y = cornerPairing q xi y x := by
  have step1 : ∀ w ∈ 𝒜, cornerPairing q xi x w = cornerPairing q xi w x :=
    fun w hw => cornerPairing_comm_of_local hq hqxi 𝒜 hx (fun u hu => hlocal u hu w hw)
  exact (cornerPairing_comm_of_local hq hqxi 𝒜 hy (fun u hu => (step1 u hu).symm)).symm

/-- On corner elements the pairing *is* the corner functional of the product. -/
theorem cornerPairing_eq_vectorFunctional_mul
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H} {a b : H →L[ℂ] H}
    (ha : IsCornerElement M q a) (hb : IsCornerElement M q b) :
    cornerPairing q xi a b = vectorFunctional xi (a * b) := by
  rw [cornerPairing]
  congr 1
  calc q * a * q * b * q = ((q * a) * q) * (b * q) := by noncomm_ring
    _ = a * b := by rw [ha.2.1, ha.2.2, hb.2.2]

/-- **Traciality on `q M q` from symmetry of the corner pairing on `M`.** -/
theorem tracial_of_cornerPairing_comm
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, cornerPairing q xi x y = cornerPairing q xi y x)
    {a b : H →L[ℂ] H} (ha : IsCornerElement M q a) (hb : IsCornerElement M q b) :
    vectorFunctional xi (a * b) = vectorFunctional xi (b * a) := by
  rw [← cornerPairing_eq_vectorFunctional_mul ha hb,
    ← cornerPairing_eq_vectorFunctional_mul hb ha]
  exact hcomm a ha.1 b hb.1

/-! ### Passing symmetry of the pairing through the strong limit -/

omit [CompleteSpace H] in
/-- A contractive strongly convergent sequence of operators may be composed with a
convergent sequence of vectors. -/
theorem tendsto_apply_of_stronglyTendsTo {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (hp : StronglyTendsTo p q) (hcontr : ∀ (n : ℕ) (v : H), ‖p n v‖ ≤ ‖v‖)
    {v : ℕ → H} {w : H} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => p n (v n)) atTop (𝓝 (q w)) := by
  have h1 : Tendsto (fun n => p n (v n) - p n w) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => ‖v n - w‖) (fun n => ?_) ?_
    · rw [← map_sub]; exact hcontr n _
    · exact tendsto_iff_norm_sub_tendsto_zero.mp hv
  simpa using h1.add (hp w)

omit [CompleteSpace H] in
/-- The threefold compression `p_n u p_n w p_n` converges strongly to `q u q w q`. -/
theorem tendsto_sandwich_apply {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (hp : StronglyTendsTo p q) (hcontr : ∀ (n : ℕ) (v : H), ‖p n v‖ ≤ ‖v‖)
    (u w : H →L[ℂ] H) (xi : H) :
    Tendsto (fun n => (p n * u * p n * w * p n) xi) atTop
      (𝓝 ((q * u * q * w * q) xi)) := by
  have t0 : Tendsto (fun n => p n xi) atTop (𝓝 (q xi)) := hp xi
  have t1 : Tendsto (fun n => w (p n xi)) atTop (𝓝 (w (q xi))) :=
    (w.continuous.tendsto _).comp t0
  have t2 := tendsto_apply_of_stronglyTendsTo hp hcontr t1
  have t3 : Tendsto (fun n => u (p n (w (p n xi)))) atTop (𝓝 (u (q (w (q xi))))) :=
    (u.continuous.tendsto _).comp t2
  exact tendsto_apply_of_stronglyTendsTo hp hcontr t3

omit [CompleteSpace H] in
/-- The exact normality statement used for the corner pairing: the finite-stage compressed
functionals converge to the corner pairing. -/
theorem tendsto_vectorFunctional_sandwich {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (hp : StronglyTendsTo p q) (hcontr : ∀ (n : ℕ) (v : H), ‖p n v‖ ≤ ‖v‖)
    (u w : H →L[ℂ] H) (xi : H) :
    Tendsto (fun n => vectorFunctional xi (p n * u * p n * w * p n)) atTop
      (𝓝 (cornerPairing q xi u w)) := by
  simp only [vectorFunctional_apply, cornerPairing]
  exact ((continuous_const.inner continuous_id).tendsto _).comp
    (tendsto_sandwich_apply hp hcontr u w xi)

omit [CompleteSpace H] in
/--
**Finite-stage symmetry passes to the limit.**  If the compressed functionals are eventually
symmetric in `u` and `w`, the corner pairing is symmetric in `u` and `w`.
-/
theorem cornerPairing_comm_of_eventually {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (hp : StronglyTendsTo p q) (hcontr : ∀ (n : ℕ) (v : H), ‖p n v‖ ≤ ‖v‖)
    {xi : H} {u w : H →L[ℂ] H}
    (heq : ∀ᶠ n in atTop, vectorFunctional xi (p n * u * p n * w * p n)
      = vectorFunctional xi (p n * w * p n * u * p n)) :
    cornerPairing q xi u w = cornerPairing q xi w u := by
  refine tendsto_nhds_unique (tendsto_vectorFunctional_sandwich hp hcontr u w xi) ?_
  exact (tendsto_vectorFunctional_sandwich hp hcontr w u xi).congr'
    (heq.mono fun n h => h.symm)

end Pairing

/-! ## Part VIII. Local traciality at the finite-range stabilizer model -/

section LocalTraciality

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped FiniteFiber.FiniteRegionQubitMatrix

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState R.stabilizerSystem Q)

/-- Each local code-space support is a star projection, hence contractive. -/
theorem supportProjection_isStarProjection (n : ℕ) :
    IsStarProjection (R.supportProjection W n) := by
  rw [R.supportProjection_eq_representation W n]
  refine ⟨?_, ?_⟩
  · show _ * _ = _
    rw [← map_mul, ← map_mul,
      R.stabilizerSystem.regionCodeProjector_isIdempotent (R.region n)]
  · show star _ = _
    rw [← map_star, ← map_star,
      (R.stabilizerSystem.regionCodeProjector_isStarProjection
        (R.region n)).isSelfAdjoint.star_eq]

theorem norm_supportProjection_apply_le (n : ℕ) (v : W.GNS) :
    ‖R.supportProjection W n v‖ ≤ ‖v‖ :=
  norm_apply_le_of_isStarProjection (R.supportProjection_isStarProjection W n) v

/--
**The finite-stage value of the compressed vector functional.**  For a region `Γ_n`
containing the supports of both local operators, the compressed functional is exactly the
finite local stabilizer state of the compressed matrix product.
-/
theorem vectorFunctional_supportProjection_sandwich
    (n : ℕ) {F₀ F₁ : Finset Site} (h₀ : F₀ ⊆ R.region n) (h₁ : F₁ ⊆ R.region n)
    (a : finiteRegionQubitAlgebra F₀) (b : finiteRegionQubitAlgebra F₁) :
    vectorFunctional W.gnsVector
        (R.supportProjection W n * W.gnsRepresentation (Q.embed F₀ a)
          * R.supportProjection W n * W.gnsRepresentation (Q.embed F₁ b)
          * R.supportProjection W n)
      = R.stabilizerSystem.localState (R.region n)
          (R.stabilizerSystem.regionCodeProjector (R.region n) * localInclusion h₀ a
            * R.stabilizerSystem.regionCodeProjector (R.region n) * localInclusion h₁ b
            * R.stabilizerSystem.regionCodeProjector (R.region n)) := by
  have hu : W.gnsRepresentation (Q.embed F₀ a)
      = W.gnsRepresentation (Q.embed (R.region n) (localInclusion h₀ a)) := by
    rw [Q.embed_localInclusion F₀ (R.region n) h₀ a]
  have hw : W.gnsRepresentation (Q.embed F₁ b)
      = W.gnsRepresentation (Q.embed (R.region n) (localInclusion h₁ b)) := by
    rw [Q.embed_localInclusion F₁ (R.region n) h₁ b]
  rw [hu, hw, R.supportProjection_eq_representation W n]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  rw [vectorFunctional_apply, W.inner_gnsVector_gnsRepresentation_embed]

/--
**Local traciality (manuscript Lemma `lem:finite-trace`, represented form).**  The corner
pairing of two represented local operators is symmetric.  The finite-volume trace
cyclicity holds at every stage whose region contains both supports, and the strong limit
transports it to the corner.
-/
theorem cornerPairing_comm_of_local_embed (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    {F₀ F₁ : Finset Site} (a : finiteRegionQubitAlgebra F₀)
    (b : finiteRegionQubitAlgebra F₁) :
    cornerPairing (R.cornerProjection W) W.gnsVector
        (W.gnsRepresentation (Q.embed F₀ a)) (W.gnsRepresentation (Q.embed F₁ b))
      = cornerPairing (R.cornerProjection W) W.gnsVector
        (W.gnsRepresentation (Q.embed F₁ b)) (W.gnsRepresentation (Q.embed F₀ a)) := by
  obtain ⟨n₀, hn₀⟩ := R.exists_region_superset (F₀ ∪ F₁)
  refine cornerPairing_comm_of_eventually (R.stronglyTendsTo_cornerProjection W M hM)
    (R.norm_supportProjection_apply_le W) ?_
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  have hsub : F₀ ∪ F₁ ⊆ R.region n := hn₀.trans (R.region_mono hn)
  have h₀ : F₀ ⊆ R.region n := (Finset.subset_union_left).trans hsub
  have h₁ : F₁ ⊆ R.region n := (Finset.subset_union_right).trans hsub
  rw [R.vectorFunctional_supportProjection_sandwich W n h₀ h₁ a b,
    R.vectorFunctional_supportProjection_sandwich W n h₁ h₀ b a]
  exact R.stabilizerSystem.localState_regionCodeProjector_comm (R.region n)
    (localInclusion h₀ a) (localInclusion h₁ b)

/-- The same statement for arbitrary members of the represented local algebra. -/
theorem cornerPairing_comm_of_mem_localOperatorAlgebra (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    {u w : W.GNS →L[ℂ] W.GNS} (hu : u ∈ W.localOperatorAlgebra)
    (hw : w ∈ W.localOperatorAlgebra) :
    cornerPairing (R.cornerProjection W) W.gnsVector u w
      = cornerPairing (R.cornerProjection W) W.gnsVector w u := by
  obtain ⟨F₀, a, rfl⟩ := (W.mem_localOperatorAlgebra_iff u).mp hu
  obtain ⟨F₁, b, rfl⟩ := (W.mem_localOperatorAlgebra_iff w).mp hw
  exact R.cornerPairing_comm_of_local_embed W M hM a b

end FiniteRangeStabilizerSystem

end LocalTraciality

/-! ## Part IX. Fullness, traciality and the assembled FF20 premises -/

section Assembly

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped FiniteFiber.FiniteRegionQubitMatrix

namespace QuasilocalStabilizerState

variable {S : FullPauliStabilizerSystem Site} {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState S Q)

/--
**The one genuinely extra hypothesis of this packet.**  `M` is *generated by* the
represented local algebra: every element of `M` commutes with every operator commuting
with `π_ω(𝒜_loc)`, i.e. `M ⊆ 𝒜''`.  Together with the FF21 hypothesis `hM` (`𝒜 ⊆ M`) this
says exactly `M = π_ω(𝒜_loc)'' = M_Γ`, the algebra the manuscript works with.

It is a *definitional identification* of `M`, not an analytic gap.  It cannot simply be
deleted: for the strictly larger algebra `M = B(H)` (which still satisfies `hM`) the
approximation argument below produces the local symmetry only for operators in the strong
closure of the local algebra, so the vector state on the corner is in general not tracial.
For the canonical algebra `M_Γ = π_ω(𝒜_loc)''` the hypothesis holds by construction; see
`QuasilocalStabilizerState.generatedByLocalAlgebra_localVonNeumannAlgebra`.
-/
def GeneratedByLocalAlgebra (M : VonNeumannAlgebra W.GNS) : Prop :=
  ∀ x ∈ M, ∀ t : W.GNS →L[ℂ] W.GNS,
    (∀ a ∈ W.localOperatorAlgebra, a * t = t * a) → x * t = t * x

end QuasilocalStabilizerState

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState R.stabilizerSystem Q)
variable (M : VonNeumannAlgebra W.GNS)
variable (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
  W.gnsRepresentation (Q.embed F x) ∈ M)

include hM

/-! ### Premise 2: the support projection is nonzero -/

/-- **FF20 premise 2 (derived).**  The corner projection `q` is nonzero, because it fixes
the unit GNS vector. -/
theorem cornerProjection_ne_zero' : R.cornerProjection W ≠ 0 :=
  R.cornerProjection_ne_zero W M hM

/-- The corner functional is a state on the corner: `τ_q(q) = 1`. -/
theorem vectorFunctional_cornerProjection_eq_one :
    vectorFunctional W.gnsVector (R.cornerProjection W) = 1 :=
  vectorFunctional_eq_one_of_fixes (R.cornerProjection_gnsVector W M hM) W.norm_gnsVector

/-! ### Premise 3: fullness -/

/--
**FF20 premise 3 (derived).**  The corner projection is *full*: no nonzero central
projection of `M` annihilates it.  The orbit argument uses only cyclicity of `Ω` for the
represented local algebra; no traciality is needed.
-/
theorem cornerProjection_isFullProjection :
    IsFullProjection M (R.cornerProjection W) := by
  refine ⟨R.cornerProjection_isProjectionIn W M hM, ?_⟩
  intro z hz hz0 hzq
  refine hz0 ?_
  have hzxi : z W.gnsVector = 0 := by
    have h1 : (z * R.cornerProjection W) W.gnsVector
        = z (R.cornerProjection W W.gnsVector) := rfl
    rw [R.cornerProjection_gnsVector W M hM] at h1
    rw [← h1, hzq]
    rfl
  have horbit : Set.EqOn z (0 : W.GNS →L[ℂ] W.GNS)
      {v : W.GNS | ∃ T ∈ W.localOperatorAlgebra, T W.gnsVector = v} := by
    rintro v ⟨T, hT, rfl⟩
    have hTM : T ∈ M := W.localOperatorAlgebra_le hM T hT
    have hcomm : (z * T) W.gnsVector = (T * z) W.gnsVector := by rw [hz.2 T hTM]
    have hval : z (T W.gnsVector) = T (z W.gnsVector) := hcomm
    show z (T W.gnsVector) = (0 : W.GNS →L[ℂ] W.GNS) _
    rw [hval, hzxi, map_zero]
    rfl
  exact DFunLike.coe_injective (Continuous.ext_on W.dense_localOperatorAlgebra_orbit
    z.continuous (0 : W.GNS →L[ℂ] W.GNS).continuous horbit)

/-! ### Premise 1: traciality and faithfulness on `q M q` -/

/--
**FF20 premise 1, traciality (conditional on `GeneratedByLocalAlgebra`).**  The corner
vector functional is tracial on `q M q`.
-/
theorem tracial_cornerProjection
    (hgen : W.GeneratedByLocalAlgebra M)
    {a b : W.GNS →L[ℂ] W.GNS}
    (ha : IsCornerElement M (R.cornerProjection W) a)
    (hb : IsCornerElement M (R.cornerProjection W) b) :
    vectorFunctional W.gnsVector (a * b) = vectorFunctional W.gnsVector (b * a) := by
  refine tracial_of_cornerPairing_comm (M := M) (fun x hx y hy => ?_) ha hb
  exact cornerPairing_comm_of_localAlgebra
    (R.cornerProjection_isProjectionIn W M hM).2.isSelfAdjoint
    (R.cornerProjection_gnsVector W M hM) W.localOperatorAlgebra
    (fun u hu w hw => R.cornerPairing_comm_of_mem_localOperatorAlgebra W M hM hu hw)
    (hgen x hx) (hgen y hy)

/-! ### The assembled orbit data -/

/--
**The three FF20 premises, assembled.**  With the definitional identification
`M = π_ω(𝒜_loc)''` supplied by `hgen`, the finite-range stabilizer model satisfies all
the analytic hypotheses `GNSOrbitConditions` which FF20 had to assume.  The regional
algebra is the represented local algebra and the complementary algebra is the scalars.
-/
noncomputable def gnsOrbitConditions (hgen : W.GeneratedByLocalAlgebra M) :
    GNSOrbitConditions M (R.cornerProjection W) W.gnsVector where
  region := (W.localOperatorAlgebra : Set (W.GNS →L[ℂ] W.GNS))
  complement := {1}
  region_mem a ha := W.localOperatorAlgebra_le hM a ha
  region_commutes_complement a _ b hb := by
    rw [Set.mem_singleton_iff] at hb; rw [hb, mul_one, one_mul]
  commutes_complement x _ b hb := by
    rw [Set.mem_singleton_iff] at hb; rw [hb, mul_one, one_mul]
  product_orbit_dense := by
    refine Dense.mono ?_ W.dense_localOperatorAlgebra_orbit
    refine le_trans ?_ Submodule.subset_span
    rintro v ⟨T, hT, rfl⟩
    exact ⟨T, hT, 1, rfl, by rw [mul_one]⟩
  tracial ha hb := R.tracial_cornerProjection W M hM hgen ha hb

/--
**The full support-corner conclusion at the finite-range stabilizer model.**  Feeding the
assembled premises into FF20 yields fullness, faithfulness on support subprojections, the
nonzero finite compression of every central summand, and semifiniteness of `M`.

(No no-type-III statement is derived here; that is FF23.)
-/
theorem supportCornerConclusion (hgen : W.GeneratedByLocalAlgebra M) :
    SupportCornerConclusion M (R.cornerProjection W) W.gnsVector :=
  finiteRange_supportCornerConclusion_of_gnsOrbit R W M hM
    (R.gnsOrbitConditions W M hM hgen)

/--
**FF20 premise 1, faithfulness (conditional on `GeneratedByLocalAlgebra`).**  The corner
state is faithful on all of `q M q`: `τ_q(x^* x) = 0` forces `x = 0`.  This strengthens
the projection-only faithfulness recorded in `SupportCornerConclusion`.
-/
theorem faithful_cornerProjection (hgen : W.GeneratedByLocalAlgebra M)
    {x : W.GNS →L[ℂ] W.GNS} (hx : IsCornerElement M (R.cornerProjection W) x)
    (hzero : vectorFunctional W.gnsVector (star x * x) = 0) : x = 0 :=
  VectorCornerData.cornerElement_eq_zero_of_vectorFunctional_star_mul_self_eq_zero
    ((R.gnsOrbitConditions W M hM hgen).toVectorCornerData
      (R.cornerProjection_isProjectionIn W M hM)
      (R.cornerProjection_gnsVector W M hM)) hx hzero

end FiniteRangeStabilizerSystem

/-! ### The canonical algebra `M_Γ = π_ω(𝒜_loc)''`: the premises become unconditional -/

namespace QuasilocalStabilizerState

variable {S : FullPauliStabilizerSystem Site} {Q : QuasilocalEmbedding Site A}

/--
The manuscript's algebra `M_Γ`: the von Neumann algebra generated by the represented local
algebra, i.e. its bicommutant.
-/
noncomputable def localVonNeumannAlgebra (W : QuasilocalStabilizerState S Q) :
    VonNeumannAlgebra W.GNS :=
  bicommutant W.localOperatorAlgebra

/-- `M_Γ` contains every represented finite local algebra: the FF21 hypothesis `hM`. -/
theorem representation_mem_localVonNeumannAlgebra (W : QuasilocalStabilizerState S Q)
    (F : Finset Site) (x : finiteRegionQubitAlgebra F) :
    W.gnsRepresentation (Q.embed F x) ∈ W.localVonNeumannAlgebra :=
  le_bicommutant _ (W.representation_mem_localOperatorAlgebra F x)

/-- **`M_Γ` satisfies the extra hypothesis by construction.** -/
theorem generatedByLocalAlgebra_localVonNeumannAlgebra
    (W : QuasilocalStabilizerState S Q) :
    W.GeneratedByLocalAlgebra W.localVonNeumannAlgebra :=
  fun x hx => (mem_bicommutant_iff _ x).mp hx

end QuasilocalStabilizerState

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState R.stabilizerSystem Q)

/--
**FF20 premise 1 for the canonical algebra, unconditionally.**  For `M = M_Γ = π_ω(𝒜_loc)''`
the corner vector functional is tracial on `q M q`; no extra hypothesis is needed, because
`GeneratedByLocalAlgebra` holds by construction of the bicommutant.
-/
theorem tracial_cornerProjection_localVonNeumannAlgebra
    {a b : W.GNS →L[ℂ] W.GNS}
    (ha : IsCornerElement W.localVonNeumannAlgebra (R.cornerProjection W) a)
    (hb : IsCornerElement W.localVonNeumannAlgebra (R.cornerProjection W) b) :
    vectorFunctional W.gnsVector (a * b) = vectorFunctional W.gnsVector (b * a) :=
  R.tracial_cornerProjection W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra
    W.generatedByLocalAlgebra_localVonNeumannAlgebra ha hb

/-- **Faithfulness on `q M_Γ q`, unconditionally.** -/
theorem faithful_cornerProjection_localVonNeumannAlgebra
    {x : W.GNS →L[ℂ] W.GNS}
    (hx : IsCornerElement W.localVonNeumannAlgebra (R.cornerProjection W) x)
    (hzero : vectorFunctional W.gnsVector (star x * x) = 0) : x = 0 :=
  R.faithful_cornerProjection W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra
    W.generatedByLocalAlgebra_localVonNeumannAlgebra hx hzero

/-- **Fullness of `q` in `M_Γ`, unconditionally.** -/
theorem cornerProjection_isFullProjection_localVonNeumannAlgebra :
    IsFullProjection W.localVonNeumannAlgebra (R.cornerProjection W) :=
  R.cornerProjection_isFullProjection W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra

/-- **The corner projection is nonzero, unconditionally.** -/
theorem cornerProjection_ne_zero_localVonNeumannAlgebra :
    R.cornerProjection W ≠ 0 :=
  R.cornerProjection_ne_zero W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra

/-- **Normalization `τ_q(q) = 1`, unconditionally.** -/
theorem vectorFunctional_cornerProjection_eq_one_localVonNeumannAlgebra :
    vectorFunctional W.gnsVector (R.cornerProjection W) = 1 :=
  R.vectorFunctional_cornerProjection_eq_one W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra

/--
**The main theorem of this packet.**  For a finite-range consistent stabilizer system on a
countable locally finite lattice, a quasilocal completion `Q` and its global stabilizer
state `W`, the canonical corner projection `q` of the represented local code-space supports
is a nonzero full projection of the manuscript's algebra `M_Γ = π_ω(𝒜_loc)''`, the corner
vector state `τ_q` is a faithful tracial state on `q M_Γ q`, and the whole
`SupportCornerConclusion` of FF20 holds — with **no** additional hypothesis.

(The no-type-III conclusion is *not* asserted here; that is FF23.)
-/
theorem supportCornerConclusion_localVonNeumannAlgebra :
    SupportCornerConclusion W.localVonNeumannAlgebra (R.cornerProjection W) W.gnsVector :=
  R.supportCornerConclusion W W.localVonNeumannAlgebra
    W.representation_mem_localVonNeumannAlgebra
    W.generatedByLocalAlgebra_localVonNeumannAlgebra

end FiniteRangeStabilizerSystem

end Assembly

end FiniteFiber
