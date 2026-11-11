import FiniteFiber.ActualStabilizerSupportCorner

/-!
# The finite-range geometric input for the support-corner construction

This file supplies the *geometric* data that
`FiniteFiber.ActualStabilizerSupportCorner` (FF20) still had to assume by hand:
a countable, locally finite lattice together with a **finite-range** consistent
stabilizer system, an explicit exhaustion of the lattice by finite regions, the
resulting increasing sequence of **finite** local stabilizer subgroups, and the
decreasing sequence of local code-space support projections in the supplied GNS
operator model, with its canonical strong limit.

## The data

`FiniteRangeStabilizerSystem Site` bundles

* a surjective enumeration `enumerate : ℕ → Site` (countability of the lattice);
* a finite `neighborhood : Site → Finset Site` with `s ∈ neighborhood s`
  (local finiteness: the range-`r` ball around a site is a finite region);
* pairwise-commuting involutive full-Pauli generators whose generated group
  omits `-1` (`FullPauliWord.StabilizerGeneratorData`, i.e. the manuscript's
  consistent stabilizer system); and
* the **finite-range condition** `generator_range`: every generator is
  supported inside a single neighborhood ball.

## What is proved here from that data alone

* `FiniteRangeStabilizerSystem.region` is a monotone exhaustion of `Site` by
  finite regions, each of which is a finite union of range balls
  (`region_mono`, `mem_region`, `exhaustion`).
* Finite range gives the *one-ball* statement
  `generator_supportedIn_region`: each generator already sits in the stage
  `k + 1` determined by the single site index enumerating the centre of its
  ball.  (For an arbitrary finite-support stabilizer one only gets the weaker
  `exists_region_superset`, which needs an induction over the finite support.)
* `localStabilizer n`, the group of global stabilizers supported in
  `region n`, is a subgroup of the global stabilizer group; it is **finite**
  (`localStabilizerFintype`), the sequence is increasing
  (`localStabilizer_mono`), and it exhausts the global stabilizer group
  (`exists_mem_localStabilizer`, `iSup_localStabilizer`).
* In the supplied GNS model of a `QuasilocalStabilizerState`, the local
  code-space supports `supportProjection W n = π_ω(P_{Γ_n})` form a decreasing
  sequence of projections in any von Neumann algebra `M` containing the
  represented finite local algebras, each fixes `Ω`, and each is nonzero
  (`supportProjectionSequence`, `supportProjection_gnsVector`,
  `supportProjection_ne_zero`).
* Their strong limit exists and is *constructed*, not assumed: the canonical
  `decreasingProjectionStrongLimit` of `FiniteFiber.StrongSupport` is a
  projection in `M`, fixes `Ω`, and is therefore **nonzero**
  (`cornerProjection_isProjectionIn`, `cornerProjection_gnsVector`,
  `cornerProjection_ne_zero`).  No strong-limit premise is needed.

* **Non-vacuity**: `natAllZFiniteRangeSystem` is an explicit finite-range
  consistent stabilizer system on the countably infinite lattice `ℕ` (the
  all-`Z` code, range zero) with nontrivial finite local stabilizer groups.

All of that is collected in `FiniteRangeSupportCornerData` and produced by
`FiniteRangeStabilizerSystem.supportCornerData`; feeding it to FF20 gives
`finiteRange_supportCornerConclusion_of_gnsOrbit`.

## What finite range does *not* give

The remaining inputs are exactly the analytic/global ones, and they stay
explicit premises:

* the quasilocal C-star completion `Q` and the global state `W` (existence of
  the state is Proposition `prop:define_state` of the manuscript; it is an
  interface input here);
* the von Neumann algebra `M` with `hM`;
* `GNSOrbitConditions M q Ω`: the regional/complementary commutation data, the
  dense product orbit (fullness of `q`) and traciality of the compressed vector
  functional on corner elements.

Also isolated here is the *local-code consistency* condition
`FiniteRangeStabilizerSystem.LocallyGenerated`: that the stabilizers supported
in `region n` are exactly the products of generators supported in `region n`.
Only the easy inclusion
`closure_localGenerators_le_regionStabilizer` follows from finite range; the
converse is an extra hypothesis, and it is what identifies the abstract local
code projection `P_{Γ_n}` with the projection built from the generators of the
code inside `Γ_n`.  None of the results below need it, because nonzeroness of
each `p n` is obtained from the fixed GNS vector instead; it is recorded because
any *local* computation of the code space (dimension counting, local
independence of generators) does need it.

No trace, fullness, type classification or no-type-III statement is claimed in
this file.
-/

namespace FiniteFiber

open scoped InnerProductSpace

variable {Site : Type*} [DecidableEq Site]

/-! ### The finite-range lattice/stabilizer data -/

/--
**A countable locally finite lattice with a finite-range consistent stabilizer
system.**  The lattice is presented by a surjective enumeration and by finite
neighbourhood balls containing their centres; the stabilizer system is a
`FullPauliWord.StabilizerGeneratorData` (pairwise commuting involutive
generators generating a group without `-1`) whose generators each fit inside a
single ball.
-/
structure FiniteRangeStabilizerSystem (Site : Type*) [DecidableEq Site] extends
    FullPauliWord.StabilizerGeneratorData Site where
  /-- A surjective enumeration of the lattice sites: the lattice is countable. -/
  enumerate : ℕ → Site
  /-- Every site is enumerated. -/
  enumerate_surjective : Function.Surjective enumerate
  /-- The finite range ball around a site: local finiteness of the lattice. -/
  neighborhood : Site → Finset Site
  /-- A site belongs to its own ball. -/
  self_mem_neighborhood : ∀ s, s ∈ neighborhood s
  /-- **Finite range**: every generator is supported inside a single ball. -/
  generator_range : ∀ g ∈ generators, ∃ s : Site, g.label.support ⊆ neighborhood s

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site)

/-! #### The exhaustion by finite regions -/

/-- The `n`-th finite region: the union of the balls around the first `n`
enumerated sites. -/
def region (n : ℕ) : Finset Site :=
  (Finset.range n).biUnion fun k => R.neighborhood (R.enumerate k)

theorem mem_region_iff (n : ℕ) (s : Site) :
    s ∈ R.region n ↔ ∃ k < n, s ∈ R.neighborhood (R.enumerate k) := by
  simp [region, Finset.mem_biUnion, Finset.mem_range]

/-- The regions increase. -/
theorem region_mono : Monotone R.region := by
  intro n m hnm s hs
  rw [mem_region_iff] at hs ⊢
  obtain ⟨k, hk, hsk⟩ := hs
  exact ⟨k, lt_of_lt_of_le hk hnm, hsk⟩

/-- The ball around the `k`-th enumerated site is already a subregion of stage
`k + 1`. -/
theorem neighborhood_subset_region (k : ℕ) :
    R.neighborhood (R.enumerate k) ⊆ R.region (k + 1) := by
  intro s hs
  exact (R.mem_region_iff _ s).mpr ⟨k, Nat.lt_succ_self k, hs⟩

/-- Every site is covered by some finite stage. -/
theorem mem_region (s : Site) : ∃ n, s ∈ R.region n := by
  obtain ⟨k, hk⟩ := R.enumerate_surjective s
  exact ⟨k + 1, R.neighborhood_subset_region k (hk ▸ R.self_mem_neighborhood s)⟩

/-- The regions form a finite-region exhaustion of the lattice. -/
def exhaustion : ProjectivePauliWord.FiniteExhaustion Site where
  region := R.region
  mono := R.region_mono
  cover := R.mem_region

/-- Every finite set of sites is contained in a stage of the exhaustion. -/
theorem exists_region_superset (F : Finset Site) : ∃ n, F ⊆ R.region n :=
  R.exhaustion.covers_finset F

/--
**The finite-range statement.**  A generator supported in the ball around
`enumerate k` is supported in the single region `region (k + 1)`; no induction
over its support is needed.
-/
theorem generator_supportedIn_region {g : FullPauliWord Site} (hg : g ∈ R.generators) :
    ∃ n, g.label.support ⊆ R.region n := by
  obtain ⟨s, hs⟩ := R.generator_range g hg
  obtain ⟨k, hk⟩ := R.enumerate_surjective s
  exact ⟨k + 1, hs.trans (hk ▸ R.neighborhood_subset_region k)⟩

/-! #### The induced consistent stabilizer system -/

/-- The consistent stabilizer system generated by the finite-range generators. -/
noncomputable def stabilizerSystem : FullPauliStabilizerSystem Site where
  group := Subgroup.closure R.generators
  involutive := fun g hg => R.toStabilizerGeneratorData.closure_involutive g hg
  consistent := R.no_negative_identity

@[simp] theorem stabilizerSystem_group :
    R.stabilizerSystem.group = Subgroup.closure R.generators := rfl

/-- Each generator is a global stabilizer. -/
theorem generator_mem_group {g : FullPauliWord Site} (hg : g ∈ R.generators) :
    g ∈ R.stabilizerSystem.group :=
  Subgroup.subset_closure hg

/-- The global stabilizer group is abelian, as the generators commute. -/
theorem stabilizerSystem_commute (g h : R.stabilizerSystem.group) :
    Commute (g : FullPauliWord Site) (h : FullPauliWord Site) :=
  R.toStabilizerGeneratorData.closure_commute _ _ g.2 h.2

/-! #### The increasing sequence of finite local stabilizer groups -/

/--
The local stabilizer group `G_{S,Γ_n}` of the manuscript, seen as a subgroup of
the global stabilizer group: the stabilizers supported in `region n`.
-/
noncomputable def localStabilizer (n : ℕ) : Subgroup ↥R.stabilizerSystem.group :=
  ((R.stabilizerSystem.regionStabilizer (R.region n)).group).comap
    R.stabilizerSystem.group.subtype

theorem mem_localStabilizer_iff (n : ℕ) (g : ↥R.stabilizerSystem.group) :
    g ∈ R.localStabilizer n ↔ (g : FullPauliWord Site).label.support ⊆ R.region n := by
  constructor
  · intro hg
    exact ((R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mp hg).2
  · intro hg
    exact (R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mpr ⟨g.2, hg⟩

/-- The local stabilizer groups increase along the exhaustion. -/
theorem localStabilizer_mono (n m : ℕ) (hnm : n ≤ m) :
    R.localStabilizer n ≤ R.localStabilizer m := by
  intro g hg
  rw [mem_localStabilizer_iff] at hg ⊢
  exact hg.trans (R.region_mono hnm)

/-- Every global stabilizer is local at some finite stage: the sequence of
local stabilizer groups exhausts the stabilizer group. -/
theorem exists_mem_localStabilizer (g : ↥R.stabilizerSystem.group) :
    ∃ n, g ∈ R.localStabilizer n := by
  obtain ⟨n, hn⟩ := R.exists_region_superset (g : FullPauliWord Site).label.support
  exact ⟨n, (R.mem_localStabilizer_iff n g).mpr hn⟩

/-- The local stabilizer groups have the whole stabilizer group as supremum. -/
theorem iSup_localStabilizer : (⨆ n : ℕ, R.localStabilizer n) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨n, hn⟩ := R.exists_mem_localStabilizer g
  exact Subgroup.mem_iSup_of_mem n hn

/-- Every generator is a member of some finite local stabilizer group. -/
theorem generator_mem_localStabilizer {g : FullPauliWord Site} (hg : g ∈ R.generators) :
    ∃ n, (⟨g, R.generator_mem_group hg⟩ : ↥R.stabilizerSystem.group) ∈
      R.localStabilizer n := by
  obtain ⟨n, hn⟩ := R.generator_supportedIn_region hg
  exact ⟨n, (R.mem_localStabilizer_iff n _).mpr hn⟩

/-- **Each local stabilizer group is finite**, by finite support alone. -/
noncomputable instance localStabilizerFintype (n : ℕ) :
    Fintype ↥(R.localStabilizer n) := by
  classical
  letI : Fintype ↥(FullPauliWord.localGroup (Site := Site) (R.region n)) :=
    FullPauliWord.localGroupFintype _
  have hinj : Function.Injective
      (fun g : ↥(R.localStabilizer n) =>
        (⟨(g : ↥R.stabilizerSystem.group), (R.mem_localStabilizer_iff n _).mp g.2⟩ :
          ↥(FullPauliWord.localGroup (Site := Site) (R.region n)))) := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(FullPauliWord.localGroup (Site := Site) (R.region n)) =>
      (x : FullPauliWord Site)) hgh
  have : Finite ↥(R.localStabilizer n) := Finite.of_injective _ hinj
  exact Fintype.ofFinite _

/-! #### The isolated local-code consistency condition -/

/--
**Local-code consistency along the exhaustion.**  The stabilizers supported in
`region n` are exactly the products of *generators* supported in `region n`.

This does **not** follow from finite range: a product of generators reaching
outside `region n` may well be supported inside it, and then the local code
space of `region n` is strictly smaller than the one cut out by the local
generators.  It is exactly the hypothesis needed to compute the local code
space, its dimension, or the local density from the generator set; none of the
theorems in this file assume it.
-/
def LocallyGenerated : Prop :=
  ∀ n : ℕ, (R.stabilizerSystem.regionStabilizer (R.region n)).group =
    Subgroup.closure {g | g ∈ R.generators ∧ g.label.support ⊆ R.region n}

/-- The inclusion of `LocallyGenerated` which *is* implied by finite range:
products of generators supported in a region are stabilizers supported there. -/
theorem closure_localGenerators_le_regionStabilizer (n : ℕ) :
    Subgroup.closure {g | g ∈ R.generators ∧ g.label.support ⊆ R.region n} ≤
      (R.stabilizerSystem.regionStabilizer (R.region n)).group := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro g ⟨hgen, hsupp⟩
  exact (R.stabilizerSystem.mem_regionStabilizer_group_iff _ _).mpr
    ⟨R.generator_mem_group hgen, hsupp⟩

end FiniteRangeStabilizerSystem

/-! ### Non-vacuity of the finite-range data -/

namespace FullPauliWord

/-- The full-Pauli words with trivial central phase and trivial `X` coordinate:
the phase-free `Z`-type words. -/
def phaseFreeZSubgroup (Site : Type*) : Subgroup (FullPauliWord Site) where
  carrier := {a | a.phase = 0 ∧ FullPauliWord.xCoordinate a.label = 0}
  one_mem' := ⟨rfl, map_zero _⟩
  mul_mem' := by
    rintro a b ⟨hap, hax⟩ ⟨hbp, hbx⟩
    refine ⟨?_, ?_⟩
    · show a.phase + b.phase + FullPauliWord.cocycle a.label b.label = 0
      rw [FullPauliWord.cocycle, hbx, FullPauliWord.binaryDot_zero_right, map_zero,
        hap, hbp]
      simp
    · show FullPauliWord.xCoordinate (a.label + b.label) = 0
      rw [map_add, hax, hbx, add_zero]
  inv_mem' := by
    rintro a ⟨hap, hax⟩
    refine ⟨?_, ?_⟩
    · show -a.phase - FullPauliWord.cocycle (-a.label) a.label = 0
      rw [FullPauliWord.cocycle, hax, FullPauliWord.binaryDot_zero_right, map_zero,
        hap]
      simp
    · show FullPauliWord.xCoordinate (-a.label) = 0
      rw [map_neg, hax, neg_zero]

theorem mem_phaseFreeZSubgroup_iff {Site : Type*} (a : FullPauliWord Site) :
    a ∈ phaseFreeZSubgroup Site ↔
      a.phase = 0 ∧ FullPauliWord.xCoordinate a.label = 0 := Iff.rfl

/-- Phase-free `Z`-type words commute: the Pauli cocycle vanishes on them. -/
theorem commute_of_mem_phaseFreeZSubgroup {Site : Type*} {a b : FullPauliWord Site}
    (ha : a ∈ phaseFreeZSubgroup Site) (hb : b ∈ phaseFreeZSubgroup Site) :
    Commute a b := by
  have hcab : FullPauliWord.cocycle a.label b.label = 0 := by
    rw [FullPauliWord.cocycle, hb.2, FullPauliWord.binaryDot_zero_right, map_zero]
  have hcba : FullPauliWord.cocycle b.label a.label = 0 := by
    rw [FullPauliWord.cocycle, ha.2, FullPauliWord.binaryDot_zero_right, map_zero]
  show a * b = b * a
  apply FullPauliWord.ext
  · show a.phase + b.phase + FullPauliWord.cocycle a.label b.label =
      b.phase + a.phase + FullPauliWord.cocycle b.label a.label
    rw [hcab, hcba, add_comm a.phase b.phase]
  · show a.label + b.label = b.label + a.label
    exact add_comm _ _

/-- The excluded central word `-1` is not phase free. -/
theorem negativeIdentity_not_mem_phaseFreeZSubgroup (Site : Type*) :
    FullPauliWord.negativeIdentity (Site := Site) ∉ phaseFreeZSubgroup Site := by
  intro h
  have hphase : (2 : ZMod 4) = 0 := h.1
  exact absurd hphase (by decide)

end FullPauliWord

omit [DecidableEq Site] in
/-- The one-site `Z` word is a phase-free `Z`-type word. -/
theorem zWord_mem_phaseFreeZSubgroup (s : Site) :
    zWord s ∈ FullPauliWord.phaseFreeZSubgroup Site := by
  refine ⟨rfl, ?_⟩
  show Finsupp.mapRange.addMonoidHom _ (Finsupp.single s ((0, 1) : ZMod 2 × ZMod 2)) = 0
  simp [Finsupp.mapRange_single]

/--
**Non-vacuity of the finite-range hypotheses.**  The all-`Z` stabilizer system
on the countably infinite lattice `ℕ`, with range-zero neighbourhoods
`{s}`, is a finite-range consistent stabilizer system in the above sense.
-/
noncomputable def natAllZFiniteRangeSystem : FiniteRangeStabilizerSystem ℕ where
  generators := Set.range zWord
  pairwise_commute := by
    rintro a ⟨s, rfl⟩ b ⟨t, rfl⟩ _
    exact FullPauliWord.commute_of_mem_phaseFreeZSubgroup
      (zWord_mem_phaseFreeZSubgroup s) (zWord_mem_phaseFreeZSubgroup t)
  generator_involutive := by
    rintro a ⟨s, rfl⟩
    exact zWord_mul_self s
  no_negative_identity := by
    intro hmem
    have hle : Subgroup.closure (Set.range (zWord (Site := ℕ))) ≤
        FullPauliWord.phaseFreeZSubgroup ℕ := by
      rw [Subgroup.closure_le]
      rintro a ⟨s, rfl⟩
      exact zWord_mem_phaseFreeZSubgroup s
    exact FullPauliWord.negativeIdentity_not_mem_phaseFreeZSubgroup ℕ (hle hmem)
  enumerate := id
  enumerate_surjective := Function.surjective_id
  neighborhood := fun s => {s}
  self_mem_neighborhood := fun s => Finset.mem_singleton_self s
  generator_range := by
    rintro a ⟨s, rfl⟩
    exact ⟨s, zWord_support s⟩

/-- The all-`Z` finite-range system has nontrivial finite local stabilizer
groups: the `Z` stabilizer at site `k` is local at every stage `n > k`. -/
theorem zWord_mem_natAllZ_localStabilizer {k n : ℕ} (hkn : k < n) :
    (⟨zWord k, natAllZFiniteRangeSystem.generator_mem_group ⟨k, rfl⟩⟩ :
        ↥natAllZFiniteRangeSystem.stabilizerSystem.group) ∈
      natAllZFiniteRangeSystem.localStabilizer n := by
  refine (natAllZFiniteRangeSystem.mem_localStabilizer_iff n _).mpr ?_
  refine (zWord_support k).trans ?_
  intro s hs
  rw [Finset.mem_singleton] at hs
  subst hs
  exact (natAllZFiniteRangeSystem.mem_region_iff n s).mpr ⟨s, hkn, Finset.mem_singleton_self s⟩

/-! ### The bundled operator-side output handed to FF20 -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
**The support-corner input data.**  A decreasing sequence `p` of projections of
`M`, each fixing the unit vector `xi` and hence nonzero, together with its
strong limit `q`, which is again a projection of `M` fixing `xi` and nonzero.

This is exactly the geometric/operator-algebraic package which the abstract
support-corner theorem consumes; the remaining `GNSOrbitConditions` are the
analytic inputs and are not part of it.
-/
structure FiniteRangeSupportCornerData (M : VonNeumannAlgebra H)
    (p : ℕ → H →L[ℂ] H) (q : H →L[ℂ] H) (xi : H) where
  /-- The finite stages are a decreasing sequence of projections of `M`. -/
  decreasing : DecreasingProjectionSequence M p
  /-- Every finite stage fixes the distinguished vector. -/
  stage_fixes : ∀ n : ℕ, p n xi = xi
  /-- Hence every finite stage is nonzero. -/
  stage_ne_zero : ∀ n : ℕ, p n ≠ 0
  /-- The stages converge strongly to `q`. -/
  tendsTo : StronglyTendsTo p q
  /-- The limit is a projection of `M`. -/
  q_projection : IsProjectionIn M q
  /-- The limit fixes the distinguished vector. -/
  q_fixes : q xi = xi
  /-- Hence the candidate corner projection is nonzero. -/
  q_ne_zero : q ≠ 0

namespace FiniteRangeStabilizerSystem

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}

/-- The represented local code-space support of the region `Γ_n`:
`π_ω(P_{Γ_n})`, the average of the finite local stabilizer group. -/
noncomputable def supportProjection (W : QuasilocalStabilizerState R.stabilizerSystem Q)
    (n : ℕ) : W.GNS →L[ℂ] W.GNS :=
  stabilizerAverageSequence W.stabilizerAction R.localStabilizer n

theorem supportProjection_eq (W : QuasilocalStabilizerState R.stabilizerSystem Q) :
    R.supportProjection W = stabilizerAverageSequence W.stabilizerAction R.localStabilizer :=
  rfl

/-- **The decreasing sequence of local code-space supports.**  It uses only the
exhaustion and the increasing finite local stabilizer groups. -/
theorem supportProjectionSequence (W : QuasilocalStabilizerState R.stabilizerSystem Q)
    (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    DecreasingProjectionSequence M (R.supportProjection W) :=
  stabilizerAverageSequence_decreasingProjectionSequence W.stabilizerAction
    R.localStabilizer
    (fun _ s => W.stabilizerRepresentation_mem hM (s : ↥R.stabilizerSystem.group))
    R.localStabilizer_mono

/-- Each local code-space support fixes the GNS vector. -/
theorem supportProjection_gnsVector (W : QuasilocalStabilizerState R.stabilizerSystem Q)
    (n : ℕ) : R.supportProjection W n W.gnsVector = W.gnsVector :=
  stabilizerAverageSequence_fixes W.stabilizerAction R.localStabilizer W.gnsVector
    (fun _ s => W.stabilizerAction_representation_gnsVector
      (s : ↥R.stabilizerSystem.group)) n

/-- The GNS vector is nonzero, since it is a unit vector. -/
theorem gnsVector_ne_zero (W : QuasilocalStabilizerState R.stabilizerSystem Q) :
    W.gnsVector ≠ 0 := by
  intro h
  have := W.norm_gnsVector
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Each local code-space support is nonzero: the code space contains `Ω`. -/
theorem supportProjection_ne_zero (W : QuasilocalStabilizerState R.stabilizerSystem Q)
    (n : ℕ) : R.supportProjection W n ≠ 0 :=
  stabilizerAverageSequence_ne_zero W.stabilizerAction R.localStabilizer
    (R.gnsVector_ne_zero W)
    (fun _ s => W.stabilizerAction_representation_gnsVector
      (s : ↥R.stabilizerSystem.group)) n

/--
**The candidate corner projection.**  The strong limit of the decreasing local
code-space supports; it is *constructed* (as the canonical strong limit of
`FiniteFiber.StrongSupport`), so no convergence premise is required.
-/
noncomputable def cornerProjection (W : QuasilocalStabilizerState R.stabilizerSystem Q) :
    W.GNS →L[ℂ] W.GNS :=
  decreasingProjectionStrongLimit (R.supportProjection W)

theorem stronglyTendsTo_cornerProjection
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    StronglyTendsTo (R.supportProjection W) (R.cornerProjection W) :=
  (R.supportProjectionSequence W M hM).stronglyTendsTo_decreasingProjectionStrongLimit

theorem cornerProjection_isProjectionIn
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    IsProjectionIn M (R.cornerProjection W) :=
  (R.supportProjectionSequence W M hM).decreasingProjectionStrongLimit_isProjectionIn

theorem cornerProjection_gnsVector
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    R.cornerProjection W W.gnsVector = W.gnsVector :=
  (R.supportProjectionSequence W M hM).decreasingProjectionStrongLimit_fixes
    (R.supportProjection_gnsVector W)

/-- **The candidate corner projection is nonzero**, because it fixes the unit
GNS vector. -/
theorem cornerProjection_ne_zero
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    R.cornerProjection W ≠ 0 := by
  intro hzero
  have hfix := R.cornerProjection_gnsVector W M hM
  rw [hzero] at hfix
  exact R.gnsVector_ne_zero W (by simpa using hfix.symm)

/--
**The main construction.**  From a countable locally finite lattice with a
finite-range consistent stabilizer system, a quasilocal completion `Q`, a
global stabilizer state `W`, and a von Neumann algebra `M` containing the
represented finite local algebras, the decreasing local code-space supports and
their strong limit — a nonzero candidate corner projection fixing `Ω` — are
constructed.  No analytic hypothesis beyond `hM` enters.
-/
noncomputable def supportCornerData
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M) :
    FiniteRangeSupportCornerData M (R.supportProjection W) (R.cornerProjection W)
      W.gnsVector where
  decreasing := R.supportProjectionSequence W M hM
  stage_fixes := R.supportProjection_gnsVector W
  stage_ne_zero := R.supportProjection_ne_zero W
  tendsTo := R.stronglyTendsTo_cornerProjection W M hM
  q_projection := R.cornerProjection_isProjectionIn W M hM
  q_fixes := R.cornerProjection_gnsVector W M hM
  q_ne_zero := R.cornerProjection_ne_zero W M hM

end FiniteRangeStabilizerSystem

/-! ### Feeding the construction to FF20 -/

section FiniteRangeModel

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}

/--
**The support-corner theorem at a finite-range stabilizer system.**

The lattice geometry (exhaustion), the finite local stabilizer groups, the
decreasing local code-space supports, their strong limit `q`, its projection
property, its invariance under the GNS vector and its nonvanishing are all
*constructed* from the finite-range data.  The remaining hypotheses are exactly
the global analytic ones: the quasilocal completion `Q`, the state `W`, the
algebra `M` with `hM`, and the GNS-orbit conditions `C` (regional commutation,
dense product orbit, corner traciality).
-/
theorem finiteRange_supportCornerConclusion_of_gnsOrbit
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (C : GNSOrbitConditions M (R.cornerProjection W) W.gnsVector) :
    SupportCornerConclusion M (R.cornerProjection W) W.gnsVector :=
  actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit W M hM
    R.localStabilizer R.localStabilizer_mono
    (R.stronglyTendsTo_cornerProjection W M hM) C

/--
The manuscript's every-nonzero-central-summand statement at a finite-range
stabilizer system: for every nonzero central projection `z` of `M`, the
compression `z * q` is a nonzero finite projection of `M` below `z`.
-/
theorem finiteRange_central_witness_of_gnsOrbit
    (W : QuasilocalStabilizerState R.stabilizerSystem Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (C : GNSOrbitConditions M (R.cornerProjection W) W.gnsVector)
    (z : W.GNS →L[ℂ] W.GNS) (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    IsFiniteProjection M (z * R.cornerProjection W) ∧ z * R.cornerProjection W ≠ 0 ∧
      IsSubprojection (z * R.cornerProjection W) z :=
  (finiteRange_supportCornerConclusion_of_gnsOrbit R W M hM C).central_witness z hz
    hz_nonzero

end FiniteRangeModel

end FiniteFiber
