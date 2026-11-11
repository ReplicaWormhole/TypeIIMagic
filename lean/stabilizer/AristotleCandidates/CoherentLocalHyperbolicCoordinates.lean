import Formalization.SymplecticCoordinates
import Formalization.AdaptedStabilizerSubspace
import Formalization.CoherentBasisEquiv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Noetherian.Basic

/-!
# P52 — coherent local-hyperbolic coordinate blocks

Context declaration: **source basis** `main.tex:1671-1679` (the definition of
short-range order: a symplectic basis `{z_i , x_i : i ∈ I}` of `V_Γ` with
`|I| = |Γ|`, a selected subset `P ⊆ I` with
`W_Γ = span_{F₂} {z_i : i ∈ P}`, and the locality clause *every hyperbolic
pair is local, i.e. every `x_i , z_i` is supported on a finite region*) and
`main.tex:1898-1939` (the finite-region restriction `F ⋐ I` used in the
proposed proof of the short-range regional-algebra theorem).

This module builds, from exactly that data, the **finite coordinate blocks**
along a lattice exhaustion, their **coherent (monotone, exhausting) inclusion
system**, and the block-restricted coordinate maps that later phase
calibration consumes.

## The audit question: does finite support alone give locally finite blocks?

**No.**  Locality of each hyperbolic pair (finite support) is modelled here by
working in the finitely supported phase space
`PauliCoordinateLabels L = (L ⊕ L) →₀ PauliBit`, so *every* label of this
module is finitely supported.  Nevertheless the block

`coordinateBlock n = {i | z i and x i are supported in the finite region Λ n}`

can be infinite: `exists_infinite_coordinateBlock_of_no_independence`
exhibits a locally supported family whose every block is infinite.

What rescues local finiteness is the *other* half of the manuscript clause,
namely that `{z_i , x_i}` is a symplectic **basis**, in particular a linearly
independent family.  `coordinateBlock_finite` proves: for a linearly
independent locally supported family, every block is finite, and
`coordinateBlock_card_le` bounds its cardinality by `|Λ n|`, matching the
manuscript's `|I| = |Γ|`.

## Auxiliary assumptions (the result is conditional on these)

1. `LocalHyperbolicFamily.indep`: the combined family `Sum.elim z x` is
   `F₂`-linearly independent.  This is implied by the manuscript's word
   "symplectic basis" but is not literally a separate clause there, so it is a
   named field.  It is exactly what is used for local finiteness and for
   injectivity of the coordinate map; the symplectic pairing values themselves
   are *not* used in this packet and are therefore not assumed.
2. `LatticeExhaustion`: a monotone sequence of finite regions covering the
   lattice.  The manuscript uses finite subregions `F ⋐ I` without fixing an
   exhaustion, so the exhaustion is supplied data.
3. `LocalHyperbolicFamily.selected`: the manuscript's subset `P ⊆ I`.  Only
   its block restriction is used here; no stabilizer-state property of `P` is
   assumed or claimed.

No local-finiteness or coherence property is assumed: both are **proved** from
(1)–(2).

## The packaged output

`LocalHyperbolicFamily.blockSystem` bundles the construction into a
`CoordinateBlockSystem`: finite blocks, their monotone exhaustion, the finite
source and target Pauli label blocks with their inclusion coherence and
exhaustion, and one injective coordinate map compatible with every block.
This is the data later phase calibration consumes.

## What is *not* claimed

Nothing about C⋆-algebras, states, GNS representations, tensor factorizations,
factorhood, traces or weights occurs here.  This packet is finite-dimensional
`F₂`-linear algebra over a lattice exhaustion.
-/

namespace StabilizerHyperfinite

namespace CoherentLocalHyperbolic

open Finsupp

/-! ### Locally supported phase-space labels -/

/-- The `F₂` phase space of a lattice `L`: finitely supported `Z`/`X`
coordinates on sites.  `Sum.inl a` is the `Z` coordinate of the site `a`,
`Sum.inr a` its `X` coordinate.  Finite support is the manuscript's locality
clause `main.tex:1678`. -/
abbrev PhaseSpace (L : Type*) := PauliCoordinateLabels L

/-- The site of a phase-space coordinate. -/
def site {L : Type*} : L ⊕ L → L := Sum.elim id id

/-- The subspace of phase-space vectors supported on the region `S`. -/
def supportedOn (L : Type*) (S : Set L) : Submodule PauliBit (PhaseSpace L) :=
  Finsupp.supported PauliBit PauliBit {p | site p ∈ S}

theorem mem_supportedOn_iff {L : Type*} (S : Set L) (v : PhaseSpace L) :
    v ∈ supportedOn L S ↔ ∀ p ∈ v.support, site p ∈ S := by
  rw [supportedOn, Finsupp.mem_supported]
  exact ⟨fun h _ hp => h hp, fun h _ hp => h _ hp⟩

theorem supportedOn_mono {L : Type*} {S T : Set L} (h : S ⊆ T) :
    supportedOn L S ≤ supportedOn L T := by
  intro v hv
  rw [mem_supportedOn_iff] at hv ⊢
  exact fun p hp => h (hv p hp)

/-- Every phase-space vector is supported on a finite region: this is the
locality of the model, and it is automatic for finitely supported labels. -/
theorem exists_finite_support {L : Type*} (v : PhaseSpace L) :
    ∃ S : Finset L, v ∈ supportedOn L (S : Set L) := by
  classical
  refine ⟨v.support.image site, ?_⟩
  rw [mem_supportedOn_iff]
  intro p hp
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp)

/-- The coordinate index set of a finite region is finite. -/
theorem finite_coordinates_of_finite_region {L : Type*} {S : Set L} (hS : S.Finite) :
    {p : L ⊕ L | site p ∈ S}.Finite := by
  have hsub : {p : L ⊕ L | site p ∈ S} ⊆ Sum.inl '' S ∪ Sum.inr '' S := by
    rintro (a | a) h
    · exact Or.inl ⟨a, h, rfl⟩
    · exact Or.inr ⟨a, h, rfl⟩
  exact Set.Finite.subset ((hS.image _).union (hS.image _)) hsub

/-- Phase-space vectors supported on a finite region form a finite module. -/
theorem supportedOn_moduleFinite {L : Type*} {S : Set L} (hS : S.Finite) :
    Module.Finite PauliBit (supportedOn L S) := by
  have hfin := (finite_coordinates_of_finite_region hS).to_subtype
  exact Module.Finite.equiv
    (Finsupp.supportedEquivFinsupp (M := PauliBit) (R := PauliBit)
      {p : L ⊕ L | site p ∈ S}).symm

/-- The coordinates of a region split into its `Z` and `X` coordinates. -/
def coordinateIndexEquiv {L : Type*} (S : Set L) :
    ↑{p : L ⊕ L | site p ∈ S} ≃ (S ⊕ S) where
  toFun := fun p => match p with
    | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
    | ⟨Sum.inr a, ha⟩ => Sum.inr ⟨a, ha⟩
  invFun := fun q => match q with
    | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a, ha⟩
    | Sum.inr ⟨a, ha⟩ => ⟨Sum.inr a, ha⟩
  left_inv := by rintro ⟨a | a, hp⟩ <;> rfl
  right_inv := by rintro (⟨a, ha⟩ | ⟨a, ha⟩) <;> rfl

/-- A finite region carries exactly two `F₂` coordinates per site. -/
theorem finrank_supportedOn {L : Type*} {S : Set L} (hS : S.Finite) :
    Module.finrank PauliBit (supportedOn L S) = 2 * Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hS.to_subtype
  haveI := (finite_coordinates_of_finite_region hS).to_subtype
  haveI : Fintype ↑{p : L ⊕ L | site p ∈ S} := Fintype.ofFinite _
  haveI : Fintype S := Fintype.ofFinite _
  rw [supportedOn, LinearEquiv.finrank_eq
      (Finsupp.supportedEquivFinsupp (M := PauliBit) (R := PauliBit)
        {p : L ⊕ L | site p ∈ S}), Module.finrank_finsupp_self,
    Fintype.card_congr (coordinateIndexEquiv S), Fintype.card_sum,
    Nat.card_eq_fintype_card]
  ring

/-! ### Lattice exhaustions -/

/-- A monotone exhaustion of the lattice by finite regions.  The manuscript
uses finite subregions without fixing an exhaustion, so this is supplied
data. -/
structure LatticeExhaustion (L : Type*) where
  /-- The finite region at stage `n`. -/
  region : ℕ → Finset L
  /-- The regions increase. -/
  mono : Monotone region
  /-- Every site is eventually covered. -/
  covers : ∀ a : L, ∃ n, a ∈ region n

namespace LatticeExhaustion

variable {L : Type*} (E : LatticeExhaustion L)

/-- An exhaustion absorbs every finite set of sites. -/
theorem absorbs (S : Finset L) : ∃ n, (S : Set L) ⊆ (E.region n : Set L) := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a S _ ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm⟩ := E.covers a
      refine ⟨max n m, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp (by exact_mod_cast hb) with rfl | hbS
      · exact E.mono (le_max_right n m) hm
      · exact E.mono (le_max_left n m) (hn hbS)

/-- Every phase-space vector is supported in some stage of the exhaustion. -/
theorem exists_mem_supportedOn (v : PhaseSpace L) :
    ∃ n, v ∈ supportedOn L (E.region n : Set L) := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_support v
  obtain ⟨n, hn⟩ := E.absorbs S
  exact ⟨n, supportedOn_mono hn hS⟩

/-- Finite target Pauli labels at stage `n`: phase-space vectors supported on
the stage-`n` region. -/
def targetLabels (n : ℕ) : Submodule PauliBit (PhaseSpace L) :=
  supportedOn L (E.region n : Set L)

/-- **Inclusion coherence, target side.** -/
theorem targetLabels_mono : Monotone E.targetLabels := by
  intro n m hnm
  exact supportedOn_mono (by exact_mod_cast E.mono hnm)

/-- The target label blocks exhaust the phase space. -/
theorem iSup_targetLabels : (⨆ n, E.targetLabels n) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨n, hn⟩ := E.exists_mem_supportedOn v
  exact Submodule.mem_iSup_of_mem n hn

/-- Each finite target label block is a finite `F₂`-module. -/
theorem targetLabels_moduleFinite (n : ℕ) :
    Module.Finite PauliBit (E.targetLabels n) :=
  supportedOn_moduleFinite (E.region n).finite_toSet

end LatticeExhaustion

/-! ### Locally supported adapted hyperbolic families -/

/-- The manuscript's local-hyperbolic data (`main.tex:1671-1679`): hyperbolic
pairs `(z i, x i)` of the phase space, each supported on a finite region
(automatic in this finitely supported model), together with the selected
subset `P = selected` labelling the local stabilizer generators.

The field `indep` is the auxiliary assumption isolating the part of "symplectic
basis" this packet uses; the symplectic pairing values are deliberately not
assumed, since no result below needs them. -/
structure LocalHyperbolicFamily (L I : Type*) where
  /-- The `Z` member of the hyperbolic pair labelled `i`. -/
  z : I → PhaseSpace L
  /-- The `X` member of the hyperbolic pair labelled `i`. -/
  x : I → PhaseSpace L
  /-- Auxiliary assumption: the adapted family is `F₂`-linearly independent. -/
  indep : LinearIndependent PauliBit (Sum.elim z x)
  /-- The manuscript's selected subset `P ⊆ I`. -/
  selected : Set I

namespace LocalHyperbolicFamily

variable {L I : Type*} (F : LocalHyperbolicFamily L I) (E : LatticeExhaustion L)

/-- The coordinate map sending a finite Pauli coordinate word over `I` to the
phase-space vector it labels. -/
noncomputable def coordinateMap : PauliCoordinateLabels I →ₗ[PauliBit] PhaseSpace L :=
  Finsupp.linearCombination PauliBit (Sum.elim F.z F.x)

theorem coordinateMap_single_z (i : I) :
    F.coordinateMap (Finsupp.single (Sum.inl i) 1) = F.z i := by
  simp [coordinateMap]

theorem coordinateMap_single_x (i : I) :
    F.coordinateMap (Finsupp.single (Sum.inr i) 1) = F.x i := by
  simp [coordinateMap]

/-- Linear independence makes the coordinate map injective: distinct finite
coordinate words label distinct phase-space vectors. -/
theorem coordinateMap_injective : Function.Injective F.coordinateMap :=
  F.indep

/-! ### The finite coordinate blocks -/

/-- The coordinate block at stage `n`: the labels whose whole hyperbolic pair
is supported inside the finite region `Λ n`. -/
def coordinateBlock (n : ℕ) : Set I :=
  {i | F.z i ∈ supportedOn L (E.region n : Set L) ∧
      F.x i ∈ supportedOn L (E.region n : Set L)}

/-- The coordinate blocks increase along the exhaustion. -/
theorem coordinateBlock_mono : Monotone (F.coordinateBlock E) := by
  intro n m hnm i hi
  have h : (E.region n : Set L) ⊆ (E.region m : Set L) := by
    exact_mod_cast E.mono hnm
  exact ⟨supportedOn_mono h hi.1, supportedOn_mono h hi.2⟩

/-- The coordinate blocks exhaust the label set. -/
theorem exists_mem_coordinateBlock (i : I) : ∃ n, i ∈ F.coordinateBlock E n := by
  obtain ⟨n, hn⟩ := E.exists_mem_supportedOn (F.z i)
  obtain ⟨m, hm⟩ := E.exists_mem_supportedOn (F.x i)
  refine ⟨max n m, ?_⟩
  have hn' : (E.region n : Set L) ⊆ (E.region (max n m) : Set L) := by
    exact_mod_cast E.mono (le_max_left n m)
  have hm' : (E.region m : Set L) ⊆ (E.region (max n m) : Set L) := by
    exact_mod_cast E.mono (le_max_right n m)
  exact ⟨supportedOn_mono hn' hn, supportedOn_mono hm' hm⟩

theorem iUnion_coordinateBlock : (⋃ n, F.coordinateBlock E n) = Set.univ := by
  ext i
  simpa using F.exists_mem_coordinateBlock E i

/-- The block-restricted hyperbolic family, viewed inside the finite
dimensional space of vectors supported on the stage-`n` region. -/
def blockFamily (n : ℕ) :
    (F.coordinateBlock E n) ⊕ (F.coordinateBlock E n) →
      E.targetLabels n :=
  Sum.elim (fun i => ⟨F.z i.1, i.2.1⟩) (fun i => ⟨F.x i.1, i.2.2⟩)

/-- The block-restricted hyperbolic family is linearly independent inside the
finite-dimensional stage-`n` target block. -/
theorem blockFamily_linearIndependent (n : ℕ) :
    LinearIndependent PauliBit (F.blockFamily E n) := by
  have hcomp : (E.targetLabels n).subtype ∘ F.blockFamily E n =
      (Sum.elim F.z F.x) ∘
        (Sum.map (Subtype.val : (F.coordinateBlock E n) → I)
          (Subtype.val : (F.coordinateBlock E n) → I)) := by
    funext p
    rcases p with i | i <;> rfl
  have hmap : Function.Injective
      (Sum.map (Subtype.val : (F.coordinateBlock E n) → I)
        (Subtype.val : (F.coordinateBlock E n) → I)) := by
    intro p q hpq
    rcases p with i | i <;> rcases q with j | j <;>
      simp_all [Sum.map, Subtype.ext_iff]
  apply LinearIndependent.of_comp (E.targetLabels n).subtype
  rw [hcomp]
  exact F.indep.comp _ hmap

/-- **Local finiteness.**  Each coordinate block is finite.  Finite support
alone does *not* give this (see
`exists_infinite_coordinateBlock_of_no_independence`); the proof uses the
linear independence field of the family. -/
theorem coordinateBlock_finite (n : ℕ) : (F.coordinateBlock E n).Finite := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite PauliBit (E.targetLabels n) := E.targetLabels_moduleFinite n
  haveI : IsNoetherian PauliBit (E.targetLabels n) := inferInstance
  have : Finite ((F.coordinateBlock E n) ⊕ (F.coordinateBlock E n)) :=
    (F.blockFamily_linearIndependent E n).finite_of_isNoetherian
  have : Finite (F.coordinateBlock E n) :=
    Finite.of_injective
      (Sum.inl : (F.coordinateBlock E n) → (F.coordinateBlock E n) ⊕ (F.coordinateBlock E n))
      Sum.inl_injective
  exact Set.toFinite _

/-- **Quantitative local finiteness.**  The stage-`n` coordinate block has at
most `|Λ n|` labels, matching the manuscript's `|I| = |Γ|`. -/
theorem coordinateBlock_card_le (n : ℕ) :
    Nat.card (F.coordinateBlock E n) ≤ (E.region n).card := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite PauliBit (E.targetLabels n) := E.targetLabels_moduleFinite n
  haveI := (F.coordinateBlock_finite E n).to_subtype
  haveI : Fintype (F.coordinateBlock E n) := Fintype.ofFinite _
  have hcard := (F.blockFamily_linearIndependent E n).fintype_card_le_finrank
  rw [Fintype.card_sum] at hcard
  have hrank : Module.finrank PauliBit (E.targetLabels n) = 2 * (E.region n).card := by
    rw [LatticeExhaustion.targetLabels,
      finrank_supportedOn (E.region n).finite_toSet]
    simp
  rw [hrank] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

/-- The coordinate block at stage `n`, as a finite set of labels. -/
noncomputable def blockFinset (n : ℕ) : Finset I :=
  (F.coordinateBlock_finite E n).toFinset

@[simp] theorem mem_blockFinset (n : ℕ) (i : I) :
    i ∈ F.blockFinset E n ↔ i ∈ F.coordinateBlock E n :=
  Set.Finite.mem_toFinset _

/-! ### Finite source and target coordinate labels -/

/-- Finite source Pauli labels at stage `n`: coordinate words supported on the
stage-`n` coordinate block. -/
def sourceLabels (n : ℕ) : Submodule PauliBit (PauliCoordinateLabels I) :=
  Finsupp.supported PauliBit PauliBit {p : I ⊕ I | site p ∈ F.coordinateBlock E n}

theorem mem_sourceLabels_iff (n : ℕ) (c : PauliCoordinateLabels I) :
    c ∈ F.sourceLabels E n ↔ ∀ p ∈ c.support, site p ∈ F.coordinateBlock E n := by
  rw [sourceLabels, Finsupp.mem_supported]
  exact ⟨fun h _ hp => h hp, fun h _ hp => h _ hp⟩

/-- **Inclusion coherence, source side.** -/
theorem sourceLabels_mono : Monotone (F.sourceLabels E) := by
  intro n m hnm c hc
  rw [mem_sourceLabels_iff] at hc ⊢
  exact fun p hp => F.coordinateBlock_mono E hnm (hc p hp)

/-- The source label blocks exhaust all finite coordinate words. -/
theorem iSup_sourceLabels : (⨆ n, F.sourceLabels E n) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro c _
  have hchoice : ∀ p ∈ c.support, ∃ n, site p ∈ F.coordinateBlock E n :=
    fun p _ => F.exists_mem_coordinateBlock E (site p)
  choose stage hstage using hchoice
  set N : ℕ := c.support.attach.sup (fun p => stage p.1 p.2) with hN
  have hmem : c ∈ F.sourceLabels E N := by
    rw [mem_sourceLabels_iff]
    intro p hp
    have hle : stage p hp ≤ N := Finset.le_sup (f := fun q : c.support => stage q.1 q.2)
      (Finset.mem_attach _ ⟨p, hp⟩)
    exact F.coordinateBlock_mono E hle (hstage p hp)
  exact Submodule.mem_iSup_of_mem N hmem

/-- **The block coordinate map is block-supported**: stage-`n` source labels
are sent to stage-`n` target labels.  This is the compatibility that makes the
finite coordinate blocks usable as finite stages. -/
theorem coordinateMap_sourceLabels_le (n : ℕ) :
    (F.sourceLabels E n).map F.coordinateMap ≤ E.targetLabels n := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  intro c hc
  rw [Submodule.mem_comap]
  have hsupp : ∀ p ∈ c.support, site p ∈ F.coordinateBlock E n :=
    (F.mem_sourceLabels_iff E n c).mp hc
  have : F.coordinateMap c = ∑ p ∈ c.support, c p • Sum.elim F.z F.x p := by
    simp [coordinateMap, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [this]
  refine Submodule.sum_mem _ ?_
  intro p hp
  refine Submodule.smul_mem _ _ ?_
  rcases p with i | i
  · exact (hsupp _ hp).1
  · exact (hsupp _ hp).2

/-- The stage-`n` coordinate map between the finite label blocks. -/
noncomputable def blockCoordinateMap (n : ℕ) :
    F.sourceLabels E n →ₗ[PauliBit] E.targetLabels n :=
  (F.coordinateMap.restrict (p := F.sourceLabels E n) (q := E.targetLabels n)
    (fun _ hc => F.coordinateMap_sourceLabels_le E n
      (Submodule.mem_map_of_mem hc)))

@[simp] theorem blockCoordinateMap_coe (n : ℕ) (c : F.sourceLabels E n) :
    ((F.blockCoordinateMap E n c : PhaseSpace L)) = F.coordinateMap (c : PauliCoordinateLabels I) :=
  rfl

/-- Each block coordinate map is injective. -/
theorem blockCoordinateMap_injective (n : ℕ) :
    Function.Injective (F.blockCoordinateMap E n) := by
  intro c d hcd
  have : F.coordinateMap (c : PauliCoordinateLabels I) =
      F.coordinateMap (d : PauliCoordinateLabels I) := congrArg Subtype.val hcd
  exact Subtype.ext (F.coordinateMap_injective this)

/-- **Coherence of the block coordinate maps with the inclusions.**  Enlarging
the finite region before or after applying the coordinate map gives the same
result, so the blocks form a coherent inductive system. -/
theorem blockCoordinateMap_inclusion {n m : ℕ} (hnm : n ≤ m)
    (c : F.sourceLabels E n) :
    F.blockCoordinateMap E m (Submodule.inclusion (F.sourceLabels_mono E hnm) c) =
      Submodule.inclusion (E.targetLabels_mono hnm) (F.blockCoordinateMap E n c) :=
  rfl

/-- Each finite source label block is a finite `F₂`-module. -/
theorem sourceLabels_moduleFinite (n : ℕ) :
    Module.Finite PauliBit (F.sourceLabels E n) := by
  classical
  have hfin : {p : I ⊕ I | site p ∈ F.coordinateBlock E n}.Finite := by
    have hsub : {p : I ⊕ I | site p ∈ F.coordinateBlock E n} ⊆
        Sum.inl '' (F.coordinateBlock E n) ∪ Sum.inr '' (F.coordinateBlock E n) := by
      rintro (a | a) h
      · exact Or.inl ⟨a, h, rfl⟩
      · exact Or.inr ⟨a, h, rfl⟩
    exact Set.Finite.subset
      (((F.coordinateBlock_finite E n).image _).union
        ((F.coordinateBlock_finite E n).image _)) hsub
  haveI := hfin.to_subtype
  exact Module.Finite.equiv
    (Finsupp.supportedEquivFinsupp (M := PauliBit) (R := PauliBit)
      {p : I ⊕ I | site p ∈ F.coordinateBlock E n}).symm

/-! ### Data for later phase calibration -/

/-- The selected labels of stage `n`: the manuscript's `P ∩ F` for the finite
block `F`. -/
def selectedBlock (n : ℕ) : Set I := F.selected ∩ F.coordinateBlock E n

theorem selectedBlock_mono : Monotone (F.selectedBlock E) :=
  fun _ _ hnm => Set.inter_subset_inter_right _ (F.coordinateBlock_mono E hnm)

theorem selectedBlock_finite (n : ℕ) : (F.selectedBlock E n).Finite :=
  (F.coordinateBlock_finite E n).subset Set.inter_subset_right

/-- The local stabilizer generators of stage `n` are supported inside the
stage-`n` region. -/
theorem span_selectedBlock_le_targetLabels (n : ℕ) :
    Submodule.span PauliBit (F.z '' F.selectedBlock E n) ≤ E.targetLabels n := by
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact hi.2.1

end LocalHyperbolicFamily

/-! ### Bridge to the checked adapted-coordinate infrastructure -/

/-- An adapted Hamel coordinate basis of the phase space
(`Formalization/SymplecticCoordinates.lean`) is in particular a locally
supported hyperbolic family, once a selected subset `P` is fixed. -/
noncomputable def LocalHyperbolicFamily.ofAdaptedBasis
    {L I : Type*} (data : AdaptedPauliCoordinateBasis (I := I) (V := PhaseSpace L))
    (P : Set I) : LocalHyperbolicFamily L I where
  z := data.z
  x := data.x
  indep := by
    have hfun : Sum.elim data.z data.x = ⇑data.basis := by
      funext p
      rcases p with i | i
      · exact (data.basis_z i).symm
      · exact (data.basis_x i).symm
    rw [hfun]
    exact data.basis.linearIndependent
  selected := P

/-- The coordinate map of the family induced by an adapted coordinate basis is
the coordinate-label equivalence of that basis. -/
theorem LocalHyperbolicFamily.coordinateMap_ofAdaptedBasis
    {L I : Type*} (data : AdaptedPauliCoordinateBasis (I := I) (V := PhaseSpace L))
    (P : Set I) (c : PauliCoordinateLabels I) :
    (LocalHyperbolicFamily.ofAdaptedBasis data P).coordinateMap c =
      data.coordinateLabelEquiv c := by
  have hfun : Sum.elim data.z data.x = ⇑data.basis := by
    funext p
    rcases p with i | i
    · exact (data.basis_z i).symm
    · exact (data.basis_x i).symm
  change Finsupp.linearCombination PauliBit (Sum.elim data.z data.x) c =
    data.basis.repr.symm c
  rw [hfun, data.basis.repr_symm_apply]

/-! ### The bundled coherent block system -/

/-- The coherent system of finite coordinate blocks extracted from
local-hyperbolic data.  It records finite blocks, their monotone exhaustion,
the finite source/target Pauli label blocks, and a single injective coordinate
map that is compatible with every block.  Compatibility of the block-restricted
maps with the inclusions is automatic because there is one global map, which
is exactly the coherence needed by later phase calibration. -/
structure CoordinateBlockSystem (L I : Type*) where
  /-- The finite coordinate block at stage `n`. -/
  block : ℕ → Set I
  /-- Local finiteness of the blocks. -/
  block_finite : ∀ n, (block n).Finite
  /-- The blocks increase. -/
  block_mono : Monotone block
  /-- The blocks exhaust the label set. -/
  block_exhausts : (⋃ n, block n) = Set.univ
  /-- Finite source Pauli labels at stage `n`. -/
  sourceLabels : ℕ → Submodule PauliBit (PauliCoordinateLabels I)
  /-- Finite target Pauli labels at stage `n`. -/
  targetLabels : ℕ → Submodule PauliBit (PhaseSpace L)
  /-- Source inclusion coherence. -/
  sourceLabels_mono : Monotone sourceLabels
  /-- Target inclusion coherence. -/
  targetLabels_mono : Monotone targetLabels
  /-- The source label blocks exhaust all finite coordinate words. -/
  iSup_sourceLabels : (⨆ n, sourceLabels n) = ⊤
  /-- The target label blocks exhaust the phase space. -/
  iSup_targetLabels : (⨆ n, targetLabels n) = ⊤
  /-- The coordinate map, defined once for all stages. -/
  coordinateMap : PauliCoordinateLabels I →ₗ[PauliBit] PhaseSpace L
  /-- Distinct coordinate words label distinct phase-space vectors. -/
  coordinateMap_injective : Function.Injective coordinateMap
  /-- The coordinate map is block-compatible. -/
  coordinateMap_block : ∀ n, (sourceLabels n).map coordinateMap ≤ targetLabels n
  /-- Each source label block is finite dimensional. -/
  sourceLabels_moduleFinite : ∀ n, Module.Finite PauliBit (sourceLabels n)
  /-- Each target label block is finite dimensional. -/
  targetLabels_moduleFinite : ∀ n, Module.Finite PauliBit (targetLabels n)

namespace LocalHyperbolicFamily

variable {L I : Type*} (F : LocalHyperbolicFamily L I) (E : LatticeExhaustion L)

/-- **The P52 construction.**  A locally supported, linearly independent
adapted hyperbolic family and a lattice exhaustion produce a coherent system
of finite coordinate blocks. -/
noncomputable def blockSystem : CoordinateBlockSystem L I where
  block := F.coordinateBlock E
  block_finite := F.coordinateBlock_finite E
  block_mono := F.coordinateBlock_mono E
  block_exhausts := F.iUnion_coordinateBlock E
  sourceLabels := F.sourceLabels E
  targetLabels := E.targetLabels
  sourceLabels_mono := F.sourceLabels_mono E
  targetLabels_mono := E.targetLabels_mono
  iSup_sourceLabels := F.iSup_sourceLabels E
  iSup_targetLabels := E.iSup_targetLabels
  coordinateMap := F.coordinateMap
  coordinateMap_injective := F.coordinateMap_injective
  coordinateMap_block := F.coordinateMap_sourceLabels_le E
  sourceLabels_moduleFinite := F.sourceLabels_moduleFinite E
  targetLabels_moduleFinite := E.targetLabels_moduleFinite

end LocalHyperbolicFamily

/-! ### Audit: finite support alone is not enough -/

/-- **Audit result.**  Local (finite) support of every hyperbolic pair does
*not* by itself make the coordinate blocks finite: here every label of the
family is supported on the empty region, yet every block is infinite.  Hence
the linear independence field of `LocalHyperbolicFamily` is genuinely needed
for `coordinateBlock_finite`. -/
theorem exists_infinite_coordinateBlock_of_no_independence :
    ∃ (E : LatticeExhaustion Unit) (z x : ℕ → PhaseSpace Unit),
      ∀ n : ℕ,
        ¬ {i : ℕ | z i ∈ supportedOn Unit (E.region n : Set Unit) ∧
              x i ∈ supportedOn Unit (E.region n : Set Unit)}.Finite := by
  classical
  refine ⟨⟨fun _ => Finset.univ, fun _ _ _ => le_rfl, fun a => ⟨0, Finset.mem_univ a⟩⟩,
    fun _ => 0, fun _ => 0, fun n hfin => ?_⟩
  have huniv : {i : ℕ | (0 : PhaseSpace Unit) ∈ supportedOn Unit
      ((Finset.univ : Finset Unit) : Set Unit) ∧
      (0 : PhaseSpace Unit) ∈ supportedOn Unit
      ((Finset.univ : Finset Unit) : Set Unit)} = Set.univ := by
    ext i
    simp
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

end CoherentLocalHyperbolic

end StabilizerHyperfinite
