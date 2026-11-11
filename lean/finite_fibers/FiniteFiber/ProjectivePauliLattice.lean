import FiniteFiber.FiniteLocalGroupSupport
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Basic

/-!
# Finite-support projective Pauli words on a lattice

This file supplies the literal finite-support object behind the support
predicate used in `FiniteLocalGroupSupport`.  A projective Pauli label is the
binary pair recording the `X` and `Z` exponents; a projective Pauli word is a
finitely supported function from lattice sites to such labels.  Addition is
the phase-free Pauli multiplication law.  We use `Multiplicative` only to
present that additive group through the multiplicative `Group` interface of
the earlier local-stabilizer development.

The central `ZMod 4` phase extension of the full Pauli group, the Hermitian
signed lift appropriate to a consistent stabilizer group, and the finite
matrix realization are deliberately not claimed here.  This layer proves the
support, finite-local-group, and countable-exhaustion facts which do not
depend on those phase choices.
-/

namespace FiniteFiber

/-- The two binary projective coordinates of a one-qubit Pauli label. -/
abbrev ProjectivePauliLabel := ZMod 2 × ZMod 2

/-- A finite-support projective Pauli word on a lattice. -/
abbrev ProjectivePauliWord (Site : Type*) := Site →₀ ProjectivePauliLabel

namespace PauliLabel

/-- The usual phase-free binary coordinates of the four Hermitian Pauli labels. -/
def projectiveCoordinates : PauliLabel → ProjectivePauliLabel
  | I => (0, 0)
  | X => (1, 0)
  | Y => (1, 1)
  | Z => (0, 1)

/-- A one-site Pauli label has zero projective coordinates exactly when it is identity. -/
theorem projectiveCoordinates_eq_zero_iff (a : PauliLabel) :
    projectiveCoordinates a = 0 ↔ a = I := by
  cases a <;> simp [projectiveCoordinates]

/--
The canonical Hermitian representative of a phase-free binary Pauli label.
This only chooses among `I`, `X`, `Y`, and `Z`; it does not choose a phase for
the full Pauli group.
-/
def ofProjectiveCoordinates (p : ProjectivePauliLabel) : PauliLabel :=
  if p.1 = 0 then
    if p.2 = 0 then I else Z
  else
    if p.2 = 0 then X else Y

/-- The canonical representative is identity exactly at the zero projective label. -/
theorem ofProjectiveCoordinates_eq_I_iff (p : ProjectivePauliLabel) :
    ofProjectiveCoordinates p = I ↔ p = 0 := by
  rcases p with ⟨x, z⟩
  fin_cases x <;> fin_cases z <;> simp [ofProjectiveCoordinates]

end PauliLabel

namespace ProjectivePauliWord

variable {Site : Type*} [DecidableEq Site]

/--
The support of a finite-support projective Pauli word obeys the abstract
support contract used for local stabilizer groups.
-/
def supportData :
    StabilizerSupportData (Multiplicative (ProjectivePauliWord Site)) Site where
  support g := (Multiplicative.toAdd g).support
  support_one := by
    change (0 : ProjectivePauliWord Site).support = ∅
    exact Finsupp.support_zero
  support_mul := by
    intro g h
    change (Multiplicative.toAdd g + Multiplicative.toAdd h).support ⊆
      (Multiplicative.toAdd g).support ∪ (Multiplicative.toAdd h).support
    exact Finsupp.support_add
  support_inv := by
    intro g
    change (-Multiplicative.toAdd g).support ⊆ (Multiplicative.toAdd g).support
    rw [Finsupp.support_neg]

/-- The projective Pauli words supported in a finite lattice region. -/
abbrev localGroup (F : Finset Site) := (supportData (Site := Site)).localGroup F

/--
Restricting a finite-support word to a finite region identifies the local
projective Pauli group with finitely supported functions on that region.
-/
noncomputable def localGroupEquiv (F : Finset Site) :
    localGroup F ≃ (F →₀ ProjectivePauliLabel) where
  toFun g := Finsupp.subtypeDomain (fun x => x ∈ F) (Multiplicative.toAdd g.1)
  invFun f := ⟨Multiplicative.ofAdd f.extendDomain, by
    intro a ha
    exact Finsupp.support_extendDomain_subset f ha⟩
  left_inv g := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Finsupp.extendDomain_subtypeDomain _ g.property
  right_inv f := by
    exact Finsupp.subtypeDomain_extendDomain f

/-- A local projective Pauli group on a finite region is finite. -/
noncomputable def localGroupFintype (F : Finset Site) : Fintype (localGroup F) := by
  classical
  exact Fintype.ofEquiv (F →₀ ProjectivePauliLabel) (localGroupEquiv F).symm

/-- Support data restricted to a projective stabilizer subgroup. -/
def stabilizerSupportData (S : Subgroup (Multiplicative (ProjectivePauliWord Site))) :
    StabilizerSupportData S Site where
  support s :=
    (Multiplicative.toAdd (s : Multiplicative (ProjectivePauliWord Site))).support
  support_one := by
    change (0 : ProjectivePauliWord Site).support = ∅
    exact Finsupp.support_zero
  support_mul := by
    intro s t
    change (Multiplicative.toAdd (s : Multiplicative (ProjectivePauliWord Site)) +
      Multiplicative.toAdd (t : Multiplicative (ProjectivePauliWord Site))).support ⊆
      (Multiplicative.toAdd (s : Multiplicative (ProjectivePauliWord Site))).support ∪
      (Multiplicative.toAdd (t : Multiplicative (ProjectivePauliWord Site))).support
    exact Finsupp.support_add
  support_inv := by
    intro s
    change (-Multiplicative.toAdd (s : Multiplicative (ProjectivePauliWord Site))).support ⊆
      (Multiplicative.toAdd (s : Multiplicative (ProjectivePauliWord Site))).support
    rw [Finsupp.support_neg]

/-- The finite-region part of a projective stabilizer subgroup. -/
abbrev stabilizerLocalGroup (S : Subgroup (Multiplicative (ProjectivePauliWord Site)))
    (F : Finset Site) := (stabilizerSupportData S).localGroup F

/-- Forgetting stabilizer membership embeds a local stabilizer group into all local words. -/
def stabilizerLocalGroupToLocalGroup
    (S : Subgroup (Multiplicative (ProjectivePauliWord Site))) (F : Finset Site) :
    stabilizerLocalGroup S F → localGroup F := fun s =>
  ⟨s.1.1, s.2⟩

/-- The forgetful map from a local stabilizer group is injective. -/
theorem stabilizerLocalGroupToLocalGroup_injective
    (S : Subgroup (Multiplicative (ProjectivePauliWord Site))) (F : Finset Site) :
    Function.Injective (stabilizerLocalGroupToLocalGroup S F) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : localGroup F => (u : Multiplicative (ProjectivePauliWord Site))) hst

/-- Every projective local stabilizer group is finite. -/
noncomputable def stabilizerLocalGroupFintype
    (S : Subgroup (Multiplicative (ProjectivePauliWord Site))) (F : Finset Site) :
    Fintype (stabilizerLocalGroup S F) := by
  classical
  letI : Fintype (localGroup F) := localGroupFintype F
  letI : Finite (stabilizerLocalGroup S F) :=
    Finite.of_injective (stabilizerLocalGroupToLocalGroup S F)
      (stabilizerLocalGroupToLocalGroup_injective S F)
  exact Fintype.ofFinite (stabilizerLocalGroup S F)

/-- An increasing finite-region exhaustion of a lattice. -/
structure FiniteExhaustion (Site : Type*) [DecidableEq Site] where
  /-- The finite region at each stage. -/
  region : ℕ → Finset Site
  /-- The regions are nested. -/
  mono : Monotone region
  /-- Every lattice site occurs at a finite stage. -/
  cover : ∀ site, ∃ n, site ∈ region n

namespace FiniteExhaustion

/-- Every finite set of sites is contained in one stage of an exhaustion. -/
theorem covers_finset (E : FiniteExhaustion Site) (F : Finset Site) :
    ∃ n, F ⊆ E.region n := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | insert a F ha ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm⟩ := E.cover a
      refine ⟨max n m, ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact E.mono (Nat.le_max_right _ _) hm
      · exact E.mono (Nat.le_max_left _ _) (hn hx)

/-- Every finite-support projective Pauli word belongs to one local group. -/
theorem word_mem_localGroup (E : FiniteExhaustion Site)
    (g : Multiplicative (ProjectivePauliWord Site)) :
    ∃ n, g ∈ localGroup (E.region n) := by
  obtain ⟨n, hn⟩ := E.covers_finset (Multiplicative.toAdd g).support
  exact ⟨n, hn⟩

/-- Every element of a projective stabilizer subgroup belongs to one local stabilizer group. -/
theorem stabilizer_mem_localGroup (E : FiniteExhaustion Site)
    (S : Subgroup (Multiplicative (ProjectivePauliWord Site))) (g : S) :
    ∃ n, g ∈ stabilizerLocalGroup S (E.region n) := by
  obtain ⟨n, hn⟩ := E.covers_finset
    (Multiplicative.toAdd (g : Multiplicative (ProjectivePauliWord Site))).support
  exact ⟨n, hn⟩

end FiniteExhaustion

/-- The finite regions induced by the initial segments of an enumeration. -/
def regionsOfEnumeration (enumerate : ℕ → Site) (n : ℕ) : Finset Site :=
  (Finset.range n).image enumerate

/-- Initial segments of an enumeration form nested finite regions. -/
theorem regionsOfEnumeration_mono (enumerate : ℕ → Site) :
    Monotone (regionsOfEnumeration enumerate) := by
  intro n m hnm
  exact Finset.image_subset_image (Finset.range_mono hnm)

/-- A surjective enumeration covers every site at a finite stage. -/
theorem regionsOfEnumeration_cover (enumerate : ℕ → Site)
    (henumerate : Function.Surjective enumerate) :
    ∀ site, ∃ n, site ∈ regionsOfEnumeration enumerate n := by
  intro site
  obtain ⟨k, hk⟩ := henumerate site
  refine ⟨k + 1, ?_⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hk⟩

/-- A surjective enumeration supplies the manuscript's finite-region exhaustion. -/
def exhaustionOfSurjectiveEnumeration (enumerate : ℕ → Site)
    (henumerate : Function.Surjective enumerate) : FiniteExhaustion Site where
  region := regionsOfEnumeration enumerate
  mono := regionsOfEnumeration_mono enumerate
  cover := regionsOfEnumeration_cover enumerate henumerate

end ProjectivePauliWord

end FiniteFiber
