import FiniteFiber.FiniteNestedPauli

/-!
# Support-defined local stabilizer groups

The manuscript defines a local stabilizer group by the intersection
`G_{S,F} = G_S ∩ A_F`.  This file records the group-theoretic part of that
definition through a finite-support predicate.  It proves that nested finite
regions give a canonical subgroup inclusion and, under a supplied detection
hypothesis, that all-identity discarded Pauli labels are equivalent to support
being contained in the smaller region and hence to membership in its local
group.

It deliberately does not construct a countable lattice Pauli group.  The
support map and its basic multiplication/inversion behavior are explicit
inputs, as are the finite Pauli coordinate facts needed to connect the support
predicate to a tensor-product representation.
-/

namespace FiniteFiber

/--
The finite-support facts needed to turn ``supported in a region'' into a
subgroup of an ambient stabilizer group.
-/
structure StabilizerSupportData (K Site : Type*) [Group K] [DecidableEq Site] where
  /-- The finite set of lattice sites on which an ambient group element acts nontrivially. -/
  support : K → Finset Site
  /-- The identity has empty support. -/
  support_one : support 1 = ∅
  /-- A product has no support outside the union of the two supports. -/
  support_mul : ∀ g h : K, support (g * h) ⊆ support g ∪ support h
  /-- Taking an inverse creates no new support. -/
  support_inv : ∀ g : K, support g⁻¹ ⊆ support g

namespace StabilizerSupportData

variable {K Site : Type*} [Group K] [DecidableEq Site]

/-- The subgroup of ambient stabilizers supported inside a finite region. -/
protected def localGroup (D : StabilizerSupportData K Site) (F : Finset Site) :
    Subgroup K where
  carrier := {g | D.support g ⊆ F}
  one_mem' := by simp [D.support_one]
  mul_mem' {g h} hg hh :=
    (D.support_mul g h).trans (Finset.union_subset hg hh)
  inv_mem' {g} hg := (D.support_inv g).trans hg

/-- Inclusion of support-defined local groups along an inclusion of finite regions. -/
protected def localGroupInclusion (D : StabilizerSupportData K Site)
    {F F' : Finset Site} (hFF' : F ⊆ F') :
    D.localGroup F →* D.localGroup F' where
  toFun g := ⟨g, g.property.trans hFF'⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The canonical inclusion of support-defined local groups is injective. -/
protected theorem localGroupInclusion_injective (D : StabilizerSupportData K Site)
    {F F' : Finset Site} (hFF' : F ⊆ F') :
    Function.Injective (D.localGroupInclusion hFF') := by
  intro g h hgh
  refine Subtype.ext ?_
  exact congrArg (fun x : D.localGroup F' => (x : K)) hgh

/--
If the discarded labels detect precisely whether an ambient stabilizer has
support outside the smaller region, their identity condition is exactly
membership in the included smaller local subgroup.
-/
protected theorem right_identity_iff_exists_local
    (D : StabilizerSupportData K Site) {F F' : Finset Site} (hFF' : F ⊆ F')
    {m : ℕ} (right : D.localGroup F' → Fin m → PauliLabel)
    (hright : ∀ g : D.localGroup F', IsIdentityPauliString (right g) ↔
      D.support (g : K) ⊆ F) (g : D.localGroup F') :
    IsIdentityPauliString (right g) ↔ ∃ h : D.localGroup F,
      D.localGroupInclusion hFF' h = g := by
  constructor
  · intro hg
    let h : D.localGroup F := ⟨g, (hright g).mp hg⟩
    refine ⟨h, ?_⟩
    rfl
  · rintro ⟨h, rfl⟩
    exact (hright _).mpr h.property

end StabilizerSupportData

/--
Pauli labels that detect the finite support of an ambient group element.  This
is a syntactic locality interface: it states exactly when a site belongs to
the supplied support and does not assert a matrix realization of the labels.
-/
structure StabilizerSupportLabelData
    (K Site : Type*) [Group K] [DecidableEq Site]
    (supportData : StabilizerSupportData K Site) where
  /-- The Pauli label assigned to an ambient group element at a site. -/
  labels : K → Site → PauliLabel
  /-- A site lies in the finite support exactly when its label is nonidentity. -/
  support_iff_label_ne_I : ∀ g : K, ∀ site : Site,
    site ∈ supportData.support g ↔ labels g site ≠ PauliLabel.I

namespace StabilizerSupportLabelData

variable {K Site : Type*} [Group K] [DecidableEq Site]
variable {D : StabilizerSupportData K Site}

/--
If the discarded sites enumerate the finite difference `F' \ F`, all their
labels are identity exactly when the support of an element already lies in
`F`.  This discharges the discarded-label detection hypothesis used by the
nested finite-density bridge.
-/
theorem right_identity_iff_support_of_enumerated_complement
    (L : StabilizerSupportLabelData K Site D)
    {F F' : Finset Site} {m : ℕ} (discarded : Fin m → Site)
    (hdiscarded : ∀ j, discarded j ∈ F' \ F)
    (hcover : ∀ site, site ∈ F' \ F → ∃ j, discarded j = site)
    (g : D.localGroup F') :
    IsIdentityPauliString (fun j => L.labels (g : K) (discarded j)) ↔
      D.support (g : K) ⊆ F := by
  constructor
  · intro hidentity site hsite
    by_contra hnotF
    have hsite_large : site ∈ F' := g.property hsite
    obtain ⟨j, hj⟩ := hcover site (Finset.mem_sdiff.mpr ⟨hsite_large, hnotF⟩)
    have hlabel_I : L.labels (g : K) site = PauliLabel.I := by
      rw [← hj]
      exact hidentity j
    exact (L.support_iff_label_ne_I (g : K) site).mp hsite hlabel_I
  · intro hsupport j
    by_contra hne
    have hsite : discarded j ∈ D.support (g : K) :=
      (L.support_iff_label_ne_I (g : K) (discarded j)).mpr hne
    have hsmall : discarded j ∈ F := hsupport hsite
    exact (Finset.mem_sdiff.mp (hdiscarded j)).2 hsmall

/--
Combining support detection with the canonical local-group inclusion identifies
the right-identity survivors with the smaller local group itself.
-/
theorem right_identity_iff_exists_local_of_enumerated_complement
    (L : StabilizerSupportLabelData K Site D)
    {F F' : Finset Site} (hFF' : F ⊆ F') {m : ℕ} (discarded : Fin m → Site)
    (hdiscarded : ∀ j, discarded j ∈ F' \ F)
    (hcover : ∀ site, site ∈ F' \ F → ∃ j, discarded j = site)
    (g : D.localGroup F') :
    IsIdentityPauliString (fun j => L.labels (g : K) (discarded j)) ↔
      ∃ h : D.localGroup F, D.localGroupInclusion hFF' h = g := by
  exact D.right_identity_iff_exists_local hFF'
    (fun g j => L.labels (g : K) (discarded j))
    (fun g => L.right_identity_iff_support_of_enumerated_complement
      discarded hdiscarded hcover g) g

end StabilizerSupportLabelData

/--
Finite Pauli data for two support-defined local groups.  The first three
support-derived clauses of `NestedFinitePauliStabilizerData` are constructed,
not assumed: the local inclusion is canonical and the survivor iff follows
from `right_identity_iff_support`.  The remaining fields are the exact
coordinate/Pauli facts still needed from a concrete lattice realization.
-/
structure SupportDefinedNestedFinitePauliData
    (K Site : Type*) [Group K] [DecidableEq Site] (n m : ℕ) where
  /-- Ambient support data for the global stabilizer group. -/
  supportData : StabilizerSupportData K Site
  /-- The retained finite lattice region. -/
  smallRegion : Finset Site
  /-- The larger finite lattice region. -/
  largeRegion : Finset Site
  /-- The retained region is contained in the larger region. -/
  region_subset : smallRegion ⊆ largeRegion
  /-- Actual finite Pauli stabilizer data for the larger support-defined local group. -/
  large : FinitePauliStabilizerData (supportData.localGroup largeRegion) (n + m)
  /-- Actual finite Pauli stabilizer data for the smaller support-defined local group. -/
  small : FinitePauliStabilizerData (supportData.localGroup smallRegion) n
  /-- Chosen tensor-product coordinates for the larger finite block. -/
  coordinateEquiv : QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m
  /-- Signed Pauli phase in the chosen larger-region coordinates. -/
  negative : supportData.localGroup largeRegion → Bool
  /-- Retained labels in the chosen coordinates. -/
  left : supportData.localGroup largeRegion → Fin n → PauliLabel
  /-- Discarded labels in the chosen coordinates. -/
  right : supportData.localGroup largeRegion → Fin m → PauliLabel
  /-- Tensor decomposition of every larger local stabilizer. -/
  large_decomposes : ∀ g : supportData.localGroup largeRegion,
    Matrix.reindex coordinateEquiv coordinateEquiv (large.representation g) =
      signedBipartitePauliTerm (negative g) (left g) (right g)
  /-- Right labels are all identity exactly for stabilizers supported in the smaller region. -/
  right_identity_iff_support : ∀ g : supportData.localGroup largeRegion,
    IsIdentityPauliString (right g) ↔ supportData.support (g : K) ⊆ smallRegion
  /-- The canonical local inclusion preserves phase. -/
  negative_compat : ∀ h : supportData.localGroup smallRegion,
    negative (supportData.localGroupInclusion region_subset h) = small.negative h
  /-- The canonical local inclusion preserves retained labels. -/
  left_compat : ∀ h : supportData.localGroup smallRegion,
    left (supportData.localGroupInclusion region_subset h) = small.labels h

namespace SupportDefinedNestedFinitePauliData

variable {K Site : Type*} [Group K] [DecidableEq Site] {n m : ℕ}

/--
The support-defined local groups canonically instantiate the actual nested
finite-stabilizer contract used by the density compatibility theorem.
-/
noncomputable def toNestedFinitePauliStabilizerData
    (D : SupportDefinedNestedFinitePauliData K Site n m) :
    NestedFinitePauliStabilizerData
      (D.supportData.localGroup D.largeRegion)
      (D.supportData.localGroup D.smallRegion) n m where
  large := D.large
  small := D.small
  coordinateEquiv := D.coordinateEquiv
  negative := D.negative
  left := D.left
  right := D.right
  large_decomposes := D.large_decomposes
  inclusion := D.supportData.localGroupInclusion D.region_subset
  inclusion_injective :=
    D.supportData.localGroupInclusion_injective D.region_subset
  survivor_iff := fun g =>
    D.supportData.right_identity_iff_exists_local D.region_subset D.right
      D.right_identity_iff_support g
  negative_compat := D.negative_compat
  left_compat := D.left_compat

/--
The manuscript's finite-region density compatibility follows directly for
support-defined local groups once the remaining concrete Pauli-coordinate
facts in `SupportDefinedNestedFinitePauliData` are supplied.
-/
theorem partialTrace_reindexedLargeDensity_eq_smallDensity
    (D : SupportDefinedNestedFinitePauliData K Site n m)
    [Fintype (D.supportData.localGroup D.largeRegion)]
    [Fintype (D.supportData.localGroup D.smallRegion)]
    [DecidableEq (D.supportData.localGroup D.largeRegion)] :
    partialTraceRight D.toNestedFinitePauliStabilizerData.reindexedLargeDensity =
      D.small.stabilizerDensity := by
  exact D.toNestedFinitePauliStabilizerData.partialTrace_reindexedLargeDensity_eq_smallDensity

end SupportDefinedNestedFinitePauliData

end FiniteFiber
