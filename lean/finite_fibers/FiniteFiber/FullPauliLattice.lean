import FiniteFiber.ProjectivePauliLattice

/-!
# An algebraic finite-support Pauli normal form with phases

This file constructs an algebraic normal-form model of the finite-support
Pauli group on an arbitrary lattice.  Its elements are written in the form
`i^phase X^x Z^z`, where `phase : ZMod 4` and the binary exponents are a
finitely supported projective Pauli word.  The multiplication cocycle records
the sign obtained when a `Z` exponent crosses an `X` exponent.

This is deliberately separate from the finite matrix realization.  The latter
must still prove that this presentation is faithfully represented by the
manuscript's tensor-product Pauli operators, transport a finite region to
`Fin n`, and identify syntactic support with matrix-algebra locality.  Until
then this file does not claim an operator-level realization.
-/

namespace FiniteFiber

/-- An algebraic full-Pauli word in the normal form `i^phase X^x Z^z`. -/
structure FullPauliWord (Site : Type*) where
  /-- The central phase exponent modulo four. -/
  phase : ZMod 4
  /-- The finite-support phase-free Pauli coordinates. -/
  label : ProjectivePauliWord Site

namespace FullPauliWord

variable {Site : Type*}

/-- The additive embedding `Z/2Z → Z/4Z` sending `1` to the Pauli sign `-1=i^2`. -/
def phaseEmbed : ZMod 2 →+ ZMod 4 where
  toFun x := if x = 0 then 0 else 2
  map_zero' := by simp
  map_add' x y := by
    fin_cases x <;> fin_cases y <;> decide

/-- The `X` coordinate of a projective Pauli word. -/
noncomputable def xCoordinate :
    ProjectivePauliWord Site →+ (Site →₀ ZMod 2) :=
  Finsupp.mapRange.addMonoidHom
    { toFun := Prod.fst
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The `Z` coordinate of a projective Pauli word. -/
noncomputable def zCoordinate :
    ProjectivePauliWord Site →+ (Site →₀ ZMod 2) :=
  Finsupp.mapRange.addMonoidHom
    { toFun := Prod.snd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Multiplication by a fixed binary exponent as an additive homomorphism. -/
def multiplyBy (c : ZMod 2) : ZMod 2 →+ ZMod 2 where
  toFun x := x * c
  map_zero' := by simp
  map_add' x y := by rw [add_mul]

/-- The finite dot product of binary finitely supported functions. -/
noncomputable def binaryDot (u v : Site →₀ ZMod 2) : ZMod 2 :=
  Finsupp.liftAddHom (fun i => multiplyBy (v i)) u

/-- The binary dot product is additive in its left input. -/
theorem binaryDot_add_left (u v w : Site →₀ ZMod 2) :
    binaryDot (u + v) w = binaryDot u w + binaryDot v w :=
  (Finsupp.liftAddHom (fun i => multiplyBy (w i))).map_add u v

/-- The binary dot product is additive in its right input. -/
theorem binaryDot_add_right (u v w : Site →₀ ZMod 2) :
    binaryDot u (v + w) = binaryDot u v + binaryDot u w := by
  change u.sum (fun i x => x * (v + w) i) =
    u.sum (fun i x => x * v i) + u.sum (fun i x => x * w i)
  rw [show (fun i x => x * (v + w) i) =
    fun i x => x * v i + x * w i by
      funext i x
      rw [Finsupp.add_apply, mul_add]]
  exact Finsupp.sum_add

/-- The binary dot product vanishes against the zero right input. -/
theorem binaryDot_zero_right (u : Site →₀ ZMod 2) : binaryDot u 0 = 0 := by
  change u.sum (fun i x => x * 0) = 0
  simp

/--
The Pauli multiplication cocycle.  It records the sign
`(-1)^(z(u) dot x(v))` incurred in the normal-form product.
-/
noncomputable def cocycle (u v : ProjectivePauliWord Site) : ZMod 4 :=
  phaseEmbed (binaryDot (zCoordinate u) (xCoordinate v))

/-- The cocycle vanishes with a zero left argument. -/
theorem cocycle_zero_left (u : ProjectivePauliWord Site) : cocycle 0 u = 0 := by
  simp [cocycle, binaryDot, zCoordinate]

/-- The cocycle vanishes with a zero right argument. -/
theorem cocycle_zero_right (u : ProjectivePauliWord Site) : cocycle u 0 = 0 := by
  rw [cocycle, xCoordinate.map_zero, binaryDot_zero_right, phaseEmbed.map_zero]

/-- The Pauli multiplication cocycle satisfies the associative two-cocycle identity. -/
theorem cocycle_assoc (u v w : ProjectivePauliWord Site) :
    cocycle u v + cocycle (u + v) w =
      cocycle v w + cocycle u (v + w) := by
  rw [cocycle, cocycle, cocycle, cocycle]
  rw [zCoordinate.map_add, xCoordinate.map_add]
  rw [binaryDot_add_left, binaryDot_add_right]
  repeat rw [← phaseEmbed.map_add]
  abel_nf

/-- Equality of full Pauli words is equality of their phase and projective coordinates. -/
@[ext]
theorem ext {a b : FullPauliWord Site} (hphase : a.phase = b.phase)
    (hlabel : a.label = b.label) : a = b := by
  cases a
  cases b
  cases hphase
  cases hlabel
  rfl

/-- Normal-form multiplication of full Pauli words. -/
noncomputable def mul (a b : FullPauliWord Site) : FullPauliWord Site :=
  ⟨a.phase + b.phase + cocycle a.label b.label, a.label + b.label⟩

noncomputable instance : Mul (FullPauliWord Site) := ⟨mul⟩

/-- The phase-zero, all-identity Pauli word. -/
def one : FullPauliWord Site := ⟨0, 0⟩

instance : One (FullPauliWord Site) := ⟨one⟩

/-- The inverse in normal form, obtained by cancelling the cocycle in `a⁻¹ a`. -/
noncomputable def inv (a : FullPauliWord Site) : FullPauliWord Site :=
  ⟨-a.phase - cocycle (-a.label) a.label, -a.label⟩

noncomputable instance : Inv (FullPauliWord Site) := ⟨inv⟩

/-- The finite-support normal-form Pauli words form a group. -/
noncomputable instance : Group (FullPauliWord Site) where
  mul_assoc a b c := by
    apply ext
    · change (a.phase + b.phase + cocycle a.label b.label) + c.phase +
        cocycle (a.label + b.label) c.label =
        a.phase + (b.phase + c.phase + cocycle b.label c.label) +
          cocycle a.label (b.label + c.label)
      calc
        (a.phase + b.phase + cocycle a.label b.label) + c.phase +
            cocycle (a.label + b.label) c.label =
            a.phase + b.phase + c.phase +
              (cocycle a.label b.label + cocycle (a.label + b.label) c.label) := by
                abel
        _ = a.phase + b.phase + c.phase +
              (cocycle b.label c.label + cocycle a.label (b.label + c.label)) := by
                rw [cocycle_assoc]
        _ = a.phase + (b.phase + c.phase + cocycle b.label c.label) +
              cocycle a.label (b.label + c.label) := by
                abel
    · change (a.label + b.label) + c.label = a.label + (b.label + c.label)
      abel
  one_mul a := by
    apply ext
    · change 0 + a.phase + cocycle 0 a.label = a.phase
      rw [cocycle_zero_left]
      abel
    · change 0 + a.label = a.label
      abel
  mul_one a := by
    apply ext
    · change a.phase + 0 + cocycle a.label 0 = a.phase
      rw [cocycle_zero_right]
      abel
    · change a.label + 0 = a.label
      abel
  inv_mul_cancel a := by
    apply ext
    · change (-a.phase - cocycle (-a.label) a.label) + a.phase +
        cocycle (-a.label) a.label = 0
      abel
    · change -a.label + a.label = 0
      abel

/-- The central full-Pauli word representing `-1`. -/
noncomputable def negativeIdentity : FullPauliWord Site := ⟨2, 0⟩

/-- The formal Pauli `-1` is not the group identity. -/
theorem negativeIdentity_ne_one : negativeIdentity (Site := Site) ≠ 1 := by
  intro h
  have hphase := congrArg FullPauliWord.phase h
  change (2 : ZMod 4) = 0 at hphase
  exact (by decide : (2 : ZMod 4) ≠ 0) hphase

/--
Algebraic input for a stabilizer system presented by generators.  These
conditions are deliberately about the full-Pauli normal-form group: their
operator-Hermitian interpretation still requires the separate matrix
realization.
-/
structure StabilizerGeneratorData (Site : Type*) where
  /-- The finite-support full-Pauli generators. -/
  generators : Set (FullPauliWord Site)
  /-- Distinct generators commute; equality cases commute automatically. -/
  pairwise_commute : generators.Pairwise Commute
  /-- Each generator has order dividing two. -/
  generator_involutive : ∀ g, g ∈ generators → g * g = 1
  /-- Consistency: the group generated by the generators excludes `-1`. -/
  no_negative_identity : negativeIdentity (Site := Site) ∉ Subgroup.closure generators

namespace StabilizerGeneratorData

variable {Site : Type*} (D : StabilizerGeneratorData Site)

/-- A generator commutes with every element of the subgroup it generates. -/
theorem generator_commutes_closure (g : FullPauliWord Site) (hg : g ∈ D.generators)
    (h : FullPauliWord Site) (hh : h ∈ Subgroup.closure D.generators) : Commute g h := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hh
  · intro x hx
    rcases eq_or_ne g x with rfl | hne
    · exact Commute.refl g
    · exact D.pairwise_commute hg hx hne
  · exact Commute.one_right g
  · intro x y hx hy hgx hgy
    exact hgx.mul_right hgy
  · intro x hx hcomm
    exact hcomm.inv_right

/-- Pairwise commutation extends from generators to the generated subgroup. -/
theorem closure_commute (x y : FullPauliWord Site)
    (hx : x ∈ Subgroup.closure D.generators)
    (hy : y ∈ Subgroup.closure D.generators) : Commute x y := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · intro g hg
    exact D.generator_commutes_closure g hg y hy
  · exact Commute.one_left y
  · intro a b ha hb hac hbc
    exact hac.mul_left hbc
  · intro a ha hcomm
    exact hcomm.inv_left

/-- The generated subgroup remains of exponent two. -/
theorem closure_involutive (x : FullPauliWord Site)
    (hx : x ∈ Subgroup.closure D.generators) : x * x = 1 := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · intro g hg
    exact D.generator_involutive g hg
  · simp
  · intro a b ha hb haa hbb
    have hcomm : Commute a b := D.closure_commute a b ha hb
    calc
      (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
      _ = a * (a * b) * b := by rw [hcomm.eq]
      _ = (a * a) * (b * b) := by noncomm_ring
      _ = 1 := by rw [haa, hbb, one_mul]
  · intro a ha haa
    have hinv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left haa).symm
    rw [hinv, haa]

end StabilizerGeneratorData

variable [DecidableEq Site]

/--
An algebraic record for the global group generated by a consistent commuting
stabilizer system.  The subgroup form represents the generated group, not yet
a construction from a manuscript generator set.  `involutive` records the
order-two condition which will correspond to Hermiticity after the finite
matrix realization is proved; `no_negative_identity` is the consistency
condition.
-/
structure ConsistentStabilizerGroup (Site : Type*) [DecidableEq Site] where
  /-- The global group of finite stabilizer products. -/
  group : Subgroup (FullPauliWord Site)
  /-- The group is abelian, as follows from mutually commuting generators. -/
  commute : ∀ g h : group,
    Commute (g : FullPauliWord Site) (h : FullPauliWord Site)
  /-- Every group element has order dividing two in the algebraic normal form. -/
  involutive : ∀ g : group, (g : FullPauliWord Site) * g = 1
  /-- The group does not contain the inconsistent central element `-1`. -/
  no_negative_identity : negativeIdentity (Site := Site) ∉ group

/--
Pairwise-commuting order-two generators construct the algebraic consistent
stabilizer subgroup used by the local-support development.
-/
noncomputable def StabilizerGeneratorData.toConsistentStabilizerGroup
    (D : StabilizerGeneratorData Site) : ConsistentStabilizerGroup Site where
  group := Subgroup.closure D.generators
  commute := by
    intro x y
    exact D.closure_commute x y x.2 y.2
  involutive := by
    intro x
    exact D.closure_involutive x x.2
  no_negative_identity := D.no_negative_identity

/-- An order-two phase in `Z/4Z` is zero or the sign phase two. -/
theorem phase_eq_zero_or_two_of_double_eq_zero (x : ZMod 4) (h : x + x = 0) :
    x = 0 ∨ x = 2 := by
  have hv : (x.val + x.val) % 4 = 0 := by
    simpa [ZMod.val_add] using congrArg ZMod.val h
  have hlt : x.val < 4 := ZMod.val_lt x
  have hcase : x.val = 0 ∨ x.val = 2 := by omega
  rcases hcase with hzero | htwo
  · left
    rw [← ZMod.natCast_zmod_val x, hzero]
    rfl
  · right
    rw [← ZMod.natCast_zmod_val x, htwo]
    norm_num

/--
An involutive full-Pauli stabilizer with trivial projective label is either
the identity or the forbidden central `-1`.
-/
theorem element_eq_one_or_negativeIdentity_of_label_eq_zero
    (D : ConsistentStabilizerGroup Site) (g : D.group)
    (hlabel : (g : FullPauliWord Site).label = 0) :
    (g : FullPauliWord Site) = 1 ∨
      (g : FullPauliWord Site) = negativeIdentity (Site := Site) := by
  have hphase : (g : FullPauliWord Site).phase + (g : FullPauliWord Site).phase = 0 := by
    have hmul := congrArg FullPauliWord.phase (D.involutive g)
    change (g.1.phase + g.1.phase + cocycle g.1.label g.1.label) = 0 at hmul
    rw [hlabel, cocycle_zero_left] at hmul
    simpa using hmul
  rcases phase_eq_zero_or_two_of_double_eq_zero _ hphase with hzero | htwo
  · left
    apply FullPauliWord.ext
    · exact hzero
    · exact hlabel
  · right
    apply FullPauliWord.ext
    · exact htwo
    · exact hlabel

/-- Consistency eliminates the `-1` alternative for a trivial projective label. -/
theorem element_eq_one_of_label_eq_zero
    (D : ConsistentStabilizerGroup Site) (g : D.group)
    (hlabel : (g : FullPauliWord Site).label = 0) :
    (g : FullPauliWord Site) = 1 := by
  rcases element_eq_one_or_negativeIdentity_of_label_eq_zero D g hlabel with h | h
  · exact h
  · exact False.elim (D.no_negative_identity (by rw [← h]; exact g.2))

/-- The projective-label map is injective on a consistent stabilizer group. -/
theorem label_injective (D : ConsistentStabilizerGroup Site) :
    Function.Injective (fun g : D.group => (g : FullPauliWord Site).label) := by
  intro g h hlabel
  change g.1.label = h.1.label at hlabel
  apply eq_of_mul_inv_eq_one
  apply Subtype.ext
  apply element_eq_one_of_label_eq_zero D (g * h⁻¹)
  change g.1.label + -h.1.label = 0
  rw [hlabel]
  abel

/--
The literal finite support of a full Pauli word: the central phase never adds
sites to the support.
-/
noncomputable def supportData : StabilizerSupportData (FullPauliWord Site) Site where
  support g := g.label.support
  support_one := by
    change (0 : ProjectivePauliWord Site).support = ∅
    exact Finsupp.support_zero
  support_mul := by
    intro g h
    change (g.label + h.label).support ⊆ g.label.support ∪ h.label.support
    exact Finsupp.support_add
  support_inv := by
    intro g
    change (-g.label).support ⊆ g.label.support
    rw [Finsupp.support_neg]

/--
The canonical Hermitian projective Pauli label at a lattice site.  It records
only whether and how the normal-form word is nontrivial at that site; the
central `ZMod 4` phase is intentionally not represented here.
-/
def localPauliLabel (g : FullPauliWord Site) (site : Site) : PauliLabel :=
  PauliLabel.ofProjectiveCoordinates (g.label site)

omit [DecidableEq Site] in
/-- A site lies in the syntactic support exactly when its local label is not identity. -/
theorem mem_support_iff_localPauliLabel_ne_I
    (g : FullPauliWord Site) (site : Site) :
    site ∈ g.label.support ↔ localPauliLabel g site ≠ PauliLabel.I := by
  rw [Finsupp.mem_support_iff]
  constructor
  · intro h hI
    apply h
    exact (PauliLabel.ofProjectiveCoordinates_eq_I_iff _).mp hI
  · intro h hzero
    apply h
    exact (PauliLabel.ofProjectiveCoordinates_eq_I_iff _).mpr hzero

/--
The full-Pauli normal form supplies the syntactic support-label interface.
This remains a support statement, not a matrix Pauli representation.
-/
noncomputable def supportLabelData :
    StabilizerSupportLabelData (FullPauliWord Site) Site supportData where
  labels := localPauliLabel
  support_iff_label_ne_I := mem_support_iff_localPauliLabel_ne_I

/--
For an enumerated finite complement, trivial canonical projective labels on
the discarded sites detect exactly that a local full-Pauli word was already
supported in the retained region.
-/
theorem right_identity_iff_support_of_enumerated_complement
    {F F' : Finset Site} {m : ℕ} (discarded : Fin m → Site)
    (hdiscarded : ∀ j, discarded j ∈ F' \ F)
    (hcover : ∀ site, site ∈ F' \ F → ∃ j, discarded j = site)
    (g : supportData.localGroup F') :
    IsIdentityPauliString (fun j => localPauliLabel (g : FullPauliWord Site)
      (discarded j)) ↔ supportData.support (g : FullPauliWord Site) ⊆ F := by
  exact supportLabelData.right_identity_iff_support_of_enumerated_complement
    discarded hdiscarded hcover g

/--
Equivalently, the normal-form words trivial on an enumerated discarded
complement are exactly the images of the smaller syntactic local group under
its canonical inclusion.
-/
theorem right_identity_iff_exists_local_of_enumerated_complement
    {F F' : Finset Site} (hFF' : F ⊆ F') {m : ℕ} (discarded : Fin m → Site)
    (hdiscarded : ∀ j, discarded j ∈ F' \ F)
    (hcover : ∀ site, site ∈ F' \ F → ∃ j, discarded j = site)
    (g : supportData.localGroup F') :
    IsIdentityPauliString (fun j => localPauliLabel (g : FullPauliWord Site)
      (discarded j)) ↔
      ∃ h : supportData.localGroup F, supportData.localGroupInclusion hFF' h = g := by
  exact supportLabelData.right_identity_iff_exists_local_of_enumerated_complement
    hFF' discarded hdiscarded hcover g

/-- The algebraic full-Pauli words syntactically supported in a finite region. -/
noncomputable def localGroup (F : Finset Site) :=
  (supportData (Site := Site)).localGroup F

/--
Forgetting only the finite-support restriction embeds a local full Pauli group
into its four phase choices times the finite local projective Pauli group.
-/
noncomputable def localGroupToFinite (F : Finset Site) :
    localGroup F → ZMod 4 × ProjectivePauliWord.localGroup F := fun g =>
  ⟨g.1.phase, ⟨Multiplicative.ofAdd g.1.label, g.2⟩⟩

/-- The finite-coordinate encoding of a local full Pauli word is injective. -/
theorem localGroupToFinite_injective (F : Finset Site) :
    Function.Injective (localGroupToFinite (Site := Site) F) := by
  intro g h hgh
  apply Subtype.ext
  apply FullPauliWord.ext
  · exact congrArg Prod.fst hgh
  · apply Multiplicative.toAdd.injective
    exact congrArg (fun u : ZMod 4 × ProjectivePauliWord.localGroup F =>
      (u.2 : Multiplicative (ProjectivePauliWord Site))) hgh

/-- Every full Pauli local group on a finite lattice region is finite. -/
noncomputable def localGroupFintype (F : Finset Site) : Fintype (localGroup F) := by
  classical
  letI : Fintype (ProjectivePauliWord.localGroup F) :=
    ProjectivePauliWord.localGroupFintype F
  letI : Finite (localGroup F) :=
    Finite.of_injective (localGroupToFinite F) (localGroupToFinite_injective F)
  exact Fintype.ofFinite (localGroup F)

/-- Support data restricted to a global full-Pauli stabilizer subgroup. -/
noncomputable def stabilizerSupportData (S : Subgroup (FullPauliWord Site)) :
    StabilizerSupportData S Site where
  support s := s.1.label.support
  support_one := by
    change (0 : ProjectivePauliWord Site).support = ∅
    exact Finsupp.support_zero
  support_mul := by
    intro s t
    change (s.1.label + t.1.label).support ⊆ s.1.label.support ∪ t.1.label.support
    exact Finsupp.support_add
  support_inv := by
    intro s
    change (-s.1.label).support ⊆ s.1.label.support
    rw [Finsupp.support_neg]

/-- The syntactic local stabilizer group inside a full-Pauli stabilizer subgroup. -/
noncomputable def stabilizerLocalGroup (S : Subgroup (FullPauliWord Site))
    (F : Finset Site) := (stabilizerSupportData S).localGroup F

/-- Forgetting global stabilizer membership embeds a local stabilizer group into local Paulis. -/
noncomputable def stabilizerLocalGroupToLocalGroup (S : Subgroup (FullPauliWord Site))
    (F : Finset Site) : stabilizerLocalGroup S F → localGroup F := fun s =>
  ⟨s.1.1, s.2⟩

/-- The local-stabilizer inclusion into local full Pauli words is injective. -/
theorem stabilizerLocalGroupToLocalGroup_injective
    (S : Subgroup (FullPauliWord Site)) (F : Finset Site) :
    Function.Injective (stabilizerLocalGroupToLocalGroup S F) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : localGroup F => (u : FullPauliWord Site)) hst

/-- A global full-Pauli stabilizer subgroup has finite local stabilizer groups. -/
noncomputable def stabilizerLocalGroupFintype
    (S : Subgroup (FullPauliWord Site)) (F : Finset Site) :
    Fintype (stabilizerLocalGroup S F) := by
  classical
  letI : Fintype (localGroup F) := localGroupFintype F
  letI : Finite (stabilizerLocalGroup S F) :=
    Finite.of_injective (stabilizerLocalGroupToLocalGroup S F)
      (stabilizerLocalGroupToLocalGroup_injective S F)
  exact Fintype.ofFinite (stabilizerLocalGroup S F)

/-- Every full Pauli word lies in one stage of every finite-region exhaustion. -/
theorem word_mem_localGroup (E : ProjectivePauliWord.FiniteExhaustion Site)
    (g : FullPauliWord Site) : ∃ n, g ∈ localGroup (E.region n) := by
  obtain ⟨n, hn⟩ := E.covers_finset g.label.support
  exact ⟨n, hn⟩

/-- Every global stabilizer lies in one finite local stabilizer group of an exhaustion. -/
theorem stabilizer_mem_localGroup (E : ProjectivePauliWord.FiniteExhaustion Site)
    (S : Subgroup (FullPauliWord Site)) (g : S) :
    ∃ n, g ∈ stabilizerLocalGroup S (E.region n) := by
  obtain ⟨n, hn⟩ := E.covers_finset g.1.label.support
  exact ⟨n, hn⟩

end FullPauliWord

end FiniteFiber
