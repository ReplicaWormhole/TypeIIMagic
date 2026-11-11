import FiniteFiber.QuasilocalStateGNSInterface
import FiniteFiber.StabilizerFiniteFiber

/-!
# The support-corner theorem instantiated at the actual stabilizer model

This file connects three already checked layers of the package:

* the **actual** finite full-Pauli local system of
  `FiniteFiber.FullPauliDirectedLocalSystem` (finite region algebras
  `finiteRegionQubitAlgebra F`, identity padding `localInclusion`, the actual
  full-Pauli matrices `fullPauliRegionMatrix`, and the compatible finite
  stabilizer states of a `FullPauliStabilizerSystem`);
* the C-star/GNS interface of `FiniteFiber.QuasilocalStateGNSInterface`
  (`QuasilocalEmbedding`, `QuasilocalStabilizerState`, their GNS vector
  `Ω = W.gnsVector` and GNS representation `π_ω`);
* the checked support-corner theorem
  `FiniteFiber.stabilizerAverageSequence_supportCornerConclusion_of_gnsOrbit`.

## What is constructed here (unconditional)

For a `QuasilocalEmbedding Site A` the single quasilocal image
`Q.wordElement a ∈ A` of a full-Pauli word is constructed and shown to be
* region independent (`QuasilocalEmbedding.embed_eq_wordElement`),
* multiplicative and unital, hence a group homomorphism
  `QuasilocalEmbedding.wordHom : FullPauliWord Site →* A`.

For a `QuasilocalStabilizerState S Q` this gives the **actual** stabilizer
action on the GNS space,
`W.stabilizerAction : SelfAdjointFiniteGroupAction (H := W.GNS) (G := ↥S.group)`,
whose representing operators are the GNS images `π_ω(g)` of the actual Pauli
stabilizers, are self-adjoint (from algebraic involutivity of the stabilizer
system), and — this is proved, not assumed — **fix the GNS vector**
(`QuasilocalStabilizerState.stabilizerRepresentation_gnsVector`).

Consequently the local supports of any increasing sequence of finite subgroups
of the actual stabilizer group form a decreasing sequence of projections in any
von Neumann algebra containing the represented local algebras, and they all fix
`Ω`.  Neither the vanishing hypothesis `hfix` nor the projection/decrease
hypotheses of the abstract theorem have to be assumed at this instantiation.

## What remains conditional (stated as explicit hypotheses)

The main theorem
`actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit`
is **conditional**.  Its hypotheses are exactly the global inputs which the
present package does not construct:

1. `Q : QuasilocalEmbedding Site A` — the completed quasilocal C-star algebra
   with its faithful, padding-compatible, densely-imaged local embeddings;
2. `W : QuasilocalStabilizerState S Q` — the global stabilizer state extending
   the compatible finite local states, whose GNS data is then Mathlib's;
3. `M` together with `hM` — a von Neumann algebra on the GNS space containing
   the represented finite local algebras;
4. `T : ℕ → Subgroup ↥S.group` with `Fintype` instances and monotonicity — the
   exhausting sequence of *finite* local stabilizer subgroups, giving the
   decreasing finite stabilizer supports;
5. `hstrong` — strong convergence of those supports to `q` (or, in the
   canonical variant, no hypothesis at all: the canonical strong limit is
   used);
6. `C : GNSOrbitConditions M q W.gnsVector` — the regional/complementary
   commutation data, the dense product orbit (fullness), and traciality of the
   compressed vector functional on corner elements.

**No claim is made that 1–6 follow from the manuscript's short-range
definition.**  In particular nothing here constructs `A`, `ω`, the strong limit
of the supports for a concrete lattice, the dense product orbit, or corner
traciality; and no direct-integral or type classification statement is made.

## Conclusion

The conclusion is the existing `SupportCornerConclusion M q Ω`, whose
`central_witness` field is the manuscript's every-nonzero-central-summand
finite-projection statement: for every nonzero central projection `z` of `M`,
`z * q` is a nonzero finite projection of `M` below `z`.  It is restated
separately as `actualStabilizerSystem_central_witness_of_gnsOrbit`, together
with the semifiniteness corollary.
-/

namespace FiniteFiber

open scoped InnerProductSpace

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A]

/-! ### The single quasilocal image of a full-Pauli word -/

namespace QuasilocalEmbedding

variable (Q : QuasilocalEmbedding Site A)

/--
The quasilocal image in `A` of an algebraic full-Pauli word: the image of its
finite-region matrix on the finite region given by its own support.
-/
noncomputable def wordElement (a : FullPauliWord Site) : A :=
  Q.embed a.label.support (fullPauliRegionMatrix a.label.support a)

/--
Region independence: on any finite region containing the support of the word,
the embedded finite-region matrix is the quasilocal image.
-/
theorem embed_eq_wordElement (F : Finset Site) (a : FullPauliWord Site)
    (ha : a.SupportedIn F) :
    Q.embed F (fullPauliRegionMatrix F a) = Q.wordElement a :=
  Q.embed_fullPauliRegionMatrix_eq a.label.support F ha a (Finset.Subset.refl _)

@[simp] theorem wordElement_one : Q.wordElement (1 : FullPauliWord Site) = 1 := by
  have hsupp : (1 : FullPauliWord Site).SupportedIn (∅ : Finset Site) := by
    show (1 : FullPauliWord Site).label.support ⊆ (∅ : Finset Site)
    change (0 : ProjectivePauliWord Site).support ⊆ (∅ : Finset Site)
    simp
  rw [← Q.embed_eq_wordElement ∅ 1 hsupp, fullPauliRegionMatrix_one, map_one]

/-- The quasilocal image is multiplicative: the phases compose exactly. -/
theorem wordElement_mul (a b : FullPauliWord Site) :
    Q.wordElement (a * b) = Q.wordElement a * Q.wordElement b := by
  classical
  set F : Finset Site := a.label.support ∪ b.label.support with hF
  have hlabel : (a * b).label = a.label + b.label := rfl
  have ha : a.SupportedIn F := Finset.subset_union_left
  have hb : b.SupportedIn F := Finset.subset_union_right
  have hab : (a * b).SupportedIn F := by
    show (a * b).label.support ⊆ F
    rw [hlabel]
    exact Finsupp.support_add
  rw [← Q.embed_eq_wordElement F a ha, ← Q.embed_eq_wordElement F b hb,
    ← Q.embed_eq_wordElement F (a * b) hab, fullPauliRegionMatrix_mul F a b ha, map_mul]

/-- The quasilocal images assemble into a group homomorphism. -/
@[simps] noncomputable def wordHom : FullPauliWord Site →* A where
  toFun := Q.wordElement
  map_one' := Q.wordElement_one
  map_mul' := Q.wordElement_mul

/-- The quasilocal image of an involutive word is self-adjoint. -/
theorem isSelfAdjoint_wordElement (a : FullPauliWord Site) (ha : a * a = 1) :
    IsSelfAdjoint (Q.wordElement a) := by
  have hmat : IsSelfAdjoint (fullPauliRegionMatrix a.label.support a) :=
    fullPauliRegionMatrix_isSelfAdjoint a.label.support a (Finset.Subset.refl _) ha
  show star (Q.wordElement a) = Q.wordElement a
  rw [wordElement, ← map_star]
  exact congrArg (Q.embed a.label.support) hmat

end QuasilocalEmbedding

/-! ### The actual stabilizer action on the GNS space -/

namespace QuasilocalStabilizerState

variable [PartialOrder A] [StarOrderedRing A]
variable {S : FullPauliStabilizerSystem Site} {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState S Q)

/--
The GNS representation of the actual global stabilizer group: the stabilizer
word `g` acts by `π_ω(g)`, the GNS image of its quasilocal Pauli operator.
-/
@[simps] noncomputable def stabilizerRepresentation :
    ↥S.group →* (W.GNS →L[ℂ] W.GNS) where
  toFun g := W.gnsRepresentation (Q.wordElement (g : FullPauliWord Site))
  map_one' := by
    show W.gnsRepresentation (Q.wordElement (1 : FullPauliWord Site)) = 1
    rw [Q.wordElement_one, map_one]
  map_mul' g h := by
    show W.gnsRepresentation (Q.wordElement ((g : FullPauliWord Site) * h)) = _
    rw [Q.wordElement_mul, map_mul]

/-- Each represented stabilizer is self-adjoint, by algebraic involutivity. -/
theorem isSelfAdjoint_stabilizerRepresentation (g : ↥S.group) :
    IsSelfAdjoint (W.stabilizerRepresentation g) := by
  have hinv : (g : FullPauliWord Site) * (g : FullPauliWord Site) = 1 :=
    S.involutive _ g.property
  have h := Q.isSelfAdjoint_wordElement (g : FullPauliWord Site) hinv
  show star (W.gnsRepresentation (Q.wordElement (g : FullPauliWord Site))) = _
  rw [← map_star]
  exact congrArg W.gnsRepresentation h.star_eq

/--
**The actual finite-group symmetry data.**  The global Pauli stabilizer group
acting on the GNS space by self-adjoint operators; the local supports of its
finite subgroups are the manuscript's code-space projections.
-/
noncomputable def stabilizerAction :
    SelfAdjointFiniteGroupAction (H := W.GNS) (G := ↥S.group) where
  representation := W.stabilizerRepresentation
  selfAdjoint := W.isSelfAdjoint_stabilizerRepresentation

@[simp] theorem stabilizerAction_representation (g : ↥S.group) :
    W.stabilizerAction.representation g =
      W.gnsRepresentation (Q.wordElement (g : FullPauliWord Site)) := rfl

/--
**The GNS vector is fixed by every actual stabilizer.**  This is proved from
the finite-stage deviation computation of the interface, not assumed.
-/
theorem stabilizerRepresentation_gnsVector (g : ↥S.group) :
    W.stabilizerRepresentation g W.gnsVector = W.gnsVector := by
  have hmem : (g : FullPauliWord Site) ∈
      (S.regionStabilizer (g : FullPauliWord Site).label.support).group :=
    (S.mem_regionStabilizer_group_iff _ _).mpr ⟨g.property, Finset.Subset.refl _⟩
  have h := W.gnsRepresentation_fullPauliRegionMatrix_gnsVector
    ((g : FullPauliWord Site).label.support) ⟨(g : FullPauliWord Site), hmem⟩
  rw [localRepresentation_apply, Q.embed_eq_wordElement _ _ (Finset.Subset.refl _)] at h
  exact h

/-- Every local support of the actual stabilizer action fixes the GNS vector. -/
theorem stabilizerAction_representation_gnsVector (g : ↥S.group) :
    W.stabilizerAction.representation g W.gnsVector = W.gnsVector :=
  W.stabilizerRepresentation_gnsVector g

/-- Each represented stabilizer lies in any von Neumann algebra containing the
represented finite local algebras. -/
theorem stabilizerRepresentation_mem {M : VonNeumannAlgebra W.GNS}
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (g : ↥S.group) : W.stabilizerRepresentation g ∈ M := by
  have h := hM ((g : FullPauliWord Site).label.support)
    (fullPauliRegionMatrix ((g : FullPauliWord Site).label.support)
      (g : FullPauliWord Site))
  rwa [Q.embed_eq_wordElement _ _ (Finset.Subset.refl _)] at h

end QuasilocalStabilizerState

/-! ### The conditional support-corner theorem at the actual stabilizer model -/

section ActualModel

variable [PartialOrder A] [StarOrderedRing A]
variable {S : FullPauliStabilizerSystem Site} {Q : QuasilocalEmbedding Site A}

/--
**The conditional support-corner theorem for the actual full-Pauli stabilizer
model.**

Inputs, all explicit: a consistent full-Pauli stabilizer system `S`; a
quasilocal C-star completion `Q` of the actual finite local algebras; a global
stabilizer state `W` extending the compatible finite local states, with its
Mathlib GNS data; a von Neumann algebra `M` on the GNS space containing the
represented local algebras (`hM`); an increasing sequence `T` of **finite**
subgroups of the actual stabilizer group, whose averages are the decreasing
local code-space supports; strong convergence of those supports to `q`
(`hstrong`); and the GNS-orbit data `C` — regional commutation, dense product
orbit (fullness) and corner traciality.

Conclusion: the full `SupportCornerConclusion`, in particular that every
nonzero central summand of `M` contains the nonzero finite projection `z * q`.

The theorem is conditional exactly in the inputs listed above; nothing else is
assumed.  In particular the projection and decrease of the supports, and the
invariance of the GNS vector under them, are supplied by the model.
-/
theorem actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit
    (W : QuasilocalStabilizerState S Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (T : ℕ → Subgroup ↥S.group) [∀ n, Fintype (T n)]
    (hmonotone : ∀ n m : ℕ, n ≤ m → T n ≤ T m)
    {q : W.GNS →L[ℂ] W.GNS}
    (hstrong : StronglyTendsTo (stabilizerAverageSequence W.stabilizerAction T) q)
    (C : GNSOrbitConditions M q W.gnsVector) :
    SupportCornerConclusion M q W.gnsVector :=
  stabilizerAverageSequence_supportCornerConclusion_of_gnsOrbit
    W.stabilizerAction T
    (fun _ s => W.stabilizerRepresentation_mem hM (s : ↥S.group))
    hmonotone
    (fun _ s => W.stabilizerAction_representation_gnsVector (s : ↥S.group))
    hstrong C

/--
The canonical-strong-limit form: the limit projection is *constructed* from the
decreasing actual stabilizer supports, so no convergence hypothesis is needed.
-/
theorem actualStabilizerSystem_canonicalSupportCornerConclusion_of_gnsOrbit
    (W : QuasilocalStabilizerState S Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (T : ℕ → Subgroup ↥S.group) [∀ n, Fintype (T n)]
    (hmonotone : ∀ n m : ℕ, n ≤ m → T n ≤ T m)
    (C : GNSOrbitConditions M
      (decreasingProjectionStrongLimit
        (stabilizerAverageSequence W.stabilizerAction T)) W.gnsVector) :
    SupportCornerConclusion M
      (decreasingProjectionStrongLimit
        (stabilizerAverageSequence W.stabilizerAction T)) W.gnsVector :=
  stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit
    W.stabilizerAction T
    (fun _ s => W.stabilizerRepresentation_mem hM (s : ↥S.group))
    hmonotone
    (fun _ s => W.stabilizerAction_representation_gnsVector (s : ↥S.group))
    C

/--
**The every-nonzero-central-summand finite-projection statement** for the
actual stabilizer model, under the same explicit global hypotheses: for every
nonzero central projection `z` of `M`, the compression `z * q` is a nonzero
finite projection of `M` below `z`.
-/
theorem actualStabilizerSystem_central_witness_of_gnsOrbit
    (W : QuasilocalStabilizerState S Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (T : ℕ → Subgroup ↥S.group) [∀ n, Fintype (T n)]
    (hmonotone : ∀ n m : ℕ, n ≤ m → T n ≤ T m)
    {q z : W.GNS →L[ℂ] W.GNS}
    (hstrong : StronglyTendsTo (stabilizerAverageSequence W.stabilizerAction T) q)
    (C : GNSOrbitConditions M q W.gnsVector)
    (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    IsFiniteProjection M (z * q) ∧ z * q ≠ 0 ∧ IsSubprojection (z * q) z :=
  (actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit
    W M hM T hmonotone hstrong C).central_witness z hz hz_nonzero

/-- Semifiniteness of `M` under the same explicit global hypotheses. -/
theorem actualStabilizerSystem_semifinite_of_gnsOrbit
    (W : QuasilocalStabilizerState S Q) (M : VonNeumannAlgebra W.GNS)
    (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
      W.gnsRepresentation (Q.embed F x) ∈ M)
    (T : ℕ → Subgroup ↥S.group) [∀ n, Fintype (T n)]
    (hmonotone : ∀ n m : ℕ, n ≤ m → T n ≤ T m)
    {q : W.GNS →L[ℂ] W.GNS}
    (hstrong : StronglyTendsTo (stabilizerAverageSequence W.stabilizerAction T) q)
    (C : GNSOrbitConditions M q W.gnsVector) :
    IsSemifinite M :=
  (actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit
    W M hM T hmonotone hstrong C).semifinite

end ActualModel

end FiniteFiber
