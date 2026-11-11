import AristotleCandidates.CoherentLocalHyperbolicCoordinates
import AristotleCandidates.ConstructedAlgebraicAlpha
import Formalization.CoordinateQuadraticPhase
import Mathlib.Data.Matrix.Basic

/-!
# P53 — the algebraic `alpha` of the local-hyperbolic coordinates

Context declaration: **source basis** `main.tex:1898-1944` (the proposed
`∗`-isomorphism `α : 𝒫_I → 𝒜_Γ` determined on the adapted symplectic basis by
`α(X_i) = P(x_i)`, `α(Z_i) = P(z_i)` and "extended to a homomorphism"), read
together with `main.tex:1671-1679` (short-range order: a symplectic basis of
hyperbolic pairs, each locally supported).

This module instantiates the checked cocycle/word-basis/coherence/direct-limit
theorems with the **concrete P52 coordinate data**
(`AristotleCandidates/CoherentLocalHyperbolicCoordinates.lean`).

## What is constructed here

1. A concrete **twisted Pauli word algebra** `pauliAlgebra B` for every finite
   `F₂`-label group carrying an `F₂`-bilinear form `B` (`PauliForm`): a
   star-subalgebra of a complex matrix algebra whose Pauli words
   `pauliWord B v` form a complex linear basis, multiply with multiplier
   `(-1)^{B v w}` and satisfy `star (word v) = (-1)^{B v v} • word v`.
   This is the ordered `X^a Z^b` convention written in an arbitrary label
   group.
2. The **finite stages**: for the coordinate block of stage `n` the source
   algebra is the twisted algebra of the finite label module
   `sourceLabels n ⊆ (I ⊕ I) →₀ F₂`, and the target ("regional") algebra is
   the twisted algebra of `targetLabels n ⊆ (L ⊕ L) →₀ F₂`.  The connecting
   maps are constructed from the label inclusions.
3. The **phase calibration**: the explicit `ZMod 4`-valued quadratic
   refinement of the coordinate discrepancy of the two Pauli cocycles, and
   proofs of the exact multiplier and involution equations for it.
4. The **finite-stage star equivalences** (through P29), their **commuting
   squares** (through P30) and the **global algebraic star equivalence**
   `alpha` of the two algebraic direct limits (through P23/P31), together
   with its Pauli-word formula, its values on the adapted `Z_i`/`X_i`
   generators and its uniqueness.

No finite-stage `StarAlgEquiv` is supplied: every stage equivalence is built
from the coordinate data below.

## Auxiliary assumptions

Bundled in `LocalHyperbolicAlphaData`, on top of the P52 data
(`LocalHyperbolicFamily`, `LatticeExhaustion`):

* `linearOrder`: a linear order on the coordinate index type `I`, used only to
  fix the ordering convention of the quadratic phase refinement.  (Every set
  admits one; it is data, not a restriction.)
* `symplectic`: the coordinate map preserves the symplectic form, i.e. the
  antisymmetrisations of the source and target Pauli cocycles agree.  This is
  the content of the manuscript's word *symplectic* basis; without it no phase
  calibration whatsoever exists, since the two multiplier cocycles then differ
  by a non-symmetric class.
* `stage_surjective`: at every stage the coordinate map carries the stage-`n`
  source labels **onto** the stage-`n` target labels.  P52 proves injectivity
  and `⊆`; surjectivity is the finite-stage form of the manuscript's clause
  that the hyperbolic pairs are a *basis* of `V_Γ` with `|I| = |Γ|`, and it is
  not derivable from local support alone.  It is exactly the finite-stage
  bijectivity premise the packet asks to expose.

Nothing else is assumed: the word bases, multipliers, involution phases, the
phase character itself, the finite-stage equivalences and the commuting
squares are all constructed or proved.

The two auxiliary assumptions are consistent: `standardAlphaData` exhibits a
witness, the tautological hyperbolic coordinates on the lattice `ℕ`.  So the
results below are not vacuous.

## What is *not* claimed

Everything below is algebra.  No C⋆-norm, completion, state identity, GNS
representation, tensor factorization, factorhood, trace or weight statement is
used or claimed.
-/

namespace StabilizerHyperfinite

namespace LocalHyperbolicAlpha

open CoherentLocalHyperbolic
open FiniteAdaptedCoordinate FiniteCoordinateEquivCoherence

/-! ## The `±1` sign of a Pauli bit -/

/-- The `±1` sign attached to a Pauli bit, written as a fourth-root phase so
that it matches the checked quadratic-phase interface. -/
noncomputable def pauliSign (b : PauliBit) : ℂ := zmodFourPhase (2 * liftPauliBit b)

@[simp] theorem pauliSign_zero : pauliSign 0 = 1 := by
  simp [pauliSign, zmodFourPhase]

@[simp] theorem pauliSign_one : pauliSign 1 = -1 := by
  have h : ((2 : ZMod 4)).val = 2 := rfl
  simp [pauliSign, zmodFourPhase, liftPauliBit, h, pow_two, Complex.I_mul_I]

theorem pauliSign_add (a b : PauliBit) :
    pauliSign (a + b) = pauliSign a * pauliSign b := by
  simp only [pauliSign, two_liftPauliBit_add, zmodFourPhase_add]

theorem star_pauliSign (a : PauliBit) : star (pauliSign a) = pauliSign a := by
  fin_cases a <;> simp

theorem pauliSign_ne_zero (a : PauliBit) : pauliSign a ≠ 0 := by
  fin_cases a <;> simp

/-! ## `F₂`-bilinear forms on Pauli label groups -/

/-- An `F₂`-bilinear form on a Pauli label group.  It plays the role of the
`Z`-versus-`X` pairing that produces the Pauli multiplier of the ordered
`X^a Z^b` word convention. -/
structure PauliForm (V : Type*) [AddCommGroup V] where
  /-- The underlying pairing. -/
  form : V → V → PauliBit
  /-- Additivity in the left argument. -/
  add_left : ∀ u v w, form (u + v) w = form u w + form v w
  /-- Additivity in the right argument. -/
  add_right : ∀ u v w, form u (v + w) = form u v + form u w

namespace PauliForm

variable {V : Type*} [AddCommGroup V]

theorem zero_left (B : PauliForm V) (w : V) : B.form 0 w = 0 := by
  have h := B.add_left 0 0 w
  rw [add_zero] at h
  have h2 : B.form 0 w + B.form 0 w = B.form 0 w + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem zero_right (B : PauliForm V) (v : V) : B.form v 0 = 0 := by
  have h := B.add_right v 0 0
  rw [add_zero] at h
  have h2 : B.form v 0 + B.form v 0 = B.form v 0 + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- The restriction of a label form to a submodule of labels. -/
def restrict [Module PauliBit V] (B : PauliForm V) (p : Submodule PauliBit V) :
    PauliForm p where
  form v w := B.form (v : V) (w : V)
  add_left u v w := B.add_left (u : V) (v : V) (w : V)
  add_right u v w := B.add_right (u : V) (v : V) (w : V)

@[simp] theorem restrict_form [Module PauliBit V] (B : PauliForm V)
    (p : Submodule PauliBit V) (v w : p) :
    (B.restrict p).form v w = B.form (v : V) (w : V) := rfl

end PauliForm

/-! ## The twisted Pauli word algebra of a finite label group -/

section Twisted

variable {V : Type*} [AddCommGroup V] [Module PauliBit V]

theorem pauli_neg_eq_self (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_right (pauliBit_add_self_eq_zero v)

variable [DecidableEq V]

/-- The twisted Pauli word matrix of a label: the `V × V` permutation matrix of
the translation by `v`, decorated with the sign of the label form. -/
noncomputable def pauliMat (B : PauliForm V) (v : V) : Matrix V V ℂ :=
  Matrix.of fun r c => if r = v + c then pauliSign (B.form v c) else 0

omit [Module PauliBit V] in
theorem pauliMat_apply (B : PauliForm V) (v r c : V) :
    pauliMat B v r c = if r = v + c then pauliSign (B.form v c) else 0 := rfl

omit [Module PauliBit V] in
theorem pauliMat_zero (B : PauliForm V) : pauliMat B 0 = 1 := by
  ext r c
  rw [pauliMat_apply, Matrix.one_apply, zero_add, B.zero_left]
  simp

theorem pauliMat_star (B : PauliForm V) (v : V) :
    star (pauliMat B v) = pauliSign (B.form v v) • pauliMat B v := by
  ext r c
  rw [Matrix.star_apply, pauliMat_apply, Matrix.smul_apply, pauliMat_apply]
  by_cases h : r = v + c
  · have hc : c = v + r := by
      rw [h, ← add_assoc, pauliBit_add_self_eq_zero, zero_add]
    rw [if_pos hc, if_pos h, star_pauliSign, h, B.add_right, pauliSign_add, smul_eq_mul]
  · have hc : ¬ c = v + r := by
      intro hc
      exact h (by rw [hc, ← add_assoc, pauliBit_add_self_eq_zero, zero_add])
    rw [if_neg hc, if_neg h, star_zero, smul_eq_mul, mul_zero]

variable [Fintype V]

omit [Module PauliBit V] in
theorem pauliMat_mul (B : PauliForm V) (v w : V) :
    pauliMat B v * pauliMat B w = pauliSign (B.form v w) • pauliMat B (v + w) := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (w + c)]
  · rw [pauliMat_apply, pauliMat_apply, Matrix.smul_apply, pauliMat_apply,
      if_pos rfl, ← add_assoc, B.add_right, B.add_left, pauliSign_add, pauliSign_add,
      smul_eq_mul]
    by_cases h : r = v + w + c
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  · intro b _ hb
    rw [pauliMat_apply (v := w), if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Module PauliBit V] in
theorem pauliMat_linearIndependent (B : PauliForm V) :
    LinearIndependent ℂ (pauliMat B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have h := congrFun (congrFun hg v) 0
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply, pauliMat_apply,
    add_zero, B.zero_right, pauliSign_zero, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single v] at h
  · simpa using h
  · intro b _ hb
    rw [if_neg (by exact fun hh => hb hh.symm)]
  · intro hv
    exact absurd (Finset.mem_univ _) hv

/-- The complex span of the twisted Pauli words. -/
noncomputable def pauliSpan (B : PauliForm V) : Submodule ℂ (Matrix V V ℂ) :=
  Submodule.span ℂ (Set.range (pauliMat B))

omit [Module PauliBit V] [Fintype V] in
theorem pauliMat_mem_span (B : PauliForm V) (v : V) : pauliMat B v ∈ pauliSpan B :=
  Submodule.subset_span ⟨v, rfl⟩

omit [Module PauliBit V] [Fintype V] in
theorem one_mem_pauliSpan (B : PauliForm V) : (1 : Matrix V V ℂ) ∈ pauliSpan B := by
  rw [← pauliMat_zero B]
  exact pauliMat_mem_span B 0

omit [Module PauliBit V] in
theorem mul_mem_pauliSpan (B : PauliForm V) (x y : Matrix V V ℂ)
    (hx : x ∈ pauliSpan B) (hy : y ∈ pauliSpan B) : x * y ∈ pauliSpan B := by
  have hle : pauliSpan B * pauliSpan B ≤ pauliSpan B := by
    rw [pauliSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro z hz
    obtain ⟨a, ⟨v, rfl⟩, b, ⟨w, rfl⟩, rfl⟩ := hz
    show pauliMat B v * pauliMat B w ∈ pauliSpan B
    rw [pauliMat_mul]
    exact Submodule.smul_mem _ _ (pauliMat_mem_span B (v + w))
  exact hle (Submodule.mul_mem_mul hx hy)

omit [Fintype V] in
theorem star_mem_pauliSpan (B : PauliForm V) {x : Matrix V V ℂ}
    (hx : x ∈ pauliSpan B) : star x ∈ pauliSpan B := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      rw [pauliMat_star]
      exact Submodule.smul_mem _ _ (pauliMat_mem_span B v)
  | zero => simp
  | add a b _ _ iha ihb => rw [star_add]; exact Submodule.add_mem _ iha ihb
  | smul c a _ iha => rw [star_smul]; exact Submodule.smul_mem _ _ iha

/-- **The twisted Pauli word algebra** of a finite label group with a label
form: the star-subalgebra of the matrix algebra spanned by the twisted Pauli
words. -/
noncomputable def pauliAlgebra (B : PauliForm V) : StarSubalgebra ℂ (Matrix V V ℂ) where
  toSubalgebra := (pauliSpan B).toSubalgebra (one_mem_pauliSpan B) (mul_mem_pauliSpan B)
  star_mem' := star_mem_pauliSpan B

/-- The Pauli word of a label, as an element of the twisted algebra. -/
noncomputable def pauliWord (B : PauliForm V) (v : V) : pauliAlgebra B :=
  ⟨pauliMat B v, pauliMat_mem_span B v⟩

@[simp] theorem pauliWord_coe (B : PauliForm V) (v : V) :
    ((pauliWord B v : pauliAlgebra B) : Matrix V V ℂ) = pauliMat B v := rfl

theorem pauliWord_zero (B : PauliForm V) : pauliWord B 0 = 1 :=
  Subtype.ext (by rw [pauliWord_coe]; exact pauliMat_zero B)

theorem pauliWord_mul (B : PauliForm V) (v w : V) :
    pauliWord B v * pauliWord B w = pauliSign (B.form v w) • pauliWord B (v + w) :=
  Subtype.ext (by
    push_cast
    simpa using pauliMat_mul B v w)

theorem pauliWord_star (B : PauliForm V) (v : V) :
    star (pauliWord B v) = pauliSign (B.form v v) • pauliWord B (-v) :=
  Subtype.ext (by
    rw [pauli_neg_eq_self]
    push_cast
    simpa using pauliMat_star B v)

/-- **The Pauli word star system** of the twisted algebra: the words, their
multiplier `(-1)^{B v w}` and their involution phase `(-1)^{B v v}`. -/
noncomputable def pauliSystem (B : PauliForm V) :
    PauliWordStarSystem V (pauliAlgebra B) where
  word := pauliWord B
  multiplier v w := pauliSign (B.form v w)
  word_mul := pauliWord_mul B
  star_multiplier v := pauliSign (B.form v v)
  word_star := pauliWord_star B

@[simp] theorem pauliSystem_word (B : PauliForm V) (v : V) :
    (pauliSystem B).word v = pauliWord B v := rfl

@[simp] theorem pauliSystem_multiplier (B : PauliForm V) (v w : V) :
    (pauliSystem B).multiplier v w = pauliSign (B.form v w) := rfl

@[simp] theorem pauliSystem_star_multiplier (B : PauliForm V) (v : V) :
    (pauliSystem B).star_multiplier v = pauliSign (B.form v v) := rfl

/-- **The Pauli words form a complex linear basis** of the twisted algebra. -/
noncomputable def pauliWordBasis (B : PauliForm V) : Module.Basis V ℂ (pauliAlgebra B) :=
  Module.Basis.span (pauliMat_linearIndependent B)

@[simp] theorem pauliWordBasis_apply (B : PauliForm V) (v : V) :
    pauliWordBasis B v = pauliWord B v :=
  Subtype.ext (Module.Basis.span_apply (pauliMat_linearIndependent B) v)

/-- Two complex-linear maps out of a twisted Pauli algebra agreeing on all
Pauli words agree. -/
theorem pauliAlgebra_linear_ext {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (B : PauliForm V) (g h : pauliAlgebra B →ₗ[ℂ] X)
    (hgh : ∀ v, g (pauliWord B v) = h (pauliWord B v)) (x : pauliAlgebra B) :
    g x = h x := by
  have := Module.Basis.ext (b := pauliWordBasis B) (f₁ := g) (f₂ := h) (by
    intro v; rw [pauliWordBasis_apply]; exact hgh v)
  exact congrArg (fun f : pauliAlgebra B →ₗ[ℂ] X => f x) this

end Twisted

/-! ## Morphisms of twisted Pauli algebras -/

section Morphism

variable {V W : Type*}
variable [AddCommGroup V] [Module PauliBit V] [DecidableEq V] [Fintype V]
variable [AddCommGroup W] [Module PauliBit W] [DecidableEq W] [Fintype W]

/-- The complex-linear word map underlying `twistHom`. -/
noncomputable def twistLinear (B : PauliForm V) (C : PauliForm W) (f : V →+ W) :
    pauliAlgebra B →ₗ[ℂ] pauliAlgebra C :=
  (pauliWordBasis B).constr ℂ (fun v => pauliWord C (f v))

@[simp] theorem twistLinear_word (B : PauliForm V) (C : PauliForm W) (f : V →+ W) (v : V) :
    twistLinear B C f (pauliWord B v) = pauliWord C (f v) := by
  rw [twistLinear, ← pauliWordBasis_apply, Module.Basis.constr_basis]

/-- The star-algebra map of twisted Pauli algebras induced by a form-preserving
additive map of labels.  It is *constructed* from the word bases; no morphism
is assumed. -/
noncomputable def twistHom (B : PauliForm V) (C : PauliForm W) (f : V →+ W)
    (hf : ∀ v w, C.form (f v) (f w) = B.form v w) :
    pauliAlgebra B →⋆ₐ[ℂ] pauliAlgebra C :=
  starAlgHomOfBasis (twistLinear B C f) (pauliWordBasis B)
    (by
      rw [show (1 : pauliAlgebra B) = pauliWord B 0 from (pauliWord_zero B).symm,
        twistLinear_word, map_zero, pauliWord_zero])
    (by
      intro v w
      simp only [pauliWordBasis_apply, pauliWord_mul, map_smul, twistLinear_word,
        map_add, hf])
    (by
      intro v
      simp only [pauliWordBasis_apply, pauliWord_star, map_smul, twistLinear_word,
        pauli_neg_eq_self, hf])

@[simp] theorem twistHom_word (B : PauliForm V) (C : PauliForm W) (f : V →+ W)
    (hf : ∀ v w, C.form (f v) (f w) = B.form v w) (v : V) :
    twistHom B C f hf (pauliWord B v) = pauliWord C (f v) :=
  twistLinear_word B C f v

/-- Any star-algebra map with the same Pauli-word formula is the constructed
one. -/
theorem twistHom_unique (B : PauliForm V) (C : PauliForm W) (f : V →+ W)
    (hf : ∀ v w, C.form (f v) (f w) = B.form v w)
    (g : pauliAlgebra B →⋆ₐ[ℂ] pauliAlgebra C)
    (hg : ∀ v, g (pauliWord B v) = pauliWord C (f v)) (x : pauliAlgebra B) :
    g x = twistHom B C f hf x :=
  pauliAlgebra_linear_ext B g.toAlgHom.toLinearMap
    (twistHom B C f hf).toAlgHom.toLinearMap
    (fun v => by
      show g (pauliWord B v) = twistHom B C f hf (pauliWord B v)
      rw [hg v, twistHom_word]) x

end Morphism


/-- The `Z`-versus-`X` pairing of Pauli coordinate words: the exponent of the
multiplier in the ordered `X^a Z^b` word convention. -/
def coordPairing (J : Type*) : PauliForm (PauliCoordinateLabels J) where
  form v w := v.sum fun p c => c * Sum.elim (fun i => w (Sum.inr i)) (fun _ => (0 : PauliBit)) p
  add_left u v w := by
    apply Finsupp.sum_add_index'
    · intro p; rw [zero_mul]
    · intro p a b; rw [add_mul]
  add_right u v w := by
    show (u.sum fun p c => c * Sum.elim (fun i => (v + w) (Sum.inr i)) (fun _ => (0 : PauliBit)) p)
      = (u.sum fun p c => c * Sum.elim (fun i => v (Sum.inr i)) (fun _ => (0 : PauliBit)) p)
        + u.sum fun p c => c * Sum.elim (fun i => w (Sum.inr i)) (fun _ => (0 : PauliBit)) p
    rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    rintro (p | p) _ <;> simp [mul_add]

/-- The `ZMod 4` fourth-root phase as a unit of `ℂ`. -/
noncomputable def phaseUnit (a : ZMod 4) : ℂˣ where
  val := zmodFourPhase a
  inv := zmodFourPhase (-a)
  val_inv := by rw [← zmodFourPhase_add, add_neg_cancel]; simp [zmodFourPhase]
  inv_val := by rw [← zmodFourPhase_add, neg_add_cancel]; simp [zmodFourPhase]

@[simp] theorem phaseUnit_val (a : ZMod 4) : (phaseUnit a : ℂ) = zmodFourPhase a := rfl

@[simp] theorem zmodFourPhase_zero : zmodFourPhase 0 = 1 := by simp [zmodFourPhase]

/-- **The coordinate discrepancy pairing of a label form.**  For a bilinear
`F₂`-form on finitely supported coordinate words, the `ZMod 4` coordinate
pairing of its matrix of values on single coordinates is twice the lift of the
form. -/
theorem coordinateBilinear_of_pauliForm {ι : Type*} [LinearOrder ι]
    (G : PauliForm (ι →₀ PauliBit)) (v w : ι →₀ PauliBit) :
    coordinateBilinear (fun p q => G.form (Finsupp.single p 1) (Finsupp.single q 1)) v w =
      2 * liftPauliBit (G.form v w) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [coordinateBilinear, G.zero_left]
  | add f g hf hg =>
      rw [coordinateBilinear_add_left, hf, hg, G.add_left, two_liftPauliBit_add]
  | single p a =>
      induction w using Finsupp.induction_linear with
      | zero => simp [coordinateBilinear, G.zero_right]
      | add f g hf hg =>
          rw [coordinateBilinear_add_right, hf, hg, G.add_right, two_liftPauliBit_add]
      | single q b =>
          fin_cases a
          · simp [coordinateBilinear, G.zero_left]
          · fin_cases b
            · simp [coordinateBilinear, G.zero_right]
            · simp [coordinateBilinear]


/-! ## The local-hyperbolic coordinate data of this packet -/

section Data

variable {L I : Type*}

/-- A linear order on the source coordinate index, used only to fix the
ordering convention of the quadratic phase refinement. -/
noncomputable local instance sumLinearOrder [LinearOrder I] : LinearOrder (I ⊕ I) :=
  LinearOrder.lift' (toLex : I ⊕ I → I ⊕ₗ I) (Equiv.injective _)

/-- **The data of this packet.**  On top of the P52 local-hyperbolic family and
lattice exhaustion it carries exactly two auxiliary assumptions: the coordinate
map is symplectic, and it is onto the finite target labels at every stage. -/
structure AlphaData (L I : Type*) [LinearOrder I] where
  /-- The P52 locally supported adapted hyperbolic family. -/
  family : CoherentLocalHyperbolic.LocalHyperbolicFamily L I
  /-- The P52 lattice exhaustion. -/
  exhaustion : CoherentLocalHyperbolic.LatticeExhaustion L
  /-- **Auxiliary assumption (symplectic coordinates).**  The coordinate map
  preserves the symplectic form, i.e. the antisymmetrisations of the source and
  target Pauli pairings agree. -/
  symplectic : ∀ v w : PauliCoordinateLabels I,
    (coordPairing I).form v w + (coordPairing I).form w v =
      (coordPairing L).form (family.coordinateMap v) (family.coordinateMap w) +
        (coordPairing L).form (family.coordinateMap w) (family.coordinateMap v)
  /-- **Auxiliary assumption (finite-stage adaptedness).**  At every stage the
  coordinate map is onto the stage labels of the region. -/
  stage_surjective : ∀ (n : ℕ), ∀ u ∈ exhaustion.targetLabels n,
    ∃ c ∈ family.sourceLabels exhaustion n, family.coordinateMap c = u

namespace AlphaData

variable [LinearOrder I] (A : AlphaData L I)

/-- The stage-`n` source Pauli labels. -/
abbrev SourceLabel (n : ℕ) : Submodule PauliBit (PauliCoordinateLabels I) :=
  A.family.sourceLabels A.exhaustion n

/-- The stage-`n` target (regional) Pauli labels. -/
abbrev TargetLabel (n : ℕ) : Submodule PauliBit (CoherentLocalHyperbolic.PhaseSpace L) :=
  A.exhaustion.targetLabels n

noncomputable instance sourceLabelFintype (n : ℕ) : Fintype (A.SourceLabel n) := by
  haveI : Module.Finite PauliBit (A.SourceLabel n) :=
    A.family.sourceLabels_moduleFinite A.exhaustion n
  haveI : Finite (A.SourceLabel n) := Module.finite_of_finite PauliBit
  exact Fintype.ofFinite _

noncomputable instance targetLabelFintype (n : ℕ) : Fintype (A.TargetLabel n) := by
  haveI : Module.Finite PauliBit (A.TargetLabel n) :=
    A.exhaustion.targetLabels_moduleFinite n
  haveI : Finite (A.TargetLabel n) := Module.finite_of_finite PauliBit
  exact Fintype.ofFinite _

noncomputable instance sourceLabelDecEq (n : ℕ) : DecidableEq (A.SourceLabel n) :=
  Classical.decEq _

noncomputable instance targetLabelDecEq (n : ℕ) : DecidableEq (A.TargetLabel n) :=
  Classical.decEq _

/-- The stage-`n` source label form: the coordinate pairing of the source
Pauli words. -/
noncomputable def sourceForm (n : ℕ) : PauliForm (A.SourceLabel n) :=
  (coordPairing I).restrict _

/-- The stage-`n` target label form: the coordinate pairing of the regional
Pauli words. -/
noncomputable def targetForm (n : ℕ) : PauliForm (A.TargetLabel n) :=
  (coordPairing L).restrict _

/-- The stage-`n` label map: the P52 block coordinate map. -/
noncomputable def stageLabelMap (n : ℕ) : A.SourceLabel n →+ A.TargetLabel n :=
  (A.family.blockCoordinateMap A.exhaustion n).toAddMonoidHom

@[simp] theorem stageLabelMap_coe (n : ℕ) (v : A.SourceLabel n) :
    ((A.stageLabelMap n v : A.TargetLabel n) : CoherentLocalHyperbolic.PhaseSpace L) =
      A.family.coordinateMap (v : PauliCoordinateLabels I) := rfl

theorem stageLabelMap_bijective (n : ℕ) : Function.Bijective (A.stageLabelMap n) := by
  constructor
  · intro v w h
    exact A.family.blockCoordinateMap_injective A.exhaustion n h
  · intro u
    obtain ⟨c, hc, hcu⟩ := A.stage_surjective n (u : CoherentLocalHyperbolic.PhaseSpace L) u.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcu⟩

/-- The stage-`n` label bijection. -/
noncomputable def stageLabelEquiv (n : ℕ) : A.SourceLabel n ≃ A.TargetLabel n :=
  Equiv.ofBijective _ (A.stageLabelMap_bijective n)


/-! ### The phase calibration -/

/-- In characteristic two, `a + b = c + d` may be rearranged. -/
theorem pauliBit_cross {a b c d : PauliBit} (h : a + b = c + d) : a + c = b + d := by
  revert h
  revert a b c d
  decide

/-- The combined discrepancy form: the difference of the source Pauli pairing
and the pullback of the target Pauli pairing. -/
noncomputable def discForm : PauliForm (PauliCoordinateLabels I) where
  form v w := (coordPairing I).form v w +
    (coordPairing L).form (A.family.coordinateMap v) (A.family.coordinateMap w)
  add_left u v w := by
    rw [(coordPairing I).add_left, map_add, (coordPairing L).add_left]
    ring
  add_right u v w := by
    rw [(coordPairing I).add_right, map_add, (coordPairing L).add_right]
    ring

@[simp] theorem discForm_form (v w : PauliCoordinateLabels I) :
    A.discForm.form v w = (coordPairing I).form v w +
      (coordPairing L).form (A.family.coordinateMap v) (A.family.coordinateMap w) := rfl

/-- The discrepancy matrix of the two Pauli cocycles in the coordinate basis. -/
noncomputable def discrepancy : (I ⊕ I) → (I ⊕ I) → PauliBit :=
  fun p q => A.discForm.form (Finsupp.single p 1) (Finsupp.single q 1)

theorem discrepancy_symm (p q : I ⊕ I) : A.discrepancy p q = A.discrepancy q p := by
  exact pauliBit_cross (A.symplectic (Finsupp.single p 1) (Finsupp.single q 1))

theorem coordinateBilinear_discrepancy (v w : PauliCoordinateLabels I) :
    coordinateBilinear A.discrepancy v w = 2 * liftPauliBit (A.discForm.form v w) :=
  coordinateBilinear_of_pauliForm A.discForm v w

/-- **The phase character.**  The `ZMod 4`-valued quadratic refinement of the
coordinate discrepancy of the two Pauli cocycles. -/
noncomputable def qGlobal : PauliCoordinateLabels I → ZMod 4 :=
  coordinateQuadraticRefinement A.discrepancy

theorem qGlobal_zero : A.qGlobal 0 = 0 :=
  coordinateQuadraticRefinement_zero A.discrepancy

theorem qGlobal_add (v w : PauliCoordinateLabels I) :
    A.qGlobal (v + w) = A.qGlobal v + A.qGlobal w + coordinateBilinear A.discrepancy v w :=
  coordinateQuadraticRefinement_polarization A.discrepancy A.discrepancy_symm v w

theorem two_qGlobal (v : PauliCoordinateLabels I) :
    2 * A.qGlobal v = coordinateBilinear A.discrepancy v v :=
  two_coordinateQuadraticRefinement A.discrepancy A.discrepancy_symm v

/-- The stage-`n` phase: the phase character read on the stage labels. -/
noncomputable def phase (n : ℕ) : A.SourceLabel n → ℂ :=
  fun v => zmodFourPhase (A.qGlobal (v : PauliCoordinateLabels I))

/-- **The multiplier equation of the phase calibration.** -/
theorem stage_mulCompatible (n : ℕ) :
    PauliWordStarSystem.MultiplicationCompatibleBetween
      (pauliSystem (A.sourceForm n)) (pauliSystem (A.targetForm n))
      (A.stageLabelMap n) (A.phase n) := by
  show PauliWordStarSystem.MultiplicationCompatibleBetween
    (pauliSystem (A.sourceForm n)) (pauliSystem (A.targetForm n)) (A.stageLabelMap n)
    (fun v => zmodFourPhase (A.qGlobal (v : PauliCoordinateLabels I)))
  refine quadraticPhase_multiplicationCompatibleBetween (pauliSystem (A.sourceForm n))
    (pauliSystem (A.targetForm n)) (A.stageLabelMap n)
    (fun v => A.qGlobal (v : PauliCoordinateLabels I))
    (fun v w => liftPauliBit ((A.sourceForm n).form v w))
    (fun u u' => liftPauliBit ((A.targetForm n).form u u'))
    (fun v w => rfl) (fun u u' => rfl) ?_
  intro v w
  dsimp only
  have hcoe : ((v + w : A.SourceLabel n) : PauliCoordinateLabels I) =
      (v : PauliCoordinateLabels I) + (w : PauliCoordinateLabels I) := rfl
  rw [hcoe, A.qGlobal_add, A.coordinateBilinear_discrepancy, discForm_form,
    two_liftPauliBit_add, mul_add]
  rfl

/-- **The involution equation of the phase calibration.** -/
theorem stage_starCompatible (n : ℕ) :
    PauliWordStarSystem.StarCompatibleBetween
      (pauliSystem (A.sourceForm n)) (pauliSystem (A.targetForm n))
      (A.stageLabelMap n) (A.phase n) := by
  show PauliWordStarSystem.StarCompatibleBetween
    (pauliSystem (A.sourceForm n)) (pauliSystem (A.targetForm n)) (A.stageLabelMap n)
    (fun v => zmodFourPhase (A.qGlobal (v : PauliCoordinateLabels I)))
  refine quadraticPhase_starCompatibleBetween (pauliSystem (A.sourceForm n))
    (pauliSystem (A.targetForm n)) (A.stageLabelMap n)
    (fun v => A.qGlobal (v : PauliCoordinateLabels I))
    (fun v => liftPauliBit ((A.sourceForm n).form v v))
    (fun u => liftPauliBit ((A.targetForm n).form u u))
    (fun v => rfl) (fun u => rfl) ?_
  intro v
  dsimp only
  rw [A.two_qGlobal, A.coordinateBilinear_discrepancy, discForm_form,
    two_liftPauliBit_add, mul_add]
  rfl



/-! ### The finite adapted coordinate basis of a stage -/

/-- The stage-`n` coordinate index type: the P52 coordinate block. -/
abbrev Coord (n : ℕ) : Type _ := ↥(A.family.coordinateBlock A.exhaustion n)

instance coordFinite (n : ℕ) : Finite (A.Coord n) :=
  (A.family.coordinateBlock_finite A.exhaustion n).to_subtype

/-- The set of coordinate positions of stage `n`. -/
def coordSupport (n : ℕ) : Set (I ⊕ I) :=
  {p : I ⊕ I | CoherentLocalHyperbolic.site p ∈ A.family.coordinateBlock A.exhaustion n}

/-- The stage-`n` coordinate positions are the `Z` and `X` positions of the
block. -/
def blockIndexEquiv (n : ℕ) : (A.Coord n ⊕ A.Coord n) ≃ ↥(A.coordSupport n) where
  toFun := Sum.elim (fun i => ⟨Sum.inl i.1, i.2⟩) (fun i => ⟨Sum.inr i.1, i.2⟩)
  invFun p := match p with
    | ⟨Sum.inl i, h⟩ => Sum.inl ⟨i, h⟩
    | ⟨Sum.inr i, h⟩ => Sum.inr ⟨i, h⟩
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro ⟨(i | i), h⟩ <;> rfl

/-- **The finite adapted coordinate basis of a stage**: the single-coordinate
words of the stage-`n` block. -/
noncomputable def stageCoordBasis (n : ℕ) :
    Module.Basis (A.Coord n ⊕ A.Coord n) PauliBit (A.SourceLabel n) :=
  (Finsupp.basisSingleOne (ι := A.Coord n ⊕ A.Coord n) (R := PauliBit)).map
    ((Finsupp.domLCongr (A.blockIndexEquiv n)).trans
      (Finsupp.supportedEquivFinsupp (A.coordSupport n)).symm)

theorem stageCoordBasis_coe (n : ℕ) (p : A.Coord n ⊕ A.Coord n) :
    ((A.stageCoordBasis n p : A.SourceLabel n) : PauliCoordinateLabels I) =
      Finsupp.single ((A.blockIndexEquiv n p : ↥(A.coordSupport n)) : I ⊕ I) 1 := by
  rw [stageCoordBasis, Module.Basis.map_apply,
    show (Finsupp.basisSingleOne (ι := A.Coord n ⊕ A.Coord n) (R := PauliBit)) p
      = Finsupp.single p 1 from by simp,
    LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  show ((Finsupp.restrictSupportEquiv (A.coordSupport n) PauliBit).symm
    (Finsupp.single (A.blockIndexEquiv n p) 1) : PauliCoordinateLabels I) = _
  rw [Finsupp.restrictSupportEquiv_symm_single]

/-- The stage-`n` adapted coordinate data: the `Z` and `X` single-coordinate
words of the block form a basis of the stage source labels. -/
noncomputable def stageCoordinates (n : ℕ) :
    AdaptedPauliCoordinateBasis (I := A.Coord n) (V := A.SourceLabel n) where
  z i := A.stageCoordBasis n (Sum.inl i)
  x i := A.stageCoordBasis n (Sum.inr i)
  basis := A.stageCoordBasis n
  basis_z _ := rfl
  basis_x _ := rfl

@[simp] theorem stageCoordinates_z_coe (n : ℕ) (i : A.Coord n) :
    (((A.stageCoordinates n).z i : A.SourceLabel n) : PauliCoordinateLabels I) =
      Finsupp.single (Sum.inl (i : I)) 1 :=
  A.stageCoordBasis_coe n (Sum.inl i)

@[simp] theorem stageCoordinates_x_coe (n : ℕ) (i : A.Coord n) :
    (((A.stageCoordinates n).x i : A.SourceLabel n) : PauliCoordinateLabels I) =
      Finsupp.single (Sum.inr (i : I)) 1 :=
  A.stageCoordBasis_coe n (Sum.inr i)

/-- **The manuscript's `α(Z_i) = P(z_i)` label equation.**  The stage label map
carries the `Z` coordinate word of `i` to the hyperbolic vector `z i`. -/
theorem stageLabelMap_z (n : ℕ) (i : A.Coord n) :
    ((A.stageLabelMap n ((A.stageCoordinates n).z i) : A.TargetLabel n) :
        CoherentLocalHyperbolic.PhaseSpace L) = A.family.z (i : I) := by
  rw [stageLabelMap_coe, stageCoordinates_z_coe, A.family.coordinateMap_single_z]

/-- **The manuscript's `α(X_i) = P(x_i)` label equation.** -/
theorem stageLabelMap_x (n : ℕ) (i : A.Coord n) :
    ((A.stageLabelMap n ((A.stageCoordinates n).x i) : A.TargetLabel n) :
        CoherentLocalHyperbolic.PhaseSpace L) = A.family.x (i : I) := by
  rw [stageLabelMap_coe, stageCoordinates_x_coe, A.family.coordinateMap_single_x]

/-! ### The finite-stage word map -/

/-- The stage-`n` complex-linear word map: the phase-corrected relabelling of
the Pauli word bases. -/
noncomputable def stageLinear (n : ℕ) :
    pauliAlgebra (A.sourceForm n) ≃ₗ[ℂ] pauliAlgebra (A.targetForm n) :=
  (pauliWordBasis (A.sourceForm n)).equiv
    ((pauliWordBasis (A.targetForm n)).unitsSMul
      (fun u => phaseUnit (A.qGlobal
        (((A.stageLabelEquiv n).symm u : A.SourceLabel n) : PauliCoordinateLabels I))))
    (A.stageLabelEquiv n)

theorem stageLinear_word (n : ℕ) (v : A.SourceLabel n) :
    A.stageLinear n (pauliWord (A.sourceForm n) v) =
      A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v) := by
  rw [← pauliWordBasis_apply, stageLinear, Module.Basis.equiv_apply,
    Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply, pauliWordBasis_apply,
    Units.smul_def, phaseUnit_val]
  rfl

theorem stageLinear_one (n : ℕ) : A.stageLinear n 1 = 1 := by
  rw [show (1 : pauliAlgebra (A.sourceForm n)) = pauliWord (A.sourceForm n) 0 from
      (pauliWord_zero _).symm, stageLinear_word]
  have h0 : A.phase n 0 = 1 := by
    show zmodFourPhase (A.qGlobal ((0 : A.SourceLabel n) : PauliCoordinateLabels I)) = 1
    rw [ZeroMemClass.coe_zero, A.qGlobal_zero, zmodFourPhase_zero]
  rw [h0, one_smul, map_zero, pauliWord_zero]


/-! ### The connecting maps of the two directed systems -/

/-- The inclusion of stage-`n` source labels into stage-`m` source labels. -/
noncomputable def sourceIncl {n m : ℕ} (h : n ≤ m) : A.SourceLabel n →+ A.SourceLabel m :=
  (Submodule.inclusion (A.family.sourceLabels_mono A.exhaustion h)).toAddMonoidHom

@[simp] theorem sourceIncl_coe {n m : ℕ} (h : n ≤ m) (v : A.SourceLabel n) :
    ((A.sourceIncl h v : A.SourceLabel m) : PauliCoordinateLabels I) =
      (v : PauliCoordinateLabels I) := rfl

/-- The inclusion of stage-`n` target labels into stage-`m` target labels. -/
noncomputable def targetIncl {n m : ℕ} (h : n ≤ m) : A.TargetLabel n →+ A.TargetLabel m :=
  (Submodule.inclusion (A.exhaustion.targetLabels_mono h)).toAddMonoidHom

@[simp] theorem targetIncl_coe {n m : ℕ} (h : n ≤ m) (u : A.TargetLabel n) :
    ((A.targetIncl h u : A.TargetLabel m) : PhaseSpace L) = (u : PhaseSpace L) := rfl

/-- **The source connecting star-algebra map**, constructed from the label
inclusion. -/
noncomputable def sourceConnecting (n m : ℕ) (h : n ≤ m) :
    pauliAlgebra (A.sourceForm n) →⋆ₐ[ℂ] pauliAlgebra (A.sourceForm m) :=
  twistHom _ _ (A.sourceIncl h) (fun _ _ => rfl)

@[simp] theorem sourceConnecting_word (n m : ℕ) (h : n ≤ m) (v : A.SourceLabel n) :
    A.sourceConnecting n m h (pauliWord (A.sourceForm n) v) =
      pauliWord (A.sourceForm m) (A.sourceIncl h v) :=
  twistHom_word _ _ _ _ v

/-- **The target connecting star-algebra map**, constructed from the label
inclusion. -/
noncomputable def targetConnecting (n m : ℕ) (h : n ≤ m) :
    pauliAlgebra (A.targetForm n) →⋆ₐ[ℂ] pauliAlgebra (A.targetForm m) :=
  twistHom _ _ (A.targetIncl h) (fun _ _ => rfl)

@[simp] theorem targetConnecting_word (n m : ℕ) (h : n ≤ m) (u : A.TargetLabel n) :
    A.targetConnecting n m h (pauliWord (A.targetForm n) u) =
      pauliWord (A.targetForm m) (A.targetIncl h u) :=
  twistHom_word _ _ _ _ u

instance sourceDirected :
    DirectedSystem (fun n => pauliAlgebra (A.sourceForm n))
      (fun n m h => A.sourceConnecting n m h) where
  map_self := by
    intro n x
    refine pauliAlgebra_linear_ext (A.sourceForm n)
      (A.sourceConnecting n n le_rfl).toAlgHom.toLinearMap LinearMap.id (fun v => ?_) x
    show A.sourceConnecting n n le_rfl (pauliWord (A.sourceForm n) v) = _
    rw [sourceConnecting_word]
    exact congrArg _ (Subtype.ext rfl)
  map_map := by
    intro k j i hij hjk x
    refine pauliAlgebra_linear_ext (A.sourceForm i)
      (((A.sourceConnecting j k hjk).comp
        (A.sourceConnecting i j hij)).toAlgHom.toLinearMap)
      (A.sourceConnecting i k (hij.trans hjk)).toAlgHom.toLinearMap (fun v => ?_) x
    show A.sourceConnecting j k hjk (A.sourceConnecting i j hij
        (pauliWord (A.sourceForm i) v)) =
      A.sourceConnecting i k (hij.trans hjk) (pauliWord (A.sourceForm i) v)
    rw [sourceConnecting_word, sourceConnecting_word, sourceConnecting_word]
    exact congrArg _ (Subtype.ext rfl)

instance targetDirected :
    DirectedSystem (fun n => pauliAlgebra (A.targetForm n))
      (fun n m h => A.targetConnecting n m h) where
  map_self := by
    intro n x
    refine pauliAlgebra_linear_ext (A.targetForm n)
      (A.targetConnecting n n le_rfl).toAlgHom.toLinearMap LinearMap.id (fun v => ?_) x
    show A.targetConnecting n n le_rfl (pauliWord (A.targetForm n) v) = _
    rw [targetConnecting_word]
    exact congrArg _ (Subtype.ext rfl)
  map_map := by
    intro k j i hij hjk x
    refine pauliAlgebra_linear_ext (A.targetForm i)
      (((A.targetConnecting j k hjk).comp
        (A.targetConnecting i j hij)).toAlgHom.toLinearMap)
      (A.targetConnecting i k (hij.trans hjk)).toAlgHom.toLinearMap (fun v => ?_) x
    show A.targetConnecting j k hjk (A.targetConnecting i j hij
        (pauliWord (A.targetForm i) v)) =
      A.targetConnecting i k (hij.trans hjk) (pauliWord (A.targetForm i) v)
    rw [targetConnecting_word, targetConnecting_word, targetConnecting_word]
    exact congrArg _ (Subtype.ext rfl)

/-! ### The finite-stage coordinate data -/

/-- **The stage-`n` finite adapted coordinate data** (the P29 interface).  Every
field is constructed from the P52 coordinates: no stage `StarAlgEquiv` is
supplied. -/
noncomputable def stage (n : ℕ) :
    FiniteAdaptedCoordinateStarData (A.Coord n) (A.SourceLabel n) (A.TargetLabel n)
      (pauliAlgebra (A.sourceForm n)) (pauliAlgebra (A.targetForm n)) where
  coordinates := A.stageCoordinates n
  source := pauliSystem (A.sourceForm n)
  target := pauliSystem (A.targetForm n)
  wordBasis := pauliWordBasis (A.sourceForm n)
  wordBasis_apply v := pauliWordBasis_apply _ v
  targetBasis := pauliWordBasis (A.targetForm n)
  targetBasis_apply u := pauliWordBasis_apply _ u
  labelMap := A.stageLabelMap n
  phase := A.phase n
  mulCompatible := A.stage_mulCompatible n
  starCompatible := A.stage_starCompatible n
  linearMap := A.stageLinear n
  linearMap_one := A.stageLinear_one n
  linearMap_word v := A.stageLinear_word n v

@[simp] theorem stage_source (n : ℕ) : (A.stage n).source = pauliSystem (A.sourceForm n) := rfl

@[simp] theorem stage_target (n : ℕ) : (A.stage n).target = pauliSystem (A.targetForm n) := rfl

@[simp] theorem stage_labelMap (n : ℕ) : (A.stage n).labelMap = A.stageLabelMap n := rfl

@[simp] theorem stage_phase (n : ℕ) : (A.stage n).phase = A.phase n := rfl

@[simp] theorem stage_coordinates (n : ℕ) : (A.stage n).coordinates = A.stageCoordinates n := rfl

/-! ### The directed family and the algebraic alpha -/

/-- **The directed family of finite coordinate systems** (the P30 interface),
assembled from the P52 local-hyperbolic data. -/
noncomputable def directedFamily : DirectedFiniteCoordinateFamily where
  Index := ℕ
  Coord := A.Coord
  SourceLabel n := A.SourceLabel n
  TargetLabel n := A.TargetLabel n
  Source n := pauliAlgebra (A.sourceForm n)
  Target n := pauliAlgebra (A.targetForm n)
  stage := A.stage
  sourceConnecting := A.sourceConnecting
  targetConnecting := A.targetConnecting
  sourceLabelIncl _ _ h v := A.sourceIncl h v
  targetLabelIncl _ _ h u := A.targetIncl h u
  sourceWord_connecting n m h v := A.sourceConnecting_word n m h v
  targetWord_connecting n m h u := A.targetConnecting_word n m h u
  labelMap_incl _ _ _ _ := Subtype.ext rfl
  phase_incl _ _ _ _ := rfl

/-! ### The algebraic limits and the global star equivalence -/

/-- The algebraic direct limit of the finite twisted Pauli algebras of the
coordinate stages: the algebraic `𝒫_I` of the manuscript. -/
abbrev SourceLimit : Type _ := A.directedFamily.SourceLimit

/-- The algebraic direct limit of the finite twisted Pauli algebras of the
regions: the algebraic `𝒜_Γ` of the manuscript. -/
abbrev TargetLimit : Type _ := A.directedFamily.TargetLimit

/-- The canonical map of a source stage into the source limit. -/
noncomputable abbrev sourceOf (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) : A.SourceLimit :=
  A.directedFamily.sourceOf n x

/-- The canonical map of a target stage into the target limit. -/
noncomputable abbrev targetOf (n : ℕ) (y : pauliAlgebra (A.targetForm n)) : A.TargetLimit :=
  A.directedFamily.targetOf n y

/-- **The algebraic `alpha` of the local-hyperbolic coordinates.**  It is
constructed, not assumed: the finite-stage star equivalences come from the P52
coordinate data through P29, their commuting squares are the P30 theorem, and
the limit equivalence is the P23/P31 construction. -/
noncomputable def alpha : A.SourceLimit ≃⋆ₐ[ℂ] A.TargetLimit :=
  A.directedFamily.alpha

/-- **The Pauli-word formula for `alpha`.**  On the image of a stage-`n` Pauli
word, `alpha` is the phase-corrected Pauli word of the image label. -/
theorem alpha_word (n : ℕ) (v : A.SourceLabel n) :
    A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) v)) =
      A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v)) :=
  A.directedFamily.alpha_word n v

/-- The calibration phase is a fourth root of unity, in particular nonzero. -/
theorem phase_ne_zero (n : ℕ) (v : A.SourceLabel n) : A.phase n v ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

/-- **The manuscript's `α(Z_i) = P(z_i)`, phase-calibrated.**  On the Pauli word
of the `Z` coordinate of a stage-`n` site, `alpha` is a fourth-root-of-unity
multiple of the regional Pauli word of the hyperbolic vector `z i`. -/
theorem alpha_zWord (n : ℕ) (i : A.Coord n) (u : A.TargetLabel n)
    (hu : (u : PhaseSpace L) = A.family.z (i : I)) :
    A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) ((A.stageCoordinates n).z i))) =
      A.targetOf n (A.phase n ((A.stageCoordinates n).z i) •
        pauliWord (A.targetForm n) u) := by
  rw [A.alpha_word n ((A.stageCoordinates n).z i),
    show A.stageLabelMap n ((A.stageCoordinates n).z i) = u from
      Subtype.ext ((A.stageLabelMap_z n i).trans hu.symm)]

/-- **The manuscript's `α(X_i) = P(x_i)`, phase-calibrated.** -/
theorem alpha_xWord (n : ℕ) (i : A.Coord n) (u : A.TargetLabel n)
    (hu : (u : PhaseSpace L) = A.family.x (i : I)) :
    A.alpha (A.sourceOf n (pauliWord (A.sourceForm n) ((A.stageCoordinates n).x i))) =
      A.targetOf n (A.phase n ((A.stageCoordinates n).x i) •
        pauliWord (A.targetForm n) u) := by
  rw [A.alpha_word n ((A.stageCoordinates n).x i),
    show A.stageLabelMap n ((A.stageCoordinates n).x i) = u from
      Subtype.ext ((A.stageLabelMap_x n i).trans hu.symm)]

/-- The inverse of `alpha` recovers each source Pauli word from the regional
Pauli word of its image label. -/
theorem alpha_symm_word (n : ℕ) (v : A.SourceLabel n) :
    A.alpha.symm (A.targetOf n (pauliWord (A.targetForm n) (A.stageLabelMap n v))) =
      (A.phase n v)⁻¹ • A.sourceOf n (pauliWord (A.sourceForm n) v) :=
  A.directedFamily.alpha_symm_targetWord n v (A.phase_ne_zero n v)

/-- **Existence and uniqueness of the algebraic `alpha`.**  There is exactly one
star-algebra equivalence of the two algebraic direct limits obeying the
phase-calibrated Pauli-word formula at every stage. -/
theorem existsUnique_alpha :
    ∃! psi : A.SourceLimit ≃⋆ₐ[ℂ] A.TargetLimit,
      ∀ (n : ℕ) (v : A.SourceLabel n),
        psi (A.sourceOf n (pauliWord (A.sourceForm n) v)) =
          A.targetOf n (A.phase n v • pauliWord (A.targetForm n) (A.stageLabelMap n v)) :=
  A.directedFamily.existsUnique_alpha

end AlphaData

end Data

/-! ## A witness: the assumptions of `AlphaData` are consistent -/

/-- The tautological local-hyperbolic family on a lattice: the hyperbolic pair
of a site is the pair of its own `Z` and `X` coordinates. -/
noncomputable def standardFamily (L : Type*) : LocalHyperbolicFamily L L where
  z i := Finsupp.single (Sum.inl i) 1
  x i := Finsupp.single (Sum.inr i) 1
  indep := by
    have h : (Sum.elim (fun i : L => Finsupp.single (Sum.inl i) (1 : PauliBit))
        (fun i : L => Finsupp.single (Sum.inr i) (1 : PauliBit)))
        = fun p : L ⊕ L => Finsupp.single p (1 : PauliBit) := by
      funext p; rcases p with p | p <;> rfl
    rw [h]
    simpa using
      (Finsupp.basisSingleOne (ι := L ⊕ L) (R := PauliBit)).linearIndependent
  selected := Set.univ

@[simp] theorem standardFamily_z (L : Type*) (i : L) :
    (standardFamily L).z i = Finsupp.single (Sum.inl i) 1 := rfl

@[simp] theorem standardFamily_x (L : Type*) (i : L) :
    (standardFamily L).x i = Finsupp.single (Sum.inr i) 1 := rfl

theorem standardFamily_coordinateMap (L : Type*) (v : PauliCoordinateLabels L) :
    (standardFamily L).coordinateMap v = v := by
  rw [LocalHyperbolicFamily.coordinateMap, Finsupp.linearCombination_apply]
  rw [show (Sum.elim (standardFamily L).z (standardFamily L).x)
      = fun p : L ⊕ L => Finsupp.single p (1 : PauliBit) from by
    funext p; rcases p with p | p <;> rfl]
  rw [show (v.sum fun p a => a • Finsupp.single p (1 : PauliBit))
      = v.sum fun p a => Finsupp.single p a from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [Finsupp.smul_single]]
  exact Finsupp.sum_single v

theorem standardFamily_coordinateBlock (L : Type*) (E : LatticeExhaustion L) (n : ℕ) :
    (standardFamily L).coordinateBlock E n = (E.region n : Set L) := by
  ext i
  constructor
  · rintro ⟨hz, -⟩
    exact (mem_supportedOn_iff _ _).mp hz (Sum.inl i) (by simp)
  · intro hi
    refine ⟨(mem_supportedOn_iff _ _).mpr ?_, (mem_supportedOn_iff _ _).mpr ?_⟩ <;>
      · intro p hp
        simp only [standardFamily_z, standardFamily_x,
          Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hp
        subst hp
        exact hi

/-- The tautological exhaustion of `ℕ` by initial segments. -/
def standardExhaustion : LatticeExhaustion ℕ where
  region n := Finset.range n
  mono := by
    intro a b h x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  covers a := ⟨a + 1, Finset.self_mem_range_succ a⟩

/-- **Non-vacuity.**  The auxiliary assumptions of `AlphaData` are consistent:
the tautological coordinates on the lattice `ℕ` satisfy them. -/
noncomputable def standardAlphaData : AlphaData ℕ ℕ where
  family := standardFamily ℕ
  exhaustion := standardExhaustion
  symplectic v w := by
    rw [standardFamily_coordinateMap, standardFamily_coordinateMap]
  stage_surjective n u hu := by
    refine ⟨u, ?_, standardFamily_coordinateMap ℕ u⟩
    rw [LocalHyperbolicFamily.mem_sourceLabels_iff]
    intro p hp
    rw [standardFamily_coordinateBlock]
    exact (mem_supportedOn_iff _ _).mp hu p hp

end LocalHyperbolicAlpha

end StabilizerHyperfinite
