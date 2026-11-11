import AristotleCandidates.AlgebraicLimitOperatorRepresentation
import AristotleCandidates.ConcreteCStarCompletion

/-!
# A concrete quasilocal C⋆-model from the algebraic limit representation

**Context declaration.** Source basis: `main.tex:1915-1924` (the
quasilocal algebra obtained from the algebraic local limit together with a
representation of it).  Everything below is *conditional* on explicitly
supplied data; no infinite tensor-product Hilbert space is constructed here.

This module combines

* the compatible algebraic-limit operator representation
  `StabilizerHyperfinite.algebraicLimitOperatorRep` (a star-algebra
  homomorphism `DirectLimit A f →⋆ₐ[ℂ] (H →L[ℂ] H)` induced by a compatible
  family of finite-stage representations `rho i : A i →⋆ₐ[ℂ] (H →L[ℂ] H)`),
  with
* the checked *closed operator-range* construction of
  `Formalization.ConcreteCStarCompletion` (the topological closure of the range
  of a star-algebra homomorphism inside the bounded operators of a Hilbert
  space, which is a genuine C⋆-algebra).

The result is a **concrete** quasilocal C⋆-algebra

`quasilocalCStarAlgebra rho compat = ((algebraicLimitOperatorRep rho compat).range).topologicalClosure`,

a closed star-subalgebra of `H →L[ℂ] H`, together with a canonical star-algebra
homomorphism from the algebraic limit into it which

* has **dense range** (`denseRange_quasilocalEmbedding`);
* satisfies the **finite-stage formula**
  `quasilocalEmbedding rho compat (of i x) = rho i x`
  (`coe_quasilocalEmbedding_of`);
* is **injective (faithful)** as soon as every stage representation is
  injective (`injective_quasilocalEmbedding`);
* realizes the concrete algebra as the closure of the union of the finite-stage
  operator ranges (`coe_quasilocalCStarAlgebra_eq_closure_iUnion`) — the precise
  quasilocality statement;
* is **minimal**: the concrete algebra is the least closed star-subalgebra of
  `H →L[ℂ] H` containing all finite-stage operator ranges
  (`quasilocalCStarAlgebra_isLeast`).

## Exact hypotheses

Two packages of assumptions are used, both explicit:

* `rho`, `compat`: a supplied Hilbert space `H`, supplied stage representations
  `rho i : A i →⋆ₐ[ℂ] (H →L[ℂ] H)` and the compatibility
  `rho j (f i j h x) = rho i x` with the connecting maps.  Faithfulness of the
  limit representation is then *conditional* on `∀ i, Function.Injective (rho i)`.
* `IsometricStageRepresentation`: the same data for *normed* stage algebras,
  with the additional field `norm_rho : ∀ i a, ‖rho i a‖ = ‖a‖`.  This is the
  "explicitly faithful isometric representation" input: isometry of each stage
  representation implies injectivity of each stage representation, hence
  faithfulness of the induced limit representation, and it yields the
  finite-stage *norm* formula `‖embedding (of i x)‖ = ‖x‖`.

## What is *not* claimed

No infinite tensor-product Hilbert space, no regional C⋆-isomorphism, no GNS
factorization, no normality, no bicommutant or factor classification, and no
statement that the concrete algebra is a UHF algebra.
-/

namespace StabilizerHyperfinite
namespace ConcreteQuasilocalCStarModel

open Formalization.ConcreteCStarCompletion

/-! ## The concrete quasilocal C⋆-algebra of a compatible stage representation -/

section General

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)

/-- The **concrete quasilocal C⋆-algebra**: the closure, inside the bounded
operators on the supplied Hilbert space `H`, of the operator range of the
induced algebraic-limit representation. -/
noncomputable def quasilocalCStarAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (algebraicLimitOperatorRep rho compat).range.topologicalClosure

instance isClosed_quasilocalCStarAlgebra :
    IsClosed ((quasilocalCStarAlgebra rho compat :
      StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

/-- The concrete quasilocal algebra is a genuine C⋆-algebra: it is a closed
star-subalgebra of the C⋆-algebra of bounded operators on `H`. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (quasilocalCStarAlgebra rho compat) :=
  StarSubalgebra.cstarAlgebra _

theorem limitRep_mem_quasilocalCStarAlgebra (z : DirectLimit A f) :
    algebraicLimitOperatorRep rho compat z ∈ quasilocalCStarAlgebra rho compat :=
  (algebraicLimitOperatorRep rho compat).range.le_topologicalClosure ⟨z, rfl⟩

theorem rho_mem_quasilocalCStarAlgebra (i : ι) (x : A i) :
    rho i x ∈ quasilocalCStarAlgebra rho compat := by
  have := limitRep_mem_quasilocalCStarAlgebra rho compat
    (DirectLimit.Module.of ℂ ι A f i x)
  rwa [algebraicLimitOperatorRep_of] at this

/-- The canonical star-algebra homomorphism from the *algebraic* quasilocal
limit into its concrete closed C⋆-range. -/
noncomputable def quasilocalEmbedding :
    DirectLimit A f →⋆ₐ[ℂ] quasilocalCStarAlgebra rho compat :=
  (algebraicLimitOperatorRep rho compat).codRestrict _
    (limitRep_mem_quasilocalCStarAlgebra rho compat)

@[simp] theorem coe_quasilocalEmbedding (z : DirectLimit A f) :
    (quasilocalEmbedding rho compat z : H →L[ℂ] H) =
      algebraicLimitOperatorRep rho compat z := rfl

/-- **Finite-stage formula.**  On the image of a stage `i`, the canonical
embedding into the concrete quasilocal C⋆-algebra is the supplied stage
representation. -/
@[simp] theorem coe_quasilocalEmbedding_of (i : ι) (x : A i) :
    (quasilocalEmbedding rho compat (DirectLimit.Module.of ℂ ι A f i x) :
      H →L[ℂ] H) = rho i x := by
  rw [coe_quasilocalEmbedding, algebraicLimitOperatorRep_of]

/-- Finite-stage formula, evaluated on a vector of the Hilbert space. -/
theorem quasilocalEmbedding_of_apply (i : ι) (x : A i) (v : H) :
    (quasilocalEmbedding rho compat (DirectLimit.Module.of ℂ ι A f i x) :
      H →L[ℂ] H) v = rho i x v := by
  rw [coe_quasilocalEmbedding_of]

/-- The operator range of the induced limit representation is exactly the union
of the finite-stage operator ranges. -/
theorem range_algebraicLimitOperatorRep :
    Set.range (algebraicLimitOperatorRep rho compat) = ⋃ i, Set.range (rho i) := by
  ext T
  constructor
  · rintro ⟨z, rfl⟩
    induction z using DirectLimit.induction with
    | _ i x =>
      refine Set.mem_iUnion.2 ⟨i, x, ?_⟩
      have h : (⟦⟨i, x⟩⟧ : DirectLimit A f) =
          DirectLimit.Module.of ℂ ι A f i x := rfl
      rw [h, algebraicLimitOperatorRep_of]
  · intro hT
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hT
    exact ⟨DirectLimit.Module.of ℂ ι A f i x, algebraicLimitOperatorRep_of rho compat i x⟩

/-- **Quasilocality.**  The concrete algebra is the closure of the union of the
finite-stage operator ranges. -/
theorem coe_quasilocalCStarAlgebra_eq_closure_iUnion :
    ((quasilocalCStarAlgebra rho compat : StarSubalgebra ℂ (H →L[ℂ] H)) :
      Set (H →L[ℂ] H)) = closure (⋃ i, Set.range (rho i)) := by
  rw [quasilocalCStarAlgebra, StarSubalgebra.topologicalClosure_coe,
    ← range_algebraicLimitOperatorRep rho compat]
  rfl

/-- **Dense embedding.**  The image of the algebraic quasilocal limit is dense
in the concrete quasilocal C⋆-algebra. -/
theorem denseRange_quasilocalEmbedding : DenseRange (quasilocalEmbedding rho compat) := by
  have hcoe : ((quasilocalCStarAlgebra rho compat : StarSubalgebra ℂ (H →L[ℂ] H)) :
      Set (H →L[ℂ] H)) = closure (Set.range ⇑(algebraicLimitOperatorRep rho compat)) := by
    rw [quasilocalCStarAlgebra, StarSubalgebra.topologicalClosure_coe]
    rfl
  rw [DenseRange, Subtype.dense_iff]
  intro T hT
  rw [hcoe] at hT
  refine closure_mono ?_ hT
  rintro _ ⟨z, rfl⟩
  exact ⟨quasilocalEmbedding rho compat z, ⟨z, rfl⟩, rfl⟩

/-- The finite-stage images are dense in the concrete quasilocal C⋆-algebra. -/
theorem denseRange_stage_images :
    Dense {T : quasilocalCStarAlgebra rho compat |
      ∃ (i : ι) (x : A i), (T : H →L[ℂ] H) = rho i x} := by
  refine (denseRange_quasilocalEmbedding rho compat).mono ?_
  rintro _ ⟨z, rfl⟩
  induction z using DirectLimit.induction with
  | _ i x =>
    refine ⟨i, x, ?_⟩
    have h : (⟦⟨i, x⟩⟧ : DirectLimit A f) =
        DirectLimit.Module.of ℂ ι A f i x := rfl
    rw [h, coe_quasilocalEmbedding_of]

/-- **Conditional faithfulness.**  If every supplied stage representation is
injective, the canonical embedding of the algebraic quasilocal limit into the
concrete C⋆-algebra is injective. -/
theorem injective_quasilocalEmbedding (h_inj : ∀ i, Function.Injective (rho i)) :
    Function.Injective (quasilocalEmbedding rho compat) := by
  intro z w hzw
  refine algebraicLimitOperatorRep_injective rho compat h_inj ?_
  simpa using congrArg (fun T : quasilocalCStarAlgebra rho compat => (T : H →L[ℂ] H)) hzw

/-- Minimality: the concrete quasilocal algebra is contained in every closed
star-subalgebra of `H →L[ℂ] H` containing all finite-stage operator ranges. -/
theorem quasilocalCStarAlgebra_le {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : IsClosed (S : Set (H →L[ℂ] H))) (hrange : ∀ i x, rho i x ∈ S) :
    quasilocalCStarAlgebra rho compat ≤ S := by
  have key : ∀ z : DirectLimit A f, algebraicLimitOperatorRep rho compat z ∈ S := by
    intro z
    induction z using DirectLimit.induction with
    | _ i x =>
      have h : (⟦⟨i, x⟩⟧ : DirectLimit A f) =
          DirectLimit.Module.of ℂ ι A f i x := rfl
      rw [h, algebraicLimitOperatorRep_of]
      exact hrange i x
  refine StarSubalgebra.topologicalClosure_minimal ?_ hS
  rintro _ ⟨z, rfl⟩
  exact key z

/-- The concrete quasilocal algebra is the *least* closed star-subalgebra of the
bounded operators containing all finite-stage operator ranges. -/
theorem quasilocalCStarAlgebra_isLeast :
    IsLeast {S : StarSubalgebra ℂ (H →L[ℂ] H) |
        IsClosed (S : Set (H →L[ℂ] H)) ∧ ∀ i x, rho i x ∈ S}
      (quasilocalCStarAlgebra rho compat) :=
  ⟨⟨isClosed_quasilocalCStarAlgebra rho compat, rho_mem_quasilocalCStarAlgebra rho compat⟩,
    fun _ hS => quasilocalCStarAlgebra_le rho compat hS.1 hS.2⟩

/-- The C⋆-identity, transported to the algebraic limit through the concrete
model: the operator norm of a limit element satisfies `‖z⋆z‖ = ‖z‖²`. -/
theorem norm_star_mul_self_limitRep (z : DirectLimit A f) :
    ‖algebraicLimitOperatorRep rho compat (star z * z)‖ =
      ‖algebraicLimitOperatorRep rho compat z‖ ^ 2 := by
  rw [map_mul, map_star, CStarRing.norm_star_mul_self, sq]

end General

/-! ## Explicitly faithful isometric stage representations -/

section Isometric

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]

/-- An **explicitly faithful isometric representation** of the algebraic
quasilocal limit: a supplied Hilbert space `H`, supplied finite-stage
representations, their compatibility with the connecting maps of the directed
system, and the supplied hypothesis that every stage representation is norm
preserving.  All three are fields, so every conclusion below is explicitly
conditional on them. -/
structure IsometricStageRepresentation (A : ι → Type*)
    [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
    (f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The supplied representation of the stage algebra `A i`. -/
  rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- Compatibility with the connecting maps of the directed system. -/
  compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x
  /-- The supplied isometry hypothesis: each stage representation is norm
  preserving. -/
  norm_rho : ∀ i a, ‖rho i a‖ = ‖a‖

namespace IsometricStageRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : IsometricStageRepresentation A f H)

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
/-- Each stage representation is an isometry. -/
theorem isometry_rho (i : ι) : Isometry (R.rho i) :=
  AddMonoidHomClass.isometry_of_norm _ (R.norm_rho i)

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
/-- Each stage representation is injective. -/
theorem injective_rho (i : ι) : Function.Injective (R.rho i) :=
  (R.isometry_rho i).injective

/-- The concrete quasilocal C⋆-algebra attached to an isometric stage
representation. -/
noncomputable def cstarAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  quasilocalCStarAlgebra R.rho R.compat

/-- The canonical embedding of the algebraic quasilocal limit into the concrete
C⋆-algebra. -/
noncomputable def embedding : DirectLimit A f →⋆ₐ[ℂ] R.cstarAlgebra :=
  quasilocalEmbedding R.rho R.compat

@[simp] theorem coe_embedding (z : DirectLimit A f) :
    (R.embedding z : H →L[ℂ] H) = algebraicLimitOperatorRep R.rho R.compat z := rfl

/-- Finite-stage formula for the concrete embedding. -/
@[simp] theorem coe_embedding_of (i : ι) (x : A i) :
    (R.embedding (DirectLimit.Module.of ℂ ι A f i x) : H →L[ℂ] H) = R.rho i x :=
  coe_quasilocalEmbedding_of R.rho R.compat i x

/-- **Finite-stage norm formula.**  The concrete embedding restricted to a stage
is isometric for the supplied stage norm. -/
theorem norm_embedding_of (i : ι) (x : A i) :
    ‖R.embedding (DirectLimit.Module.of ℂ ι A f i x)‖ = ‖x‖ := by
  have h : ‖R.embedding (DirectLimit.Module.of ℂ ι A f i x)‖ =
      ‖(R.embedding (DirectLimit.Module.of ℂ ι A f i x) : H →L[ℂ] H)‖ := rfl
  rw [h, coe_embedding_of, R.norm_rho]

/-- **Faithfulness.**  An isometric family of stage representations induces an
injective (faithful) embedding of the algebraic quasilocal limit into the
concrete C⋆-algebra. -/
theorem injective_embedding : Function.Injective R.embedding :=
  injective_quasilocalEmbedding R.rho R.compat R.injective_rho

/-- **Dense embedding.** -/
theorem denseRange_embedding : DenseRange R.embedding :=
  denseRange_quasilocalEmbedding R.rho R.compat

/-- The concrete C⋆-algebra is the closure of the union of the finite-stage
operator ranges. -/
theorem coe_cstarAlgebra_eq_closure_iUnion :
    ((R.cstarAlgebra : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      closure (⋃ i, Set.range (R.rho i)) :=
  coe_quasilocalCStarAlgebra_eq_closure_iUnion R.rho R.compat

/-- Minimality of the concrete C⋆-algebra. -/
theorem cstarAlgebra_isLeast :
    IsLeast {S : StarSubalgebra ℂ (H →L[ℂ] H) |
        IsClosed (S : Set (H →L[ℂ] H)) ∧ ∀ i x, R.rho i x ∈ S} R.cstarAlgebra :=
  quasilocalCStarAlgebra_isLeast R.rho R.compat

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
include R in
/-- The connecting maps of the directed system are isometric, hence in
particular injective, as soon as the stage representations are. -/
theorem norm_map_connecting (i j : ι) (h : i ≤ j) (x : A i) : ‖f i j h x‖ = ‖x‖ := by
  rw [← R.norm_rho j, R.compat i j h x, R.norm_rho i]

end IsometricStageRepresentation

end Isometric

/-! ## Non-vacuity of the hypotheses -/

section NonVacuity

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The constant directed system all of whose stages are the bounded operators on `H`. -/
abbrev constStage : ℕ → Type _ := fun _ => H →L[ℂ] H

/-- The identity connecting maps of the constant directed system. -/
noncomputable def constConnecting :
    ∀ i j : ℕ, i ≤ j → constStage H i →⋆ₐ[ℂ] constStage H j :=
  fun _ _ _ => StarAlgHom.id ℂ (H →L[ℂ] H)

noncomputable instance : DirectedSystem (constStage H) (constConnecting H · · ·) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The hypotheses of `IsometricStageRepresentation` are satisfiable: the identity
representation of the constant system of bounded operators on `H` is an explicitly
faithful isometric stage representation. -/
noncomputable def idIsometricStageRepresentation :
    IsometricStageRepresentation (constStage H) (constConnecting H) H where
  rho _ := StarAlgHom.id ℂ (H →L[ℂ] H)
  compat _ _ _ _ := rfl
  norm_rho _ _ := rfl

end NonVacuity

/-! ## The dyadic specialization -/

section Dyadic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : QubitOperatorRepresentationData H)

/-- The concrete quasilocal C⋆-algebra attached to a compatible family of
finite-qubit-stage representations: the closed operator range of the induced
representation of the algebraic UHF limit `QubitUHFAlgebra`.

Both the Hilbert space and the stage representations are supplied input; no
infinite tensor-product Hilbert space is constructed. -/
noncomputable def qubitQuasilocalCStarAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  quasilocalCStarAlgebra D.rho D.compat

/-- The canonical embedding of the algebraic UHF limit into its concrete
quasilocal C⋆-algebra. -/
noncomputable def qubitQuasilocalEmbedding :
    QubitUHFAlgebra →⋆ₐ[ℂ] qubitQuasilocalCStarAlgebra D :=
  quasilocalEmbedding D.rho D.compat

/-- Finite-stage formula for the dyadic concrete embedding. -/
@[simp] theorem coe_qubitQuasilocalEmbedding_of (n : ℕ) (x : QubitTensorPower n) :
    (qubitQuasilocalEmbedding D
        (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) :
      H →L[ℂ] H) = D.rho n x :=
  coe_quasilocalEmbedding_of D.rho D.compat n x

/-- Finite-stage formula for the dyadic concrete embedding, applied to a
vector. -/
theorem qubitQuasilocalEmbedding_of_apply (n : ℕ) (x : QubitTensorPower n) (v : H) :
    (qubitQuasilocalEmbedding D
        (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) :
      H →L[ℂ] H) v = D.rho n x v :=
  quasilocalEmbedding_of_apply D.rho D.compat n x v

/-- **Dense embedding** of the algebraic UHF limit in the dyadic concrete
quasilocal C⋆-algebra. -/
theorem denseRange_qubitQuasilocalEmbedding :
    DenseRange (qubitQuasilocalEmbedding D) :=
  denseRange_quasilocalEmbedding D.rho D.compat

/-- **Conditional faithfulness** for the dyadic model: if every supplied
finite-qubit-stage representation is injective, the concrete embedding is
injective. -/
theorem injective_qubitQuasilocalEmbedding (h_inj : ∀ n, Function.Injective (D.rho n)) :
    Function.Injective (qubitQuasilocalEmbedding D) :=
  injective_quasilocalEmbedding D.rho D.compat h_inj

/-- The dyadic concrete algebra is the closure of the union of the
finite-qubit-stage operator ranges. -/
theorem coe_qubitQuasilocalCStarAlgebra_eq_closure_iUnion :
    ((qubitQuasilocalCStarAlgebra D : StarSubalgebra ℂ (H →L[ℂ] H)) :
      Set (H →L[ℂ] H)) = closure (⋃ n : ℕ, Set.range (D.rho n)) :=
  coe_quasilocalCStarAlgebra_eq_closure_iUnion D.rho D.compat

/-- Minimality of the dyadic concrete algebra. -/
theorem qubitQuasilocalCStarAlgebra_isLeast :
    IsLeast {S : StarSubalgebra ℂ (H →L[ℂ] H) |
        IsClosed (S : Set (H →L[ℂ] H)) ∧ ∀ n x, D.rho n x ∈ S}
      (qubitQuasilocalCStarAlgebra D) :=
  quasilocalCStarAlgebra_isLeast D.rho D.compat

end Dyadic

end ConcreteQuasilocalCStarModel
end StabilizerHyperfinite
