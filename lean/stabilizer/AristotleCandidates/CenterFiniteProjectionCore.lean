import Mathlib.Analysis.VonNeumannAlgebra.Basic
import AristotleCandidates.BicommutantVonNeumannCore

/-!
# Center, projections, corners, central support and fullness

This file develops, for Mathlib's *concrete* von Neumann algebras
`M : VonNeumannAlgebra H` (star subalgebras of `H →L[ℂ] H` equal to their own double
commutant), the algebraic vocabulary of Murray--von Neumann comparison theory:

* `VonNeumannAlgebra.center` — the center `M ∩ M'`, again a concrete von Neumann algebra;
* `VonNeumannAlgebra.IsProjection`, `VonNeumannAlgebra.IsCentralProjection` — (central)
  star projections belonging to `M` (Mathlib's `IsStarProjection` is reused);
* `VonNeumannAlgebra.ProjLe` — the order `p ≤ q` on projections, written algebraically as
  `p * q = p ∧ q * p = p`;
* `VonNeumannAlgebra.MvNEquiv`, `VonNeumannAlgebra.MvNLe` — Murray--von Neumann equivalence
  and subequivalence of projections implemented by a partial isometry in `M`;
* `VonNeumannAlgebra.IsFiniteProjection` — a projection with no proper equivalent
  subprojection;
* `VonNeumannAlgebra.corner` — the compressed algebra `p M p`, as a non-unital star
  subalgebra of `H →L[ℂ] H`;
* `VonNeumannAlgebra.IsCentralSupport` and `VonNeumannAlgebra.IsFull` — the central support
  of a projection (as a *predicate*, so that no completeness of the projection lattice is
  needed) and fullness, i.e. central support `1`.

The main "central intersection" statement proved here is
`VonNeumannAlgebra.IsFull.mul_ne_zero`: a full projection meets every nonzero central
projection nontrivially, together with its converse
`VonNeumannAlgebra.isFull_iff_forall_central`.

The main comparison lemmas are `VonNeumannAlgebra.MvNEquiv.add` (orthogonal sums of
equivalences), `VonNeumannAlgebra.MvNLe.trans` (transitivity of subequivalence, via
`VonNeumannAlgebra.conj_isProjection_of_projLe`) and the compression lemma
`VonNeumannAlgebra.IsFiniteProjection.mul_central` (a central compression of a finite
projection is finite).

## Scope: algebra versus analysis

Everything in this file is **algebraic**.  No operator topology, no normality, no
semifiniteness, and no classification of factors is used or asserted.  The only place where
a genuinely *metric* fact about `H →L[ℂ] H` enters is
`VonNeumannAlgebra.mul_star_mul_self_eq_self` (and the results depending on it, namely that
the right endpoint of a Murray--von Neumann equivalence is again a projection, orthogonal
additivity of equivalences, and the transitivity of `MvNLe`), which uses the C*-identity
through
`CStarRing.star_mul_self_eq_zero_iff : star x * x = 0 ↔ x = 0`.  That is a norm identity
available in the pinned Mathlib for `H →L[ℂ] H`; it is *not* an operator-topology or a
von Neumann density statement.

In particular this file contains **no** projection tower, no corner trace, no weight, and no
type classification; those belong to later developments.
-/

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumannAlgebra

/-! ### The center of a concrete von Neumann algebra -/

/-- The center `M ∩ M'` of a concrete von Neumann algebra, again a concrete von Neumann
algebra.  It is realised as the commutant of `M ∪ M'`, which makes the double-commutant
condition automatic. -/
noncomputable def center (M : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ ((M : Set (H →L[ℂ] H)) ∪ (M.commutant : Set (H →L[ℂ] H)))
  centralizer_centralizer' := by
    have h : ((StarSubalgebra.centralizer ℂ
          ((M : Set (H →L[ℂ] H)) ∪ (M.commutant : Set (H →L[ℂ] H))) :
            StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
        Set.centralizer ((M : Set (H →L[ℂ] H)) ∪ (M.commutant : Set (H →L[ℂ] H))) := by
      rw [StarSubalgebra.coe_centralizer, Set.union_star, StarMemClass.star_coe_eq,
        StarMemClass.star_coe_eq, Set.union_self]
    show Set.centralizer (Set.centralizer
        ((StarSubalgebra.centralizer ℂ
          ((M : Set (H →L[ℂ] H)) ∪ (M.commutant : Set (H →L[ℂ] H))) :
            StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) = _
    rw [h, Set.centralizer_centralizer_centralizer]
    exact h.symm

@[simp]
theorem coe_center (M : VonNeumannAlgebra H) :
    (M.center : Set (H →L[ℂ] H)) =
      (M : Set (H →L[ℂ] H)) ∩ Set.centralizer (M : Set (H →L[ℂ] H)) := by
  show ((StarSubalgebra.centralizer ℂ
      ((M : Set (H →L[ℂ] H)) ∪ (M.commutant : Set (H →L[ℂ] H))) :
        StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = _
  rw [StarSubalgebra.coe_centralizer, Set.union_star, StarMemClass.star_coe_eq,
    StarMemClass.star_coe_eq, Set.union_self, Set.centralizer_union, coe_commutant,
    M.centralizer_centralizer, Set.inter_comm]

theorem mem_center_iff {M : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ M.center ↔ x ∈ M ∧ ∀ y ∈ M, y * x = x * y := by
  rw [← SetLike.mem_coe, coe_center]
  exact Iff.rfl

theorem mem_of_mem_center {M : VonNeumannAlgebra H} {x : H →L[ℂ] H} (hx : x ∈ M.center) :
    x ∈ M := (mem_center_iff.mp hx).1

theorem center_commute {M : VonNeumannAlgebra H} {x y : H →L[ℂ] H} (hx : x ∈ M.center)
    (hy : y ∈ M) : Commute x y :=
  ((mem_center_iff.mp hx).2 y hy).symm

theorem center_le (M : VonNeumannAlgebra H) :
    (M.center : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H)) := fun _ hx => mem_of_mem_center hx

theorem center_le_commutant (M : VonNeumannAlgebra H) :
    (M.center : Set (H →L[ℂ] H)) ⊆ (M.commutant : Set (H →L[ℂ] H)) := by
  rw [coe_center, coe_commutant]
  exact Set.inter_subset_right

/-- The center of `M` is the center of its commutant. -/
theorem center_commutant (M : VonNeumannAlgebra H) : M.commutant.center = M.center := by
  refine SetLike.coe_injective ?_
  rw [coe_center, coe_center, coe_commutant, M.centralizer_centralizer, Set.inter_comm]

/-! ### Projections and central projections -/

/-- A *projection of `M`* is a self-adjoint idempotent belonging to `M`. -/
def IsProjection (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ M

/-- A *central projection* of `M` is a projection lying in the center of `M`. -/
def IsCentralProjection (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  IsStarProjection z ∧ z ∈ M.center

namespace IsProjection

variable {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H}

theorem isStarProjection (hp : M.IsProjection p) : IsStarProjection p := hp.1

theorem mem (hp : M.IsProjection p) : p ∈ M := hp.2

theorem mul_self (hp : M.IsProjection p) : p * p = p := hp.1.isIdempotentElem

theorem star_eq (hp : M.IsProjection p) : star p = p := hp.1.isSelfAdjoint.star_eq

theorem one_sub (hp : M.IsProjection p) : M.IsProjection (1 - p) :=
  ⟨hp.1.one_sub, sub_mem (one_mem M) hp.2⟩

end IsProjection

theorem isProjection_zero (M : VonNeumannAlgebra H) : M.IsProjection 0 :=
  ⟨IsStarProjection.zero _, zero_mem M⟩

theorem isProjection_one (M : VonNeumannAlgebra H) : M.IsProjection 1 :=
  ⟨IsStarProjection.one _, one_mem M⟩

namespace IsCentralProjection

variable {M : VonNeumannAlgebra H} {z w : H →L[ℂ] H}

theorem isStarProjection (hz : M.IsCentralProjection z) : IsStarProjection z := hz.1

theorem mem_center (hz : M.IsCentralProjection z) : z ∈ M.center := hz.2

/-- A central projection is in particular a projection of `M`. -/
theorem isProjection (hz : M.IsCentralProjection z) : M.IsProjection z :=
  ⟨hz.1, mem_of_mem_center hz.2⟩

theorem commute (hz : M.IsCentralProjection z) {x : H →L[ℂ] H} (hx : x ∈ M) : z * x = x * z :=
  (center_commute hz.2 hx).eq

theorem one_sub (hz : M.IsCentralProjection z) : M.IsCentralProjection (1 - z) := by
  refine ⟨hz.1.one_sub, mem_center_iff.mpr ⟨sub_mem (one_mem M) (mem_of_mem_center hz.2), ?_⟩⟩
  intro y hy
  simp [sub_mul, mul_sub, hz.commute hy]

theorem mul (hz : M.IsCentralProjection z) (hw : M.IsCentralProjection w) :
    M.IsCentralProjection (z * w) := by
  have hcomm : Commute z w := center_commute hz.2 (mem_of_mem_center hw.2)
  refine ⟨hz.1.mul hw.1 hcomm, mem_center_iff.mpr
    ⟨mul_mem (mem_of_mem_center hz.2) (mem_of_mem_center hw.2), fun y hy => ?_⟩⟩
  rw [← mul_assoc, ← hz.commute hy, mul_assoc, ← hw.commute hy, ← mul_assoc]

end IsCentralProjection

theorem isCentralProjection_zero (M : VonNeumannAlgebra H) : M.IsCentralProjection 0 :=
  ⟨IsStarProjection.zero _, zero_mem M.center⟩

theorem isCentralProjection_one (M : VonNeumannAlgebra H) : M.IsCentralProjection 1 :=
  ⟨IsStarProjection.one _, one_mem M.center⟩

/-! ### The order on projections -/

section Order

omit [CompleteSpace H]

/-- The usual order on projections, written purely algebraically: `p ≤ q` means that `q` acts
as the identity on the range of `p`.  For star projections the two equations are equivalent,
see `VonNeumannAlgebra.projLe_of_mul_eq_left`. -/
def ProjLe (p q : H →L[ℂ] H) : Prop := p * q = p ∧ q * p = p

namespace ProjLe

variable {p q r : H →L[ℂ] H}

theorem mul_right (h : ProjLe p q) : p * q = p := h.1

theorem mul_left (h : ProjLe p q) : q * p = p := h.2

theorem refl (hp : IsIdempotentElem p) : ProjLe p p := ⟨hp, hp⟩

theorem trans (hpq : ProjLe p q) (hqr : ProjLe q r) : ProjLe p r :=
  ⟨by rw [← hpq.1, mul_assoc, hqr.1], by rw [← hpq.2, ← mul_assoc, hqr.2]⟩

theorem antisymm (hpq : ProjLe p q) (hqp : ProjLe q p) : p = q := by
  rw [← hpq.1, hqp.2]

end ProjLe

theorem zero_projLe (p : H →L[ℂ] H) : ProjLe 0 p := by simp [ProjLe]

theorem projLe_one (p : H →L[ℂ] H) : ProjLe p 1 := by
  simp [ProjLe]

theorem ProjLe.eq_zero_of_le_zero {p : H →L[ℂ] H} (h : ProjLe p 0) : p = 0 := by
  simpa using h.1.symm

end Order

/-- For star projections, `p * q = p` already implies `q * p = p`. -/
theorem projLe_of_mul_eq_left {p q : H →L[ℂ] H} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : p * q = p) : ProjLe p q := by
  refine ⟨h, ?_⟩
  have := congrArg star h
  rwa [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at this

theorem projLe_of_mul_eq_right {p q : H →L[ℂ] H} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : q * p = p) : ProjLe p q :=
  ⟨by
    have := congrArg star h
    rwa [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at this, h⟩


/-- If `p ≤ q` are projections of `M`, then `q - p` is a projection of `M`. -/
theorem IsProjection.sub {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} (hp : M.IsProjection p)
    (hq : M.IsProjection q) (hpq : ProjLe p q) : M.IsProjection (q - p) :=
  ⟨hp.1.sub_of_mul_eq_left hq.1 hpq.1, sub_mem hq.2 hp.2⟩

/-- The product of a central projection with a projection of `M` is a projection of `M`,
dominated by both factors. -/
theorem IsCentralProjection.mul_isProjection {M : VonNeumannAlgebra H} {z p : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) (hp : M.IsProjection p) : M.IsProjection (z * p) :=
  ⟨hz.1.mul hp.1 (center_commute hz.2 hp.2), mul_mem (mem_of_mem_center hz.2) hp.2⟩

theorem IsCentralProjection.mul_projLe_right {M : VonNeumannAlgebra H} {z p : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) (hp : M.IsProjection p) : ProjLe (z * p) p := by
  have hc : z * p = p * z := hz.commute hp.2
  constructor
  · rw [mul_assoc, hp.mul_self]
  · rw [← mul_assoc, ← hc, mul_assoc, hp.mul_self]

theorem IsCentralProjection.mul_projLe_left {M : VonNeumannAlgebra H} {z p : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) (hp : M.IsProjection p) : ProjLe (z * p) z := by
  have hc : z * p = p * z := hz.commute hp.2
  constructor
  · rw [mul_assoc, ← hc, ← mul_assoc, hz.1.isIdempotentElem]
  · rw [← mul_assoc, hz.1.isIdempotentElem]


/-! ### Partial isometries and Murray--von Neumann comparison -/

/-- If `star v * v` is idempotent, then `v` is a partial isometry: it acts as the identity
after compression by `star v * v`.

This is the one place in this file where a *metric* fact about `H →L[ℂ] H` is used, namely
the C*-identity in the form `CStarRing.star_mul_self_eq_zero_iff`. -/
theorem mul_star_mul_self_eq_self {v : H →L[ℂ] H} (h : IsIdempotentElem (star v * v)) :
    v * (star v * v) = v := by
  obtain ⟨p, hp⟩ : ∃ p, star v * v = p := ⟨_, rfl⟩
  rw [hp] at h ⊢
  have hpp : p * p = p := h
  have hps : star p = p := by rw [← hp, star_mul, star_star]
  have hstar : star (v - v * p) = star v - p * star v := by rw [star_sub, star_mul, hps]
  have expand : star (v - v * p) * (v - v * p)
      = star v * v - star v * v * p - p * (star v * v) + p * (star v * v) * p := by
    rw [hstar]; noncomm_ring
  rw [hp] at expand
  simp only [hpp] at expand
  have key : star (v - v * p) * (v - v * p) = 0 := by rw [expand]; abel
  have hv : v - v * p = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp key
  exact (sub_eq_zero.mp hv).symm

/-- **Murray--von Neumann equivalence**: `p` and `q` are equivalent when there is a partial
isometry `v ∈ M` with `star v * v = p` and `v * star v = q`. -/
def MvNEquiv (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v ∈ M, star v * v = p ∧ v * star v = q

/-- **Murray--von Neumann subequivalence**: `p` is equivalent to a subprojection of `q`. -/
def MvNLe (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ r, M.IsProjection r ∧ ProjLe r q ∧ M.MvNEquiv p r

namespace MvNEquiv

variable {M : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}

protected theorem refl (hp : M.IsProjection p) : M.MvNEquiv p p :=
  ⟨p, hp.2, by rw [hp.star_eq, hp.mul_self], by rw [hp.star_eq, hp.mul_self]⟩

protected theorem symm (h : M.MvNEquiv p q) : M.MvNEquiv q p := by
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨star v, star_mem hv, by rwa [star_star], by rwa [star_star]⟩

protected theorem trans (hp : IsIdempotentElem p) (hr : IsIdempotentElem r)
    (hpq : M.MvNEquiv p q) (hqr : M.MvNEquiv q r) : M.MvNEquiv p r := by
  obtain ⟨v, hv, hv1, hv2⟩ := hpq
  obtain ⟨w, hw, hw1, hw2⟩ := hqr
  refine ⟨w * v, mul_mem hw hv, ?_, ?_⟩
  · have h1 : star (w * v) * (w * v) = star v * ((star w * w) * v) := by
      rw [star_mul]; noncomm_ring
    rw [h1, hw1, ← hv2, show star v * (v * star v * v) = (star v * v) * (star v * v) from by
      noncomm_ring, hv1]
    exact hp
  · have h1 : (w * v) * star (w * v) = w * ((v * star v) * star w) := by
      rw [star_mul]; noncomm_ring
    rw [h1, hv2, ← hw1, show w * (star w * w * star w) = (w * star w) * (w * star w) from by
      noncomm_ring, hw2]
    exact hr

/-- The right-hand endpoint of an equivalence starting at a projection is again a
projection. -/
theorem isProjection_right (hp : M.IsProjection p) (h : M.MvNEquiv p q) : M.IsProjection q := by
  obtain ⟨v, hv, hv1, hv2⟩ := h
  have hidem : IsIdempotentElem (star v * v) := by rw [hv1]; exact hp.mul_self
  have hvp : v * (star v * v) = v := mul_star_mul_self_eq_self hidem
  refine ⟨⟨?_, ?_⟩, hv2 ▸ mul_mem hv (star_mem hv)⟩
  · show q * q = q
    rw [← hv2, show (v * star v) * (v * star v) = (v * (star v * v)) * star v from by
      noncomm_ring, hvp]
  · show star q = q
    rw [← hv2, star_mul, star_star]

theorem isProjection_left (hq : M.IsProjection q) (h : M.MvNEquiv p q) : M.IsProjection p :=
  isProjection_right hq h.symm

theorem right_eq_zero (h : M.MvNEquiv 0 q) : q = 0 := by
  obtain ⟨v, _, hv1, hv2⟩ := h
  have : v = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hv1
  rw [← hv2, this]
  simp

theorem left_eq_zero (h : M.MvNEquiv p 0) : p = 0 := right_eq_zero h.symm

end MvNEquiv

/-- Conjugating a subprojection `r₁ ≤ q` by a partial isometry `w` implementing `q ~ w star w`
produces an equivalent subprojection of `w star w`.  This is the basic transport step of
comparison theory. -/
theorem conj_isProjection_of_projLe {M : VonNeumannAlgebra H} {q r₁ w : H →L[ℂ] H}
    (hw : w ∈ M) (hw1 : star w * w = q) (hr₁ : M.IsProjection r₁) (hr₁q : ProjLe r₁ q) :
    M.IsProjection (w * r₁ * star w) ∧ M.MvNEquiv r₁ (w * r₁ * star w) ∧
      ProjLe (w * r₁ * star w) (w * star w) := by
  have hidem : (w * r₁ * star w) * (w * r₁ * star w) = w * r₁ * star w := by
    rw [show (w * r₁ * star w) * (w * r₁ * star w) = w * ((r₁ * (star w * w)) * r₁) * star w from
      by noncomm_ring, hw1, hr₁q.1, hr₁.mul_self]
  have hsa : star (w * r₁ * star w) = w * r₁ * star w := by
    rw [star_mul, star_mul, star_star, hr₁.star_eq, mul_assoc]
  refine ⟨⟨⟨hidem, hsa⟩, mul_mem (mul_mem hw hr₁.2) (star_mem hw)⟩, ⟨w * r₁,
    mul_mem hw hr₁.2, ?_, ?_⟩, ?_, ?_⟩
  · rw [show star (w * r₁) * (w * r₁) = (star r₁ * (star w * w)) * r₁ from by
      rw [star_mul]; noncomm_ring, hw1, hr₁.star_eq, hr₁q.1, hr₁.mul_self]
  · rw [show (w * r₁) * star (w * r₁) = w * (r₁ * star r₁) * star w from by
      rw [star_mul]; noncomm_ring, hr₁.star_eq, hr₁.mul_self]
  · rw [show (w * r₁ * star w) * (w * star w) = w * (r₁ * (star w * w)) * star w from by
      noncomm_ring, hw1, hr₁q.1]
  · rw [show (w * star w) * (w * r₁ * star w) = w * ((star w * w) * r₁) * star w from by
      noncomm_ring, hw1, hr₁q.2]

namespace MvNLe

variable {M : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}

theorem of_mvNEquiv (hq : M.IsProjection q) (h : M.MvNEquiv p q) : M.MvNLe p q :=
  ⟨q, hq, ProjLe.refl hq.mul_self, h⟩

theorem of_projLe (hp : M.IsProjection p) (h : ProjLe p q) : M.MvNLe p q :=
  ⟨p, hp, h, MvNEquiv.refl hp⟩

protected theorem refl (hp : M.IsProjection p) : M.MvNLe p p :=
  of_projLe hp (ProjLe.refl hp.mul_self)

protected theorem trans (hp : M.IsProjection p) (hpq : M.MvNLe p q) (hqr : M.MvNLe q r) :
    M.MvNLe p r := by
  obtain ⟨r₁, hr₁, hr₁q, hpr₁⟩ := hpq
  obtain ⟨r₂, hr₂, hr₂r, hqr₂⟩ := hqr
  obtain ⟨w, hw, hw1, hw2⟩ := hqr₂
  obtain ⟨hs, hequiv, hsle⟩ := conj_isProjection_of_projLe hw hw1 hr₁ hr₁q
  refine ⟨w * r₁ * star w, hs, ProjLe.trans (hw2 ▸ hsle) hr₂r, ?_⟩
  exact MvNEquiv.trans hp.mul_self hs.mul_self hpr₁ hequiv

end MvNLe

/-! ### Finite projections -/

/-- A projection of `M` is **finite** when it is not Murray--von Neumann equivalent to a
proper subprojection of itself. -/
def IsFiniteProjection (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  M.IsProjection p ∧
    ∀ q, M.IsProjection q → ProjLe q p → M.MvNEquiv p q → q = p

theorem IsFiniteProjection.isProjection {M : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : M.IsFiniteProjection p) : M.IsProjection p := hp.1

theorem isFiniteProjection_zero (M : VonNeumannAlgebra H) : M.IsFiniteProjection 0 :=
  ⟨M.isProjection_zero, fun q _ hq _ => by simpa using hq.1.symm⟩

/-- The "final projection" form of `mul_star_mul_self_eq_self`. -/
theorem star_mul_self_mul_eq_self {v : H →L[ℂ] H} (h : IsIdempotentElem (v * star v)) :
    (v * star v) * v = v := by
  have h' : IsIdempotentElem (star (star v) * star v) := by simpa using h
  have h1 := mul_star_mul_self_eq_self h'
  simp only [star_star] at h1
  have h2 := congrArg star h1
  simpa [star_mul, mul_assoc] using h2

/-- Orthogonal sums of Murray--von Neumann equivalences are equivalences. -/
theorem MvNEquiv.add {M : VonNeumannAlgebra H} {p₁ q₁ p₂ q₂ : H →L[ℂ] H}
    (hp₁ : M.IsProjection p₁) (hp₂ : M.IsProjection p₂)
    (h₁ : M.MvNEquiv p₁ q₁) (h₂ : M.MvNEquiv p₂ q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) : M.MvNEquiv (p₁ + p₂) (q₁ + q₂) := by
  obtain ⟨v, hv, hv1, hv2⟩ := h₁
  obtain ⟨w, hw, hw1, hw2⟩ := h₂
  have hq₁ : M.IsProjection q₁ := MvNEquiv.isProjection_right hp₁ ⟨v, hv, hv1, hv2⟩
  have hq₂ : M.IsProjection q₂ := MvNEquiv.isProjection_right hp₂ ⟨w, hw, hw1, hw2⟩
  -- `v` and `w` are partial isometries with the indicated initial and final projections
  have hvp : v * p₁ = v := by
    rw [← hv1]
    exact mul_star_mul_self_eq_self (show IsIdempotentElem (star v * v) by
      rw [hv1]; exact hp₁.mul_self)
  have hwp : w * p₂ = w := by
    rw [← hw1]
    exact mul_star_mul_self_eq_self (show IsIdempotentElem (star w * w) by
      rw [hw1]; exact hp₂.mul_self)
  have hvq : q₁ * v = v := by
    rw [← hv2]
    exact star_mul_self_mul_eq_self (show IsIdempotentElem (v * star v) by
      rw [hv2]; exact hq₁.mul_self)
  have hwq : q₂ * w = w := by
    rw [← hw2]
    exact star_mul_self_mul_eq_self (show IsIdempotentElem (w * star w) by
      rw [hw2]; exact hq₂.mul_self)
  have e1 : star v * w = 0 := by
    conv_lhs => rw [← hvq, ← hwq]
    rw [show star (q₁ * v) * (q₂ * w) = star v * ((star q₁ * q₂) * w) from by
      rw [star_mul]; noncomm_ring, hq₁.star_eq, hq]
    simp
  have e2 : star w * v = 0 := by
    have := congrArg star e1
    rwa [star_mul, star_star, star_zero] at this
  have e3 : v * star w = 0 := by
    conv_lhs => rw [← hvp, ← hwp]
    rw [show (v * p₁) * star (w * p₂) = v * ((p₁ * star p₂) * star w) from by
      rw [star_mul]; noncomm_ring, hp₂.star_eq, hp]
    simp
  have e4 : w * star v = 0 := by
    have := congrArg star e3
    rwa [star_mul, star_star, star_zero] at this
  refine ⟨v + w, add_mem hv hw, ?_, ?_⟩
  · rw [star_add, add_mul, mul_add, mul_add, hv1, hw1, e1, e2]
    abel
  · rw [star_add, add_mul, mul_add, mul_add, hv2, hw2, e3, e4]
    abel

/-- A central compression of a finite projection is finite. -/
theorem IsFiniteProjection.mul_central {M : VonNeumannAlgebra H} {z p : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) (hp : M.IsFiniteProjection p) :
    M.IsFiniteProjection (z * p) := by
  obtain ⟨hpproj, hpfin⟩ := hp
  have hzp : M.IsProjection (z * p) := hz.mul_isProjection hpproj
  refine ⟨hzp, fun q hq hqzp hequiv => ?_⟩
  set p' : H →L[ℂ] H := (1 - z) * p with hp'
  have hz' : M.IsCentralProjection (1 - z) := hz.one_sub
  have hp'proj : M.IsProjection p' := hz'.mul_isProjection hpproj
  have hcomm : z * p = p * z := hz.commute hpproj.2
  have hzq : z * q = q := (hqzp.trans (hz.mul_projLe_left hpproj)).2
  have hqz : q * z = z * q := (hz.commute hq.2).symm
  have hqp' : q * p' = 0 := by
    rw [hp', ← mul_assoc, mul_sub, mul_one, hqz, hzq, sub_self, zero_mul]
  have hzpp' : (z * p) * p' = 0 := by
    rw [hp', show (z * p) * ((1 - z) * p) = (z * p) * p - (z * (p * z)) * p from by noncomm_ring,
      ← hcomm, show (z * (z * p)) * p = (z * z) * (p * p) from by noncomm_ring,
      show (z * p) * p = z * (p * p) from by noncomm_ring, hz.1.isIdempotentElem,
      hpproj.mul_self, sub_self]
  have hsum : z * p + p' = p := by rw [hp']; noncomm_ring
  have hqsum : M.IsProjection (q + p') := ⟨hq.1.add hp'proj.1 hqp', add_mem hq.2 hp'proj.2⟩
  have hequiv' : M.MvNEquiv p (q + p') := by
    rw [← hsum]
    exact MvNEquiv.add hzp hp'proj hequiv (MvNEquiv.refl hp'proj) hzpp' hqp'
  have hqp : q * p = q := (hqzp.trans (hz.mul_projLe_right hpproj)).1
  have hp'p : p' * p = p' := by rw [hp', mul_assoc, hpproj.mul_self]
  have hle : ProjLe (q + p') p :=
    projLe_of_mul_eq_left hqsum.1 hpproj.1 (by rw [add_mul, hqp, hp'p])
  have hfin := hpfin (q + p') hqsum hle hequiv'
  have hqval : q = p - p' := by rw [← hfin]; abel
  rw [hqval, hp']
  noncomm_ring

/-! ### Corners -/

/-- The **corner** `p M p` of `M` cut down by a self-adjoint element `p`, as a non-unital star
subalgebra of `H →L[ℂ] H`.  When `p` is a projection of `M` this is the usual compressed
algebra, with unit `p` (see `VonNeumannAlgebra.corner_eq_image`). -/
def corner (M : VonNeumannAlgebra H) {p : H →L[ℂ] H} (hp : IsSelfAdjoint p) :
    NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {x | x ∈ M ∧ p * x = x ∧ x * p = x}
  add_mem' := by
    rintro x y ⟨hx, hx1, hx2⟩ ⟨hy, hy1, hy2⟩
    exact ⟨add_mem hx hy, by rw [mul_add, hx1, hy1], by rw [add_mul, hx2, hy2]⟩
  zero_mem' := ⟨zero_mem M, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1, hx2⟩ ⟨hy, hy1, hy2⟩
    exact ⟨mul_mem hx hy, by rw [← mul_assoc, hx1], by rw [mul_assoc, hy2]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx1, hx2⟩
    refine ⟨?_, by rw [mul_smul_comm, hx1], by rw [smul_mul_assoc, hx2]⟩
    exact mem_carrier.mp (SMulMemClass.smul_mem c (mem_carrier.mpr hx))
  star_mem' := by
    rintro x ⟨hx, hx1, hx2⟩
    refine ⟨star_mem hx, ?_, ?_⟩
    · have h := congrArg star hx2
      rwa [star_mul, hp.star_eq] at h
    · have h := congrArg star hx1
      rwa [star_mul, hp.star_eq] at h

theorem mem_corner_iff {M : VonNeumannAlgebra H} {p x : H →L[ℂ] H} {hp : IsSelfAdjoint p} :
    x ∈ M.corner hp ↔ x ∈ M ∧ p * x = x ∧ x * p = x := Iff.rfl

theorem corner_subset {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} {hp : IsSelfAdjoint p} :
    (M.corner hp : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H)) := fun _ hx => hx.1

theorem mul_mul_mem_corner {M : VonNeumannAlgebra H} {p x : H →L[ℂ] H}
    (hp : M.IsProjection p) (hx : x ∈ M) : p * x * p ∈ M.corner hp.1.isSelfAdjoint :=
  ⟨mul_mem (mul_mem hp.2 hx) hp.2,
    by rw [← mul_assoc, ← mul_assoc, hp.mul_self],
    by rw [mul_assoc, hp.mul_self]⟩

/-- The corner is exactly the set of compressions `p x p`, `x ∈ M`. -/
theorem corner_eq_image {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (hp : M.IsProjection p) :
    (M.corner hp.1.isSelfAdjoint : Set (H →L[ℂ] H)) =
      (fun x => p * x * p) '' (M : Set (H →L[ℂ] H)) := by
  ext x
  constructor
  · rintro ⟨hx, hx1, hx2⟩
    refine ⟨x, hx, ?_⟩
    show p * x * p = x
    rw [hx1, hx2]
  · rintro ⟨y, hy, rfl⟩
    exact mul_mul_mem_corner hp hy

/-- `p` is a unit for its own corner. -/
theorem corner_mul_left {M : VonNeumannAlgebra H} {p x : H →L[ℂ] H} {hp : IsSelfAdjoint p}
    (hx : x ∈ M.corner hp) : p * x = x := hx.2.1

theorem corner_mul_right {M : VonNeumannAlgebra H} {p x : H →L[ℂ] H} {hp : IsSelfAdjoint p}
    (hx : x ∈ M.corner hp) : x * p = x := hx.2.2

theorem mem_corner_one {M : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ M.corner (IsSelfAdjoint.one (H →L[ℂ] H)) ↔ x ∈ M := by
  simp [mem_corner_iff]

/-- Corners are monotone in the compressing projection. -/
theorem corner_mono {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} {hp : IsSelfAdjoint p}
    {hq : IsSelfAdjoint q} (h : ProjLe p q) :
    (M.corner hp : Set (H →L[ℂ] H)) ⊆ (M.corner hq : Set (H →L[ℂ] H)) := by
  rintro x ⟨hx, hx1, hx2⟩
  refine ⟨hx, ?_, ?_⟩
  · rw [← hx1, ← mul_assoc, h.2]
  · rw [← hx2, mul_assoc, h.1]

theorem corner_zero (M : VonNeumannAlgebra H) :
    (M.corner (IsSelfAdjoint.zero (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = {0} := by
  ext x
  constructor
  · rintro ⟨-, -, hx2⟩
    simpa using hx2.symm
  · rintro rfl
    exact ⟨zero_mem M, by simp, by simp⟩

/-- Compression by a *central* projection is just multiplication by it. -/
theorem central_corner_eq_image {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) :
    (M.corner hz.1.isSelfAdjoint : Set (H →L[ℂ] H)) =
      (fun x => z * x) '' (M : Set (H →L[ℂ] H)) := by
  ext x
  constructor
  · rintro ⟨hx, hx1, -⟩
    exact ⟨x, hx, hx1⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mul_mem (mem_of_mem_center hz.2) hy, ?_, ?_⟩
    · show z * (z * y) = z * y
      rw [← mul_assoc, hz.1.isIdempotentElem]
    · show z * y * z = z * y
      rw [mul_assoc, ← hz.commute hy, ← mul_assoc, hz.1.isIdempotentElem]

/-- Compression by a central projection is multiplicative on `M`. -/
theorem central_mul_mul_central {M : VonNeumannAlgebra H} {z x y : H →L[ℂ] H}
    (hz : M.IsCentralProjection z) (hx : x ∈ M) : (z * x) * (z * y) = z * (x * y) := by
  rw [← mul_assoc, mul_assoc z x z, ← hz.commute hx, ← mul_assoc, hz.1.isIdempotentElem,
    mul_assoc]

/-! ### Central support and fullness -/

/-- `z` is a **central support** (central carrier) of `p`: the smallest central projection
acting as the identity on `p`.

This is phrased as a predicate rather than as a construction, so that no completeness of the
projection lattice (an analytic input) is needed. -/
def IsCentralSupport (M : VonNeumannAlgebra H) (p z : H →L[ℂ] H) : Prop :=
  M.IsCentralProjection z ∧ z * p = p ∧
    ∀ w, M.IsCentralProjection w → w * p = p → z * w = z

/-- A projection is **full** when its central support is `1`. -/
def IsFull (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  M.IsCentralSupport p 1

namespace IsCentralSupport

variable {M : VonNeumannAlgebra H} {p z z' : H →L[ℂ] H}

theorem isCentralProjection (h : M.IsCentralSupport p z) : M.IsCentralProjection z := h.1

theorem mul_eq (h : M.IsCentralSupport p z) : z * p = p := h.2.1

/-- `p ≤ z` for the central support `z` of a projection `p` of `M`. -/
theorem projLe (h : M.IsCentralSupport p z) (hp : M.IsProjection p) : ProjLe p z :=
  ⟨by rw [← h.1.commute hp.2, h.2.1], h.2.1⟩

/-- The central support is unique. -/
theorem unique (h : M.IsCentralSupport p z) (h' : M.IsCentralSupport p z') : z = z' := by
  have h1 : z * z' = z := h.2.2 z' h'.1 h'.2.1
  have h2 : z' * z = z' := h'.2.2 z h.1 h.2.1
  calc z = z * z' := h1.symm
    _ = z' * z := (center_commute h.1.2 (mem_of_mem_center h'.1.2)).eq
    _ = z' := h2

end IsCentralSupport

/-- A full projection meets every nonzero central projection nontrivially: this is the basic
central-intersection statement of comparison theory. -/
theorem IsFull.mul_ne_zero {M : VonNeumannAlgebra H} {p z : H →L[ℂ] H} (hp : M.IsFull p)
    (hz : M.IsCentralProjection z) (hz0 : z ≠ 0) : z * p ≠ 0 := by
  intro hzp
  refine hz0 ?_
  have hw : (1 - z) * p = p := by rw [sub_mul, one_mul, hzp, sub_zero]
  have h1 := hp.2.2 (1 - z) hz.one_sub hw
  rw [one_mul] at h1
  exact sub_eq_self.mp h1

/-- Conversely, a projection meeting every nonzero central projection is full. -/
theorem isFull_of_forall_central {M : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (h : ∀ z, M.IsCentralProjection z → z ≠ 0 → z * p ≠ 0) : M.IsFull p := by
  refine ⟨M.isCentralProjection_one, one_mul p, fun w hw hwp => ?_⟩
  rw [one_mul]
  have hz : (1 - w) * p = 0 := by rw [sub_mul, one_mul, hwp, sub_self]
  have h1 : (1 : H →L[ℂ] H) - w = 0 := by
    by_contra hne
    exact h (1 - w) hw.one_sub hne hz
  exact (sub_eq_zero.mp h1).symm

/-- Sanity checks: `1` is full and `0` has central support `0`. -/
theorem isFull_one (M : VonNeumannAlgebra H) : M.IsFull 1 :=
  ⟨M.isCentralProjection_one, one_mul 1, fun w _ hw => by rw [one_mul]; rwa [mul_one] at hw⟩

theorem isCentralSupport_zero (M : VonNeumannAlgebra H) : M.IsCentralSupport 0 0 :=
  ⟨M.isCentralProjection_zero, mul_zero 0, fun w _ _ => zero_mul w⟩

theorem isFull_iff_forall_central {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} :
    M.IsFull p ↔ ∀ z, M.IsCentralProjection z → z ≠ 0 → z * p ≠ 0 :=
  ⟨fun hp _ hz hz0 => hp.mul_ne_zero hz hz0, isFull_of_forall_central⟩

/-- For a full projection `p` of `M` and a nonzero central projection `z`, the compression
`z * p` is a nonzero projection of `M` dominated by both `z` and `p`. -/
theorem IsFull.exists_nonzero_projection {M : VonNeumannAlgebra H} {p z : H →L[ℂ] H}
    (hp : M.IsProjection p) (hfull : M.IsFull p) (hz : M.IsCentralProjection z) (hz0 : z ≠ 0) :
    M.IsProjection (z * p) ∧ z * p ≠ 0 ∧ ProjLe (z * p) z ∧ ProjLe (z * p) p :=
  ⟨hz.mul_isProjection hp, hfull.mul_ne_zero hz hz0, hz.mul_projLe_left hp,
    hz.mul_projLe_right hp⟩

end VonNeumannAlgebra
