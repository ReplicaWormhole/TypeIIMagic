import FiniteFiber.FiniteFibers
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# From the GNS product orbit to a faithful tracial support corner

This file formalizes the algebraic part of the manuscript's GNS faithfulness
and fullness argument.  It does not assume a generic ``faithful corner''
interface.  Instead, it starts from a vector functional, a specified dense
product orbit for the region and its complement, and the exact commutation
property used in the manuscript.

The local stabilizer construction of the support projections and the
operator-topological extension of local traciality are separate obligations.
-/

namespace FiniteFiber

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector functional associated with a vector in a complex Hilbert space. -/
def vectorFunctional (xi : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := ⟪xi, a xi⟫_ℂ
  map_add' a b := by
    rw [ContinuousLinearMap.add_apply, inner_add_right]
  map_smul' c a := by
    rw [ContinuousLinearMap.smul_apply, inner_smul_right]
    rfl

omit [CompleteSpace H] in
@[simp]
lemma vectorFunctional_apply (xi : H) (a : H →L[ℂ] H) :
    vectorFunctional xi a = ⟪xi, a xi⟫_ℂ :=
  rfl

/-- Vectors obtained by acting first from the complementary region and then from the region. -/
def productOrbit (region complement : Set (H →L[ℂ] H)) (xi : H) : Set H :=
  {v | ∃ a ∈ region, ∃ b ∈ complement, v = (a * b) xi}

/-- The manuscript's GNS-density input, stated as density of the linear span of product vectors. -/
def ProductOrbitDense (region complement : Set (H →L[ℂ] H)) (xi : H) : Prop :=
  Dense (Submodule.span ℂ (productOrbit region complement xi) : Set H)

/-- A region/complement realization of the vector-corner hypotheses. -/
structure VectorCornerData (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) (xi : H) where
  q_projection : IsProjectionIn M q
  q_fixes_xi : q xi = xi
  region : Set (H →L[ℂ] H)
  complement : Set (H →L[ℂ] H)
  region_mem : ∀ a : H →L[ℂ] H, a ∈ region → a ∈ M
  region_commutes_complement : ∀ a : H →L[ℂ] H, a ∈ region →
    ∀ b : H →L[ℂ] H, b ∈ complement → a * b = b * a
  commutes_complement : ∀ x : H →L[ℂ] H, x ∈ M →
    ∀ b : H →L[ℂ] H, b ∈ complement → x * b = b * x
  product_orbit_dense : ProductOrbitDense region complement xi
  tracial : ∀ {a b : H →L[ℂ] H},
    IsCornerElement M q a → IsCornerElement M q b →
      vectorFunctional xi (a * b) = vectorFunctional xi (b * a)

/-- A subprojection of the corner support is represented by a corner element. -/
lemma isCornerElement_of_subprojection
    {M : VonNeumannAlgebra H} {q r : H →L[ℂ] H}
    (hr : IsProjectionIn M r) (hrq : IsSubprojection r q) :
    IsCornerElement M q r :=
  ⟨hr.1, hrq.2, hrq.1⟩

/-- The support projection itself is a corner element. -/
lemma isCornerElement_support
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H}
    (hq : IsProjectionIn M q) :
    IsCornerElement M q q := by
  exact ⟨hq.1, hq.2.isIdempotentElem, hq.2.isIdempotentElem⟩

/-- The product of two corner elements is again a corner element. -/
lemma IsCornerElement.mul
    {M : VonNeumannAlgebra H} {q a b : H →L[ℂ] H}
    (ha : IsCornerElement M q a) (hb : IsCornerElement M q b) :
    IsCornerElement M q (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, ?_, ?_⟩
  · calc
      q * (a * b) = (q * a) * b := by rw [mul_assoc]
      _ = a * b := by rw [ha.2.1]
  · calc
      (a * b) * q = a * (b * q) := by rw [mul_assoc]
      _ = a * b := by rw [hb.2.2]

/-- Taking adjoints preserves the corner condition. -/
lemma IsCornerElement.star_mem
    {M : VonNeumannAlgebra H} {q a : H →L[ℂ] H}
    (hq : IsProjectionIn M q) (ha : IsCornerElement M q a) :
    IsCornerElement M q (star a) := by
  refine ⟨M.star_mem' ha.1, ?_, ?_⟩
  · have h : star (a * q) = star a := congrArg star ha.2.2
    simpa [star_mul, hq.2.isSelfAdjoint.star_eq] using h
  · have h : star (q * a) = star a := congrArg star ha.2.1
    simpa [star_mul, hq.2.isSelfAdjoint.star_eq] using h

/-- Compressing an element of the algebra by the support gives a corner element. -/
lemma isCornerElement_compress
    {M : VonNeumannAlgebra H} {q a : H →L[ℂ] H}
    (hq : IsProjectionIn M q) (ha : a ∈ M) :
    IsCornerElement M q (q * a * q) := by
  have hqq : q * q = q := hq.2.isIdempotentElem
  refine ⟨mul_mem (mul_mem hq.1 ha) hq.1, ?_, ?_⟩
  · calc
      q * (q * a * q) = (q * q) * a * q := by repeat rw [mul_assoc]
      _ = q * a * q := by rw [hqq]
  · calc
      (q * a * q) * q = q * a * (q * q) := by repeat rw [mul_assoc]
      _ = q * a * q := by rw [hqq]

/-- For a projection, its vector-functional value is the squared norm of its action on the vector. -/
lemma vectorFunctional_projection_eq_inner
    {M : VonNeumannAlgebra H} {xi : H} {r : H →L[ℂ] H}
    (hr : IsProjectionIn M r) :
    vectorFunctional xi r = ⟪r xi, r xi⟫_ℂ := by
  rw [vectorFunctional_apply]
  symm
  calc
    ⟪r xi, r xi⟫_ℂ = ⟪xi, (star r) (r xi)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪xi, r xi⟫_ℂ := by
      rw [hr.2.isSelfAdjoint.star_eq]
      change ⟪xi, (r * r) xi⟫_ℂ = ⟪xi, r xi⟫_ℂ
      rw [hr.2.isIdempotentElem]

/-- A zero vector-functional value on a projection annihilates the vector. -/
lemma projection_apply_eq_zero_of_vectorFunctional_eq_zero
    {M : VonNeumannAlgebra H} {xi : H} {r : H →L[ℂ] H}
    (hr : IsProjectionIn M r) (hzero : vectorFunctional xi r = 0) :
    r xi = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← vectorFunctional_projection_eq_inner hr, hzero]

/--
A zero vector-functional value on a subprojection of the support annihilates
every vector obtained by a corner element.  This is the tracial step in the
manuscript's faithfulness argument.
-/
lemma projection_mul_apply_eq_zero_of_vectorFunctional_eq_zero
    {M : VonNeumannAlgebra H} {q r y : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi)
    (hr : IsProjectionIn M r) (hrq : IsSubprojection r q)
    (hy : IsCornerElement M q y) (hzero : vectorFunctional xi r = 0) :
    (r * y) xi = 0 := by
  have hr_corner : IsCornerElement M q r :=
    isCornerElement_of_subprojection hr hrq
  have hstar_y : IsCornerElement M q (star y) :=
    hy.star_mem D.q_projection
  have hstar_y_r : IsCornerElement M q (star y * r) :=
    hstar_y.mul hr_corner
  have htrace :
      vectorFunctional xi ((star y * r) * y) =
        vectorFunctional xi (y * (star y * r)) :=
    D.tracial hstar_y_r hy
  have hrxi : r xi = 0 :=
    projection_apply_eq_zero_of_vectorFunctional_eq_zero hr hzero
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    ⟪(r * y) xi, (r * y) xi⟫_ℂ = vectorFunctional xi ((star y * r) * y) := by
      rw [vectorFunctional_apply]
      symm
      calc
        ⟪xi, ((star y * r) * y) xi⟫_ℂ =
            ⟪xi, star (r * y) ((r * y) xi)⟫_ℂ := by
          have hrr : r * r = r := hr.2.isIdempotentElem
          have hsr : star r = r := hr.2.isSelfAdjoint.star_eq
          change ⟪xi, (star y * r * y) xi⟫_ℂ =
            ⟪xi, (star (r * y) * (r * y)) xi⟫_ℂ
          apply congrArg (fun h : H => ⟪xi, h⟫_ℂ)
          apply congrArg (fun t : H →L[ℂ] H => t xi)
          calc
              (star y * r) * y = star y * (r * y) := by rw [mul_assoc]
              _ = star y * ((r * r) * y) := by rw [hrr]
              _ = (star y * (r * r)) * y := by rw [← mul_assoc]
              _ = ((star y * r) * r) * y := by rw [← mul_assoc]
              _ = (star y * r) * (r * y) := by rw [mul_assoc]
              _ = (star y * star r) * (r * y) := by rw [hsr]
              _ = star (r * y) * (r * y) := by rw [star_mul]
        _ = ⟪(r * y) xi, (r * y) xi⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_right]
    _ = vectorFunctional xi (y * (star y * r)) := htrace
    _ = 0 := by
      rw [vectorFunctional_apply]
      change ⟪xi, y ((star y) (r xi))⟫_ℂ = 0
      rw [hrxi]
      simp

/-- A null subprojection annihilates every regional vector after compressing by the support. -/
lemma VectorCornerData.projection_mul_region_apply_eq_zero
    {M : VonNeumannAlgebra H} {q r : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi)
    (hr : IsProjectionIn M r) (hrq : IsSubprojection r q)
    (hzero : vectorFunctional xi r = 0)
    {a : H →L[ℂ] H} (ha : a ∈ D.region) :
    (r * a) xi = 0 := by
  have haM : a ∈ M := D.region_mem a ha
  have hy : IsCornerElement M q (q * a * q) :=
    isCornerElement_compress D.q_projection haM
  have hcompressed : (r * (q * a * q)) xi = 0 :=
    projection_mul_apply_eq_zero_of_vectorFunctional_eq_zero D hr hrq hy hzero
  have hrq_apply (v : H) : r (q v) = r v := by
    change (r * q) v = r v
    rw [hrq.1]
  calc
    (r * a) xi = (r * (q * a * q)) xi := by
      change r (a xi) = r (q (a (q xi)))
      calc
        r (a xi) = r (q (a xi)) := (hrq_apply (a xi)).symm
        _ = r (q (a (q xi))) := by rw [D.q_fixes_xi]
    _ = 0 := hcompressed

/--
The dense product orbit upgrades tracial nullity of a support subprojection to
vanishing of that projection.  This is the faithful-corner bridge used by the
manuscript, with the regional and complementary commutation hypotheses stated
explicitly.
-/
lemma VectorCornerData.projection_eq_zero_of_vectorFunctional_eq_zero
    {M : VonNeumannAlgebra H} {q r : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi)
    (hr : IsProjectionIn M r) (hrq : IsSubprojection r q)
    (hzero : vectorFunctional xi r = 0) :
    r = 0 := by
  have horbit_zero : Set.EqOn r (0 : H →L[ℂ] H)
      (productOrbit D.region D.complement xi) := by
    rintro v ⟨a, ha, b, hb, rfl⟩
    have hra : (r * a) xi = 0 :=
      D.projection_mul_region_apply_eq_zero hr hrq hzero ha
    have hab : a * b = b * a := D.region_commutes_complement a ha b hb
    have hrb : r * b = b * r := D.commutes_complement r hr.1 b hb
    change (r * (a * b)) xi = 0
    calc
      (r * (a * b)) xi = (b * (r * a)) xi := by
        congr 1
        calc
          r * (a * b) = r * (b * a) := by rw [hab]
          _ = (r * b) * a := by rw [mul_assoc]
          _ = (b * r) * a := by rw [hrb]
          _ = b * (r * a) := by rw [mul_assoc]
      _ = 0 := by
        change b ((r * a) xi) = 0
        rw [hra]
        exact map_zero b
  exact ContinuousLinearMap.ext_on D.product_orbit_dense horbit_zero

/-- The vector-functional realization supplies the faithful tracial-corner interface of I001. -/
def VectorCornerData.toFaithfulTracialCorner
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi) : FaithfulTracialCorner M q where
  tau := vectorFunctional xi
  tracial := D.tracial
  faithful_on_subprojection _ hr hrq hzero :=
    D.projection_eq_zero_of_vectorFunctional_eq_zero hr hrq hzero

/--
The same product-orbit density makes the support projection full.  This is
the manuscript's central-projection argument, with both commutation steps
made explicit.
-/
theorem VectorCornerData.isFullProjection
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi) :
    IsFullProjection M q := by
  refine ⟨D.q_projection, ?_⟩
  intro z hz hz_nonzero hzq
  have hzxi : z xi = 0 := by
    calc
      z xi = z (q xi) := by rw [D.q_fixes_xi]
      _ = (z * q) xi := rfl
      _ = 0 := by rw [hzq]; exact map_zero (0 : H →L[ℂ] H)
  have horbit_zero : Set.EqOn z (0 : H →L[ℂ] H)
      (productOrbit D.region D.complement xi) := by
    rintro v ⟨a, ha, b, hb, rfl⟩
    have hza : z * a = a * z := hz.commutes (D.region_mem a ha)
    have hzb : z * b = b * z := D.commutes_complement z hz.1.1 b hb
    change (z * (a * b)) xi = 0
    calc
      (z * (a * b)) xi = ((a * b) * z) xi := by
        congr 1
        calc
          z * (a * b) = (z * a) * b := by rw [mul_assoc]
          _ = (a * z) * b := by rw [hza]
          _ = a * (z * b) := by rw [← mul_assoc]
          _ = a * (b * z) := by rw [hzb]
          _ = (a * b) * z := by rw [mul_assoc]
      _ = 0 := by
        change a (b (z xi)) = 0
        rw [hzxi]
        simp
  exact hz_nonzero (ContinuousLinearMap.ext_on D.product_orbit_dense horbit_zero)

/--
The checked support-corner theorem: vector traciality and a specified dense
regional/complementary product orbit imply a nonzero finite projection below
every nonzero central projection.
-/
theorem VectorCornerData.full_tracial_corner_semifinite
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (D : VectorCornerData M q xi) :
    IsSemifinite M :=
  FiniteFiber.full_tracial_corner_semifinite
    D.toFaithfulTracialCorner D.isFullProjection

/-- Each supplied finite central fiber receives the canonical finite witness from the GNS support. -/
theorem VectorCornerData.finite_central_fiber_canonical_witness
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    {ι : Type*} [Fintype ι]
    (D : VectorCornerData M q xi) (fibers : FiniteCentralFiberFamily M ι) (i : ι) :
    IsFiniteProjection M (fibers.projection i * q) ∧
      fibers.projection i * q ≠ 0 ∧
      IsSubprojection (fibers.projection i * q) (fibers.projection i) :=
  FiniteFiber.finite_central_fiber_canonical_witness
    D.toFaithfulTracialCorner D.isFullProjection fibers i

end FiniteFiber
