import FiniteFiber.StrongSupport
import FiniteFiber.VectorCorner

/-!
# The checked support-to-finite-fiber theorem from specified GNS-orbit data

This file joins the strong-limit support layer to specified GNS-orbit data.  It
does not construct a GNS representation or prove the dense product orbit: those
are explicit fields in `GNSOrbitConditions`.  It is also deliberately explicit
about the remaining analytic input: traciality of the compressed vector
functional on all corner elements.  In the manuscript that input is obtained
from finite-dimensional trace cyclicity, bounded strong continuity, and
Kaplansky density.
-/

namespace FiniteFiber

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Specified regional/complementary data for the support-corner argument.  The
fields reproduce the locality, density, and corner-traciality statements used
in the manuscript's faithfulness/fullness argument; they do not construct the
GNS representation or derive those statements from a stabilizer system, and no
faithful-corner conclusion is assumed.
-/
structure GNSOrbitConditions (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) (xi : H) where
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

/--
The complete checked conclusion represented by the I002 technical theorem.
The projection-fidelity field is deliberately restricted to support
subprojections, which is exactly the condition consumed by the
Murray--von Neumann finiteness argument.
-/
structure SupportCornerConclusion (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) (xi : H) where
  q_projection : IsProjectionIn M q
  q_fixes_xi : q xi = xi
  full : IsFullProjection M q
  projection_faithful : ∀ r : H →L[ℂ] H,
    IsProjectionIn M r → IsSubprojection r q → vectorFunctional xi r = 0 → r = 0
  central_witness : ∀ z : H →L[ℂ] H, IsCentralProjection M z → z ≠ 0 →
    IsFiniteProjection M (z * q) ∧ z * q ≠ 0 ∧ IsSubprojection (z * q) z
  semifinite : IsSemifinite M

/-- Combine strong-support facts with the specified orbit data required by the vector-corner proof. -/
def GNSOrbitConditions.toVectorCornerData
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (C : GNSOrbitConditions M q xi)
    (hq : IsProjectionIn M q) (hfix : q xi = xi) :
    VectorCornerData M q xi where
  q_projection := hq
  q_fixes_xi := hfix
  region := C.region
  complement := C.complement
  region_mem := C.region_mem
  region_commutes_complement := C.region_commutes_complement
  commutes_complement := C.commutes_complement
  product_orbit_dense := C.product_orbit_dense
  tracial := C.tracial

/--
Bundle all clauses of the checked support-to-central-summand theorem from the
decreasing-support and specified-orbit hypotheses.
-/
theorem DecreasingProjectionSequence.supportCornerConclusion_of_gnsOrbit
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H}
    {q : H →L[ℂ] H} {xi : H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q)
    (hfix : ∀ n : ℕ, p n xi = xi)
    (C : GNSOrbitConditions M q xi) :
    SupportCornerConclusion M q xi := by
  let hq : IsProjectionIn M q := D.strongLimit_isProjectionIn hp
  let hfixq : q xi = xi := stronglyTendsTo_fixes hp hfix
  let V : VectorCornerData M q xi := C.toVectorCornerData hq hfixq
  exact
    { q_projection := hq
      q_fixes_xi := hfixq
      full := V.isFullProjection
      projection_faithful := fun r hr hrq hzero =>
        V.projection_eq_zero_of_vectorFunctional_eq_zero hr hrq hzero
      central_witness := fun z hz hz_nonzero =>
        canonical_central_witness_of_full_tracial_corner
          V.toFaithfulTracialCorner V.isFullProjection hz hz_nonzero
      semifinite := V.full_tracial_corner_semifinite }

/--
The support-to-finite-fiber theorem.  It proves the manuscript's
central-summand conclusion from decreasing local supports and specified orbit
conditions, not from an unexplained faithfulness or fullness assumption.
-/
theorem DecreasingProjectionSequence.full_tracial_corner_semifinite_of_gnsOrbit
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H}
    {q : H →L[ℂ] H} {xi : H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q)
    (hfix : ∀ n : ℕ, p n xi = xi)
    (C : GNSOrbitConditions M q xi) :
    IsSemifinite M := by
  let V : VectorCornerData M q xi := C.toVectorCornerData
    (D.strongLimit_isProjectionIn hp) (stronglyTendsTo_fixes hp hfix)
  exact V.full_tracial_corner_semifinite

/-- The canonical finite witness in each supplied finite central fiber. -/
theorem DecreasingProjectionSequence.finite_central_fiber_witness_of_gnsOrbit
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H}
    {q : H →L[ℂ] H} {xi : H} {ι : Type*} [Fintype ι]
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q)
    (hfix : ∀ n : ℕ, p n xi = xi)
    (C : GNSOrbitConditions M q xi)
    (fibers : FiniteCentralFiberFamily M ι) (i : ι) :
    IsFiniteProjection M (fibers.projection i * q) ∧
      fibers.projection i * q ≠ 0 ∧
      IsSubprojection (fibers.projection i * q) (fibers.projection i) := by
  let V : VectorCornerData M q xi := C.toVectorCornerData
    (D.strongLimit_isProjectionIn hp) (stronglyTendsTo_fixes hp hfix)
  exact V.finite_central_fiber_canonical_witness fibers i

end FiniteFiber
