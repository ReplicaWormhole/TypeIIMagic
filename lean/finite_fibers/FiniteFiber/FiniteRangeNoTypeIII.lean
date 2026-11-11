import FiniteFiber.FiniteRangeTracialCorner

/-!
# FF23 — finite-range stabilizer systems have no type-III central summand

For supplied finite-range stabilizer data, a quasilocal completion, and a
global stabilizer state, this module applies the FF20--FF22 support-corner
conclusion at the canonical GNS von Neumann algebra.  It proves the exact
central-summand form: every nonzero central projection has a nonzero finite
subprojection.  The quasilocal completion and global state remain supplied
data; no direct-integral or fibrewise type-classification claim is formalized.

Under the usual separability and central-decomposition hypotheses, the
central-summand conclusion excludes type-III factor fibres.  That implication
is prose only: the requisite direct-integral API is not developed here.
-/

namespace FiniteFiber

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The projection-level absence-of-finiteness property for a central summand. -/
def SummandHasNoNonzeroFiniteProjection (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  ∀ e : H →L[ℂ] H, IsFiniteProjection M e → IsSubprojection e z → e = 0

/-- Semifiniteness in the packet's central-summand sense rules out the displayed
absence-of-finiteness property in each nonzero central summand. -/
theorem not_summandHasNoNonzeroFiniteProjection_of_isSemifinite
    {M : VonNeumannAlgebra H} (hM : IsSemifinite M) {z : H →L[ℂ] H}
    (hz : IsCentralProjection M z) (hz0 : z ≠ 0) :
    ¬ SummandHasNoNonzeroFiniteProjection M z := by
  intro hno
  obtain ⟨e, hefin, hene, hesub⟩ := hM z hz hz0
  exact hene (hno e hefin hesub)

end Abstract

section FiniteRange

variable {Site : Type*} [DecidableEq Site]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped FiniteFiber.FiniteRegionQubitMatrix

namespace FiniteRangeStabilizerSystem

variable (R : FiniteRangeStabilizerSystem Site) {Q : QuasilocalEmbedding Site A}
variable (W : QuasilocalStabilizerState R.stabilizerSystem Q)

/-- For every nonzero central projection of the canonical GNS von Neumann
algebra, `z * q` is a nonzero finite projection below `z`. -/
theorem central_summand_finiteProjection_witness
    (z : W.GNS →L[ℂ] W.GNS)
    (hz : IsCentralProjection W.localVonNeumannAlgebra z) (hz0 : z ≠ 0) :
    IsFiniteProjection W.localVonNeumannAlgebra (z * R.cornerProjection W) ∧
      z * R.cornerProjection W ≠ 0 ∧
      IsSubprojection (z * R.cornerProjection W) z :=
  (R.supportCornerConclusion_localVonNeumannAlgebra W).central_witness z hz hz0

/-- The FF23 central-summand theorem at the canonical GNS von Neumann algebra. -/
theorem central_summand_exists_nonzero_finiteProjection
    (z : W.GNS →L[ℂ] W.GNS)
    (hz : IsCentralProjection W.localVonNeumannAlgebra z) (hz0 : z ≠ 0) :
    ∃ e : W.GNS →L[ℂ] W.GNS,
      IsFiniteProjection W.localVonNeumannAlgebra e ∧ e ≠ 0 ∧ IsSubprojection e z :=
  (R.supportCornerConclusion_localVonNeumannAlgebra W).semifinite z hz hz0

/-- The canonical GNS von Neumann algebra is semifinite in the packet's
central-summand sense. -/
theorem isSemifinite_localVonNeumannAlgebra :
    IsSemifinite W.localVonNeumannAlgebra :=
  (R.supportCornerConclusion_localVonNeumannAlgebra W).semifinite

/-- No nonzero central summand of the canonical GNS algebra has no nonzero
finite subprojection. -/
theorem not_summandHasNoNonzeroFiniteProjection
    (z : W.GNS →L[ℂ] W.GNS)
    (hz : IsCentralProjection W.localVonNeumannAlgebra z) (hz0 : z ≠ 0) :
    ¬ SummandHasNoNonzeroFiniteProjection W.localVonNeumannAlgebra z :=
  not_summandHasNoNonzeroFiniteProjection_of_isSemifinite
    (R.isSemifinite_localVonNeumannAlgebra W) hz hz0

/-- The concrete corner is a nonzero finite projection of the canonical GNS
von Neumann algebra. -/
theorem cornerProjection_isFiniteProjection :
    IsFiniteProjection W.localVonNeumannAlgebra (R.cornerProjection W) ∧
      R.cornerProjection W ≠ 0 := by
  have hone : IsCentralProjection W.localVonNeumannAlgebra 1 :=
    ⟨⟨one_mem _, IsStarProjection.one _⟩, fun a _ => by rw [mul_one, one_mul]⟩
  have hne : (1 : W.GNS →L[ℂ] W.GNS) ≠ 0 := by
    intro h1
    refine R.gnsVector_ne_zero W ?_
    have : (1 : W.GNS →L[ℂ] W.GNS) W.gnsVector = (0 : W.GNS →L[ℂ] W.GNS) W.gnsVector := by
      rw [h1]
    simpa using this
  have h := R.central_summand_finiteProjection_witness W 1 hone hne
  rw [one_mul] at h
  exact ⟨h.1, h.2.1⟩

variable (M : VonNeumannAlgebra W.GNS)
variable (hM : ∀ (F : Finset Site) (x : finiteRegionQubitAlgebra F),
  W.gnsRepresentation (Q.embed F x) ∈ M)

include hM

/-- The same explicit witness for a supplied algebra identified with the local
bicommutant by containment and generation hypotheses. -/
theorem central_summand_finiteProjection_witness_of_generated
    (hgen : W.GeneratedByLocalAlgebra M)
    (z : W.GNS →L[ℂ] W.GNS) (hz : IsCentralProjection M z) (hz0 : z ≠ 0) :
    IsFiniteProjection M (z * R.cornerProjection W) ∧
      z * R.cornerProjection W ≠ 0 ∧ IsSubprojection (z * R.cornerProjection W) z :=
  (R.supportCornerConclusion W M hM hgen).central_witness z hz hz0

/-- Conditional central-summand semifiniteness for a general presented algebra. -/
theorem isSemifinite_of_generated (hgen : W.GeneratedByLocalAlgebra M) :
    IsSemifinite M :=
  (R.supportCornerConclusion W M hM hgen).semifinite

/-- Conditional absence-of-finiteness exclusion for a general presented algebra. -/
theorem not_summandHasNoNonzeroFiniteProjection_of_generated
    (hgen : W.GeneratedByLocalAlgebra M)
    (z : W.GNS →L[ℂ] W.GNS) (hz : IsCentralProjection M z) (hz0 : z ≠ 0) :
    ¬ SummandHasNoNonzeroFiniteProjection M z :=
  not_summandHasNoNonzeroFiniteProjection_of_isSemifinite
    (R.isSemifinite_of_generated W M hM hgen) hz hz0

end FiniteRangeStabilizerSystem

end FiniteRange

end FiniteFiber
