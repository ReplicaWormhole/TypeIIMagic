import FiniteFiber.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Decreasing local supports and their strong-limit projection

The manuscript starts from decreasing local support projections and takes their
strong limit.  Here ``strong'' is represented directly as pointwise norm
convergence on the Hilbert space.  The file proves the algebraic consequences
needed by the support-corner theorem: the limit lies in the concrete von
Neumann algebra, is a projection, and fixes any vector fixed by every local
support.

The strong limit is constructed from the closed union of the orthogonal
complements of the decreasing ranges.  The remaining work starts only after
this Hilbert-space limit has been obtained.
-/

namespace FiniteFiber

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pointwise strong-operator convergence of a sequence of bounded operators. -/
def StronglyTendsTo (p : ℕ → H →L[ℂ] H) (q : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun n => p n x) atTop (𝓝 (q x))

/-- A decreasing sequence of projections in a concrete von Neumann algebra. -/
structure DecreasingProjectionSequence (M : VonNeumannAlgebra H) (p : ℕ → H →L[ℂ] H) where
  projection : ∀ n : ℕ, IsProjectionIn M (p n)
  decreasing : ∀ n m : ℕ, n ≤ m → IsSubprojection (p m) (p n)

/--
The strong limit of a decreasing sequence of orthogonal projections, expressed
as the complement of the projection onto the closed union of the orthogonal
complements of its ranges.
-/
noncomputable def decreasingProjectionStrongLimit
    (p : ℕ → H →L[ℂ] H) : H →L[ℂ] H :=
  1 - ((⨆ n : ℕ, (p n).rangeᗮ).topologicalClosure).starProjection

/-- A decreasing sequence of projections converges strongly to `decreasingProjectionStrongLimit`. -/
theorem DecreasingProjectionSequence.stronglyTendsTo_decreasingProjectionStrongLimit
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) :
    StronglyTendsTo p (decreasingProjectionStrongLimit p) := by
  intro x
  let U : ℕ → Submodule ℂ H := fun n => (p n).rangeᗮ
  letI : ∀ n : ℕ, (p n).range.HasOrthogonalProjection := fun n =>
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
      ((D.projection n).2.isIdempotentElem)
  have hU : Monotone U := by
    intro n m hnm
    apply Submodule.orthogonal_le
    rintro y ⟨v, rfl⟩
    refine ⟨p m v, ?_⟩
    change (p n * p m) v = p m v
    exact congrArg (fun t : H →L[ℂ] H => t v) (D.decreasing n m hnm).2
  letI : ∀ n : ℕ, (U n).HasOrthogonalProjection := fun n => by
    dsimp [U]
    infer_instance
  have hp_apply (n : ℕ) : p n x = x - (U n).starProjection x := by
    letI : (p n).range.HasOrthogonalProjection :=
      ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
        ((D.projection n).2.isIdempotentElem)
    have hp_eq : p n = (p n).range.starProjection := by
      exact (isStarProjection_iff_eq_starProjection_range.mp (D.projection n).2).choose_spec
    calc
      p n x = (p n).range.starProjection x := congrArg (fun t : H →L[ℂ] H => t x) hp_eq
      _ = x - (x - (p n).range.starProjection x) := (sub_sub_cancel x _).symm
      _ = x - (U n).starProjection x := by
        dsimp [U]
        rw [Submodule.starProjection_orthogonal_val]
  have hlimit := Submodule.starProjection_tendsto_closure_iSup U hU x
  have hsub : Tendsto (fun n : ℕ => x - (U n).starProjection x) atTop
      (𝓝 (x - ((⨆ n : ℕ, U n).topologicalClosure).starProjection x)) :=
    tendsto_const_nhds.sub hlimit
  change Tendsto (fun n : ℕ => p n x) atTop
    (𝓝 (x - ((⨆ n : ℕ, U n).topologicalClosure).starProjection x))
  rw [show (fun n : ℕ => p n x) = fun n => x - (U n).starProjection x by
    funext n
    exact hp_apply n]
  exact hsub

/-- A pointwise strong limit of members of a concrete von Neumann algebra remains in it. -/
theorem stronglyTendsTo_mem
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (hp : StronglyTendsTo p q) (hmem : ∀ n : ℕ, p n ∈ M) :
    q ∈ M := by
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro y hy
  apply ContinuousLinearMap.ext
  intro x
  have hleft : Tendsto (fun n : ℕ => y (p n x)) atTop (𝓝 (y (q x))) :=
    (y.continuous.tendsto (q x)).comp (hp x)
  have hright : Tendsto (fun n : ℕ => p n (y x)) atTop (𝓝 (q (y x))) :=
    hp (y x)
  have heventual : (fun n : ℕ => y (p n x)) =ᶠ[atTop]
      fun n : ℕ => p n (y x) := by
    filter_upwards [] with n
    have hcomm : p n * y = y * p n :=
      VonNeumannAlgebra.mem_commutant_iff.mp hy (p n) (hmem n)
    change (y * p n) x = (p n * y) x
    rw [hcomm]
  exact tendsto_nhds_unique (hleft.congr' heventual) hright

/-- Every finite-stage projection fixes the strong-limit range. -/
theorem DecreasingProjectionSequence.mul_strongLimit_eq
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q) (n : ℕ) :
    p n * q = q := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft : Tendsto (fun m : ℕ => p n (p m x)) atTop (𝓝 (p n (q x))) :=
    ((p n).continuous.tendsto (q x)).comp (hp x)
  have hright : Tendsto (fun m : ℕ => p m x) atTop (𝓝 (q x)) := hp x
  have heventual : (fun m : ℕ => p n (p m x)) =ᶠ[atTop]
      fun m : ℕ => p m x := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hsub : IsSubprojection (p m) (p n) := D.decreasing n m hnm
    change (p n * p m) x = p m x
    rw [hsub.2]
  change p n (q x) = q x
  exact tendsto_nhds_unique (hleft.congr' heventual) hright

/-- The pointwise strong limit of a decreasing sequence of projections is idempotent. -/
theorem DecreasingProjectionSequence.strongLimit_isIdempotent
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q) :
    q * q = q := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft : Tendsto (fun n : ℕ => p n (q x)) atTop (𝓝 (q (q x))) :=
    hp (q x)
  have heventual : (fun n : ℕ => p n (q x)) =ᶠ[atTop]
      fun _ : ℕ => q x := by
    filter_upwards [] with n
    have hfix := congrArg (fun t : H →L[ℂ] H => t x) (D.mul_strongLimit_eq hp n)
    exact hfix
  have hright : Tendsto (fun _ : ℕ => q x) atTop (𝓝 (q x)) :=
    tendsto_const_nhds
  change q (q x) = q x
  exact tendsto_nhds_unique (hleft.congr' heventual) hright

/-- The pointwise strong limit of self-adjoint projections is self-adjoint. -/
theorem DecreasingProjectionSequence.strongLimit_isSelfAdjoint
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q) :
    IsSelfAdjoint q := by
  change star q = q
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply (ext_inner_left (𝕜 := ℂ))
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hleft : Tendsto (fun n : ℕ => ⟪p n y, x⟫_ℂ) atTop (𝓝 ⟪q y, x⟫_ℂ) :=
    ((continuous_id.inner continuous_const).tendsto (q y)).comp (hp y)
  have hright : Tendsto (fun n : ℕ => ⟪y, p n x⟫_ℂ) atTop (𝓝 ⟪y, q x⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto (q x)).comp (hp x)
  have heventual : (fun n : ℕ => ⟪p n y, x⟫_ℂ) =ᶠ[atTop]
      fun n : ℕ => ⟪y, p n x⟫_ℂ := by
    filter_upwards [] with n
    have hself : star (p n) = p n := D.projection n |>.2.isSelfAdjoint.star_eq
    calc
      ⟪p n y, x⟫_ℂ = ⟪y, (star (p n)) x⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪y, p n x⟫_ℂ := by rw [hself]
  exact tendsto_nhds_unique (hleft.congr' heventual) hright

/-- The strong limit constructed from decreasing local supports is a projection in the algebra. -/
theorem DecreasingProjectionSequence.strongLimit_isProjectionIn
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) (hp : StronglyTendsTo p q) :
    IsProjectionIn M q := by
  refine ⟨stronglyTendsTo_mem hp fun n => (D.projection n).1, ?_⟩
  exact ⟨D.strongLimit_isIdempotent hp, D.strongLimit_isSelfAdjoint hp⟩

/-- The canonical decreasing-projection strong limit is a projection in the algebra. -/
theorem DecreasingProjectionSequence.decreasingProjectionStrongLimit_isProjectionIn
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H}
    (D : DecreasingProjectionSequence M p) :
    IsProjectionIn M (decreasingProjectionStrongLimit p) :=
  D.strongLimit_isProjectionIn D.stronglyTendsTo_decreasingProjectionStrongLimit

omit [CompleteSpace H] in
/-- If every local support fixes a vector, then so does the strong-limit support. -/
lemma stronglyTendsTo_fixes
    {p : ℕ → H →L[ℂ] H} {q : H →L[ℂ] H} {xi : H}
    (hp : StronglyTendsTo p q)
    (hfix : ∀ n : ℕ, p n xi = xi) :
    q xi = xi := by
  have hleft : Tendsto (fun n : ℕ => p n xi) atTop (𝓝 (q xi)) := hp xi
  have heventual : (fun n : ℕ => p n xi) =ᶠ[atTop] fun _ : ℕ => xi := by
    filter_upwards [] with n
    exact hfix n
  have hright : Tendsto (fun _ : ℕ => xi) atTop (𝓝 xi) := tendsto_const_nhds
  exact tendsto_nhds_unique (hleft.congr' heventual) hright

/-- The canonical decreasing-projection strong limit fixes every common fixed vector. -/
theorem DecreasingProjectionSequence.decreasingProjectionStrongLimit_fixes
    {M : VonNeumannAlgebra H} {p : ℕ → H →L[ℂ] H} {xi : H}
    (D : DecreasingProjectionSequence M p)
    (hfix : ∀ n : ℕ, p n xi = xi) :
    decreasingProjectionStrongLimit p xi = xi :=
  stronglyTendsTo_fixes D.stronglyTendsTo_decreasingProjectionStrongLimit hfix

end FiniteFiber
