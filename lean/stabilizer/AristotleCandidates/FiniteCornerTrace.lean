import Mathlib
import AristotleCandidates.CenterFiniteProjectionCore
import AristotleCandidates.GeneralLatticeProjectionTower
import AristotleCandidates.ConcreteQuasilocalCStarModel
import AristotleCandidates.DensityPartialTrace

/-!
# P49 — finite-stage trace cyclicity and the compressed quasi-local corner

**Source basis:** `main.tex:1133-1261` (equation `eq:local_traciality`, the
strong-limit passage after it, Lemma `lem:cstar_trace`, and the *statement* of
the compressed functional `tau_q(x) = <Omega| x |Omega>`).

**Plan alignment.**  Package `P49`, lane `G`.  Predecessors used: `P47`
(`CenterFiniteProjectionCore`) and `P48` (`GeneralLatticeProjectionTower`),
both already integrated.  The gate discharged here is *finite-stage cyclicity*
of the compressed vector functional together with its *compatible limit* on the
compressed quasi-local C⋆-algebra, keeping the finite codespace density data
explicit.

**Forbidden downstream claims, not made anywhere in this file.**  No normality,
no faithfulness on the von Neumann corner, no fullness of `q`, no finiteness of
`q`, no global trace or weight on `M_Gamma`, and no type-III exclusion.  In
particular nothing below mentions Kaplansky density, the double commutant, or
`q M_Gamma q`: the tracial identity is proved exactly on the *norm-closed*
compressed quasi-local C⋆-algebra, which is the furthest the existing
completion interfaces support.

## What is constructed and proved

### The compressed functional

* `tauVec Ω : (H →L[ℂ] H) →L[ℂ] ℂ`, `x ↦ ⟪Ω, x Ω⟫` — the vector functional
  `tau_q` of the manuscript, packaged as a *continuous* linear functional, so
  the manuscript's "`tau_q` is bounded, hence norm continuous" step is a
  structural fact rather than an assumption.
* `compressL q`, `x ↦ q x q` — the compression map, again continuous linear.
* `cornerTau q Ω = tauVec Ω ∘ compressL q` — the compressed functional, with
  `cornerTau_star_mul_self` (positivity) and `cornerTau_one` (normalization,
  under `q Ω = Ω`, `‖Ω‖ = 1`).
* `compressL_mem_corner` — the compression lands in the corner `q M q` of P47.
  This is the only P47 interface used, and no property of that corner is
  invoked.

### Explicit finite codespace density data

* `stabilizerCodeDensity` — the finite codespace density matrix
  `rho = (trace P)⁻¹ • P` attached to the finite group-average code projection
  `P` of `AristotleCandidates.groupAverage`, with
  `trace_stabilizerCodeDensity` (`Tr rho = 1`),
  `posSemidef_stabilizerCodeDensity` (`rho ≥ 0`) and
  `stabilizerCodeDensity_eq_smul` (`rho = (|G| / dim) • P`, the manuscript's
  normalization `rho_{Gamma_n} = |G_{S,Gamma_n}| 2^{-|Gamma_n|} P_{Gamma_n}`).
* `trace_density_sandwich_comm` — the finite-dimensional cyclicity
  `Tr(rho P a P b P) = Tr(rho P b P a P)` for `rho = c • P` and `P` idempotent.
  This is exactly `main.tex` eq. `eq:local_traciality`.

### The finite-stage system and its limit

* `FiniteCodespaceSystem Ω ι` — the explicit finite-stage data: stage star
  representations `pi n` of the finite matrix algebras, idempotent hermitian
  code projections `codeProj n`, densities `density n = weight n • codeProj n`
  of trace one, and the vector-state identity
  `⟪Ω, pi n x Ω⟫ = Tr(density n * x)`.
* `FiniteCodespaceSystem.stageProj` (`p n`), proved to be a star projection,
  with `stageProj_apply_self` (`p n Ω = Ω`, the finite-stage form of the
  manuscript's `‖(1 - p_n)Ω‖ = 0` computation) and `stage_cyclic`
  (finite-stage cyclicity of the vector state).
* `CompatibleFiniteCodespaceSystem` — the same data with stage inclusions, from
  which `trace_density_incl` (the *functional* form of the density
  compatibility `rho_n = Tr_{Gamma_{n+1} \ Gamma_n} rho_{n+1}`) and
  `range_pi_monotone` are derived.
* `tendsto_tauVec_sandwich` — the strong-limit passage
  `⟪Ω, p_n a p_n b p_n Ω⟫ → ⟪Ω, q a q b q Ω⟫`.  The manuscript invokes joint
  strong continuity of multiplication on bounded sets; because `q Ω = Ω` the
  same conclusion is obtained here from `p_n → q` strongly alone, which is a
  strictly weaker input.
* `CornerTracialOn` and `CornerTracialOn.closure` — the norm-density extension
  (`main.tex` Lemma `lem:cstar_trace`).
* `cornerTracialOn_quasilocalCStarAlgebra` — the tracial identity on the
  concrete quasi-local C⋆-algebra of `ConcreteQuasilocalCStarModel`.
* `CompatibleFiniteCodespaceSystem.finite_corner_trace` — the packaged
  conditional theorem.
* `qubitPureMixedDensity_trace_succEmbedding` — a check that the project's own
  explicit finite-stage densities satisfy the compatibility shape used by
  `CompatibleFiniteCodespaceSystem`.
* `sanitySystem`, `sanitySystem_isDecreasingProjTower` — a concrete model
  satisfying every field and premise, so the conditional theorem is not
  vacuous.

## Auxiliary assumptions (all explicit Lean fields or premises, no axioms)

1. `FiniteCodespaceSystem`: the finite-stage star representations `pi n`, the
   idempotent hermitian matrices `codeProj n`, the *scalar-multiple* form
   `density n = weight n • codeProj n` of the finite codespace densities, their
   normalization `Tr(density n) = 1`, and the vector-state identity
   `⟪Ω, pi n x Ω⟫ = Tr(density n * x)`.  The last field is the GNS input; it is
   assumed, not constructed.
2. `CompatibleFiniteCodespaceSystem`: stage inclusions `incl n` with
   `pi (n+1) ∘ incl n = pi n`.
3. Where the limit is taken: `IsDecreasingProjTower` for the stage projections
   (`main.tex` Lemma `lema:proj_inequality`), supplied as a premise since it is
   not implied by the density fields alone.
4. For the C⋆-level statement: a norm-density premise
   `(A : Set _) ⊆ closure (⋃ n, Set.range (pi n))`, i.e. the compressed
   quasi-local algebra is the norm closure of the finite-stage operators.

Everything else — in particular `‖Ω‖ = 1`, `p n Ω = Ω`, `q Ω = Ω`, positivity
and normalization of the compressed functional — is *derived*.
-/

namespace AristotleCandidates
namespace FiniteCornerTrace

open Filter Topology ProjectionTower
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §1  The compressed vector functional `tau_q` -/

/-- The vector functional `x ↦ ⟪Ω, x Ω⟫` of the manuscript, as a *continuous*
linear functional on the bounded operators.  Boundedness of `tau_q` — used in
the manuscript to pass to norm limits — is therefore structural here. -/
noncomputable def tauVec (Ω : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ H Ω)

omit [CompleteSpace H] in
@[simp] theorem tauVec_apply (Ω : H) (x : H →L[ℂ] H) : tauVec Ω x = ⟪Ω, x Ω⟫_ℂ := rfl

/-- The compression map `x ↦ q x q`, as a continuous linear map. -/
noncomputable def compressL (q : H →L[ℂ] H) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) q q

@[simp] theorem compressL_apply (q x : H →L[ℂ] H) : compressL q x = q * x * q := rfl

/-- The **compressed functional** `tau_q(x) = ⟪Ω, q x q Ω⟫`. -/
noncomputable def cornerTau (q : H →L[ℂ] H) (Ω : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (tauVec Ω).comp (compressL q)

@[simp] theorem cornerTau_apply (q : H →L[ℂ] H) (Ω : H) (x : H →L[ℂ] H) :
    cornerTau q Ω x = ⟪Ω, (q * x * q) Ω⟫_ℂ := rfl

/-- `tau_q` is positive on squares: `tau_q (x* x) = ‖x (q Ω)‖ ^ 2 ≥ 0`. -/
theorem cornerTau_star_mul_self {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) (Ω : H)
    (x : H →L[ℂ] H) : cornerTau q Ω (star x * x) = (‖x (q Ω)‖ : ℂ) ^ 2 := by
  have h : ((q * (star x * x) * q) Ω) = q ((star x) (x (q Ω))) := rfl
  rw [cornerTau_apply, h, ← inner_isSelfAdjoint hq Ω ((star x) (x (q Ω)))]
  have hx : ⟪q Ω, (star x) (x (q Ω))⟫_ℂ = ⟪x (q Ω), x (q Ω)⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [hx, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem cornerTau_nonneg {q : H →L[ℂ] H} (hq : IsSelfAdjoint q) (Ω : H) (x : H →L[ℂ] H) :
    0 ≤ (cornerTau q Ω (star x * x)).re := by
  rw [cornerTau_star_mul_self hq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- Normalization: if `q Ω = Ω` and `Ω` is a unit vector then `tau_q 1 = 1`. -/
theorem cornerTau_one {q : H →L[ℂ] H} {Ω : H} (hqΩ : q Ω = Ω) (hΩ : ⟪Ω, Ω⟫_ℂ = 1) :
    cornerTau q Ω 1 = 1 := by
  have h : ((q * (1 : H →L[ℂ] H) * q) Ω) = Ω := by
    rw [mul_one]
    show q (q Ω) = Ω
    rw [hqΩ, hqΩ]
  rw [cornerTau_apply, h, hΩ]

/-- The compression map lands in the P47 corner: if `q` is a self-adjoint
idempotent of a concrete von Neumann algebra `M`, then `q x q` belongs to the
corner `q M q` for every `x ∈ M`.  This is the only interface used from P47;
no finiteness, normality or comparison statement about the corner is invoked. -/
theorem compressL_mem_corner (M : VonNeumannAlgebra H) {q : H →L[ℂ] H}
    (hq : IsSelfAdjoint q) (hqidem : q * q = q) (hqM : q ∈ M) {x : H →L[ℂ] H}
    (hx : x ∈ M) : compressL q x ∈ VonNeumannAlgebra.corner M hq := by
  refine ⟨mul_mem (mul_mem hqM hx) hqM, ?_, ?_⟩
  · show q * (q * x * q) = q * x * q
    calc q * (q * x * q) = (q * q) * x * q := by noncomm_ring
      _ = q * x * q := by rw [hqidem]
  · show (q * x * q) * q = q * x * q
    calc (q * x * q) * q = q * x * (q * q) := by noncomm_ring
      _ = q * x * q := by rw [hqidem]

/-! ## §2  Finite-dimensional cyclicity of the codespace density -/

section FiniteTrace

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **`main.tex` eq. `eq:local_traciality`.**  For a density matrix which is a
scalar multiple of an idempotent `P` (the finite codespace normalization
`rho = |G| 2^{-|Gamma|} P`), the finite matrix trace is cyclic on the
`P`-compressions. -/
theorem trace_density_sandwich_comm (P : Matrix ι ι ℂ) (hP : P * P = P) (c : ℂ)
    (a b : Matrix ι ι ℂ) :
    ((c • P) * (P * a * P * b * P)).trace = ((c • P) * (P * b * P * a * P)).trace := by
  have key : ∀ u v : Matrix ι ι ℂ,
      (c • P) * (P * u * P * v * P) = c • ((P * u * P) * (P * v * P)) := by
    intro u v
    rw [Matrix.smul_mul]
    congr 1
    calc P * (P * u * P * v * P) = (P * P) * u * P * v * P := by noncomm_ring
      _ = P * u * P * v * P := by rw [hP]
      _ = P * u * (P * P) * v * P := by rw [hP]
      _ = (P * u * P) * (P * v * P) := by noncomm_ring
  rw [key a b, key b a, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_mul_comm (P * a * P) (P * b * P)]

/-! ### The explicit finite codespace density matrix -/

variable {G : Type*} [Group G] [Fintype G]

/-- The **finite codespace density matrix** attached to a finite stabilizer
group `G` acting by `U`: the normalized code projection `(Tr P)⁻¹ • P`, where
`P = groupAverage U` is the group-average code projection. -/
noncomputable def stabilizerCodeDensity (U : G →* Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((groupAverage U).trace)⁻¹ • groupAverage U

theorem stabilizerCodeDensity_eq_smul (U : G →* Matrix ι ι ℂ) :
    stabilizerCodeDensity U = (((groupAverage U).trace)⁻¹ : ℂ) • groupAverage U := rfl

/-- The finite codespace density matrix has trace one. -/
theorem trace_stabilizerCodeDensity (U : G →* Matrix ι ι ℂ)
    (h : (groupAverage U).trace ≠ 0) : (stabilizerCodeDensity U).trace = 1 := by
  rw [stabilizerCodeDensity, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ h]

/-- **The manuscript's normalization constant.**  If the normalized matrix trace
annihilates every nontrivial group element, then the trace of the code
projection is `dim / |G|`, so the density matrix is
`(|G| / dim) • P` — the finite-stage factor `|G_{S,Gamma_n}| / 2^{|Gamma_n|}`. -/
theorem trace_groupAverage_eq (U : G →* Matrix ι ι ℂ) [Nonempty ι]
    (hU : ∀ g : G, g ≠ 1 → (U g).trace = 0) :
    (groupAverage U).trace = (Fintype.card ι : ℂ) / (Fintype.card G : ℂ) := by
  classical
  have htr : ((Fintype.card ι : ℂ)⁻¹ • (Matrix.traceLinearMap ι ℂ ℂ)) (1 : Matrix ι ι ℂ) = 1 := by
    have : (Matrix.traceLinearMap ι ℂ ℂ) (1 : Matrix ι ι ℂ) = (Fintype.card ι : ℂ) := by
      simp [Matrix.trace_one]
    rw [LinearMap.smul_apply, this, smul_eq_mul]
    field_simp
  have hann : ∀ g : G, g ≠ 1 →
      ((Fintype.card ι : ℂ)⁻¹ • (Matrix.traceLinearMap ι ℂ ℂ)) (U g) = 0 := by
    intro g hg
    simp [hU g hg]
  have hkey := groupAverage_trace U
    ((Fintype.card ι : ℂ)⁻¹ • (Matrix.traceLinearMap ι ℂ ℂ)) htr hann
  simp only [LinearMap.smul_apply, smul_eq_mul, Matrix.traceLinearMap_apply] at hkey
  have hι : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 Fintype.card_ne_zero
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 Fintype.card_ne_zero
  field_simp at hkey
  rw [eq_div_iff hG]
  linear_combination hkey

omit [DecidableEq ι] in
/-- The finite codespace density matrix is positive semidefinite: it is a
nonnegative multiple of a hermitian idempotent. -/
theorem posSemidef_smul_of_isIdempotent {P : Matrix ι ι ℂ} (hP : P * P = P)
    (hPh : P.IsHermitian) {c : ℝ} (hc : 0 ≤ c) : ((c : ℂ) • P).PosSemidef := by
  have hPP : P = P.conjTranspose * P := by rw [hPh]; exact hP.symm
  have hps : P.PosSemidef := by rw [hPP]; exact Matrix.posSemidef_conjTranspose_mul_self P
  exact hps.smul (by simpa using hc)

end FiniteTrace

/-! ### The project's explicit finite densities satisfy the compatibility shape

The compatibility field used in §3 below has the shape
`Tr(rho_{n+1} * incl a) = Tr(rho_n * a)`.  The following theorem checks that
the project's own explicit finite-stage densities
`StabilizerHyperfinite.qubitPureMixedDensity` do satisfy it, along the dyadic
tower's identity-qubit inclusion, using the ordinary (unnormalized) trace and
the one-qubit partial trace of `AristotleCandidates.DensityPartialTrace`.  This
is the manuscript's `rho_{Gamma_n} = Tr_{Gamma_{n+1} \ Gamma_n} rho_{Gamma_{n+1}}`
in functional form for that concrete family. -/

section ExplicitDensities

open StabilizerHyperfinite

/-- The explicit finite-stage densities of the project are compatible with the
identity-qubit inclusion: pairing `rho_{n+1}` with an observable coming from
stage `n` gives the stage-`n` pairing. -/
theorem qubitPureMixedDensity_trace_succEmbedding (pure : ℕ → Bool) (n : ℕ)
    (a : QubitTensorPower n) :
    qubitTensorFullTrace (n + 1)
        (qubitPureMixedDensity pure (n + 1) * qubitTensorPowerSuccEmbedding n a)
      = qubitTensorFullTrace n (qubitPureMixedDensity pure n * a) := by
  have hmul : (qubitPureMixedDensity pure (n + 1) *
      qubitTensorPowerSuccEmbedding n a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) =
      qubitElementaryTensor n (qubitDensityFactor pure n)
        (qubitPureMixedDensity pure n * a) := by
    rw [qubitPureMixedDensity_succ_eq_elementaryTensor]
    refine Matrix.ext fun i j => ?_
    show ∑ k : Fin 2, (qubitDensityFactor pure n i k • qubitPureMixedDensity pure n) *
        (Matrix.scalar (Fin 2) a) k j = _
    rw [qubitElementaryTensor_apply]
    fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  calc qubitTensorFullTrace (n + 1)
        (qubitPureMixedDensity pure (n + 1) * qubitTensorPowerSuccEmbedding n a)
      = qubitTensorFullTrace n (qubitPartialTrace n
          ((qubitPureMixedDensity pure (n + 1) * qubitTensorPowerSuccEmbedding n a :
            Matrix (Fin 2) (Fin 2) (QubitTensorPower n)))) :=
        matrixTraceOver_eq_of_qubitPartialTrace n (qubitTensorFullTrace n) _
    _ = qubitTensorFullTrace n (qubitPureMixedDensity pure n * a) := by
        rw [hmul, qubitPartialTrace_elementaryTensor, trace_qubitDensityFactor, one_smul]

end ExplicitDensities

/-! ## §3  The finite-stage system with explicit codespace densities -/

section System

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **Explicit finite-stage codespace data.**

The fields record exactly the manuscript's finite-stage input at stage `n`:
a star representation `pi n` of the finite local matrix algebra on the GNS
space, the local code projection `codeProj n` (an hermitian idempotent), the
finite codespace density `density n = weight n • codeProj n` of trace one, and
the identity `⟪Ω, pi n x Ω⟫ = Tr(density n x)` expressing the GNS vector state
by that density.

No topology, normality, or von Neumann-algebraic statement is part of this
structure. -/
structure FiniteCodespaceSystem (Ω : H) (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] where
  /-- The finite-stage star representation on the GNS Hilbert space. -/
  pi : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- The local code projection `P_{Gamma_n}` as a matrix. -/
  codeProj : ∀ n, Matrix (ι n) (ι n) ℂ
  /-- `P_{Gamma_n}` is idempotent. -/
  codeProj_mul_self : ∀ n, codeProj n * codeProj n = codeProj n
  /-- `P_{Gamma_n}` is hermitian. -/
  codeProj_isHermitian : ∀ n, (codeProj n).IsHermitian
  /-- The explicit normalization factor `|G_{S,Gamma_n}| / 2^{|Gamma_n|}`. -/
  weight : ℕ → ℂ
  /-- The finite codespace density matrix `rho_{Gamma_n}`. -/
  density : ∀ n, Matrix (ι n) (ι n) ℂ
  /-- The density is the normalized code projection. -/
  density_eq : ∀ n, density n = weight n • codeProj n
  /-- The density is normalized. -/
  trace_density : ∀ n, (density n).trace = 1
  /-- The GNS vector state is given by the finite density matrix. -/
  vector_state : ∀ n x, ⟪Ω, (pi n x) Ω⟫_ℂ = (density n * x).trace

namespace FiniteCodespaceSystem

variable {Ω : H} (D : FiniteCodespaceSystem Ω ι)

/-- The local code projection as an operator, `p_n = pi_n (P_{Gamma_n})`. -/
noncomputable def stageProj (n : ℕ) : H →L[ℂ] H := D.pi n (D.codeProj n)

theorem stageProj_isStarProjection (n : ℕ) : IsStarProjection (D.stageProj n) := by
  constructor
  · show D.stageProj n * D.stageProj n = D.stageProj n
    rw [stageProj, ← map_mul, D.codeProj_mul_self]
  · show star (D.stageProj n) = D.stageProj n
    rw [stageProj, ← map_star]
    congr 1
    exact D.codeProj_isHermitian n

include D in
/-- `Ω` is a unit vector: this follows from the normalization of the densities. -/
theorem inner_self_eq_one : ⟪Ω, Ω⟫_ℂ = 1 := by
  have h := D.vector_state 0 1
  rw [map_one] at h
  simpa [D.trace_density 0] using h

include D in
theorem norm_eq_one : ‖Ω‖ = 1 := by
  have h := D.inner_self_eq_one
  rw [inner_self_eq_norm_sq_to_K] at h
  have h1 : ((‖Ω‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; simpa using h
  have h2 : ‖Ω‖ ^ 2 = 1 := by exact_mod_cast h1
  nlinarith [norm_nonneg Ω]

/-- **`main.tex`: `omega(P_n) = Tr(rho_n P_n) = Tr(rho_n) = 1`.** -/
theorem vector_state_stageProj (n : ℕ) : ⟪Ω, (D.stageProj n) Ω⟫_ℂ = 1 := by
  rw [stageProj, D.vector_state n (D.codeProj n)]
  have : D.density n * D.codeProj n = D.density n := by
    rw [D.density_eq n, Matrix.smul_mul, D.codeProj_mul_self]
  rw [this, D.trace_density n]

/-- **Finite-stage form of the manuscript's `‖(1 - p_n)Omega‖ = 0` computation.**
The GNS vector is fixed by every finite-stage code projection. -/
theorem stageProj_apply_self (n : ℕ) : D.stageProj n Ω = Ω := by
  have hsa : IsSelfAdjoint (D.stageProj n) := (D.stageProj_isStarProjection n).isSelfAdjoint
  have hid : D.stageProj n (D.stageProj n Ω) = D.stageProj n Ω := by
    have := (D.stageProj_isStarProjection n).isIdempotentElem
    calc D.stageProj n (D.stageProj n Ω)
        = (D.stageProj n * D.stageProj n) Ω := rfl
      _ = D.stageProj n Ω := by rw [this]
  have h1 : ⟪Ω, D.stageProj n Ω⟫_ℂ = 1 := D.vector_state_stageProj n
  have h2 : ⟪D.stageProj n Ω, Ω⟫_ℂ = 1 := by
    rw [inner_isSelfAdjoint hsa, h1]
  have h3 : ⟪D.stageProj n Ω, D.stageProj n Ω⟫_ℂ = 1 := by
    rw [inner_isSelfAdjoint hsa, hid, h1]
  have h0 : ⟪Ω - D.stageProj n Ω, Ω - D.stageProj n Ω⟫_ℂ = 0 := by
    rw [inner_sub_sub_self, D.inner_self_eq_one, h1, h2, h3]
    ring
  have := inner_self_eq_zero.1 h0
  have hz : Ω - D.stageProj n Ω = 0 := this
  linear_combination (norm := module) -hz

/-- **Finite-stage cyclicity** (`main.tex` eqs. `eq:local_state` and
`eq:local_traciality`): the GNS vector state is cyclic on the `p_n`-compressions
of stage-`n` local operators. -/
theorem stage_cyclic (n : ℕ) (a b : Matrix (ι n) (ι n) ℂ) :
    tauVec Ω (D.stageProj n * D.pi n a * D.stageProj n * D.pi n b * D.stageProj n) =
      tauVec Ω (D.stageProj n * D.pi n b * D.stageProj n * D.pi n a * D.stageProj n) := by
  have hop : ∀ u v : Matrix (ι n) (ι n) ℂ,
      D.stageProj n * D.pi n u * D.stageProj n * D.pi n v * D.stageProj n =
        D.pi n (D.codeProj n * u * D.codeProj n * v * D.codeProj n) := by
    intro u v
    simp only [stageProj, map_mul]
  rw [hop a b, hop b a, tauVec_apply, tauVec_apply, D.vector_state, D.vector_state,
    D.density_eq n]
  exact trace_density_sandwich_comm _ (D.codeProj_mul_self n) _ a b

end FiniteCodespaceSystem

/-- **Compatible finite-stage codespace data**: the finite-stage system together
with the stage inclusions intertwining the representations. -/
structure CompatibleFiniteCodespaceSystem (Ω : H) (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    extends FiniteCodespaceSystem Ω ι where
  /-- The local inclusion `A_{Gamma_n} → A_{Gamma_{n+1}}`. -/
  incl : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] Matrix (ι (n + 1)) (ι (n + 1)) ℂ
  /-- The stage representations are compatible with the inclusions. -/
  pi_incl : ∀ n x, pi (n + 1) (incl n x) = pi n x

namespace CompatibleFiniteCodespaceSystem

variable {Ω : H} (D : CompatibleFiniteCodespaceSystem Ω ι)

/-- **Density compatibility** in its functional form: the manuscript's
`rho_{Gamma_n} = Tr_{Gamma_{n+1} \ Gamma_n} rho_{Gamma_{n+1}}` says exactly that
the stage functionals agree along the inclusions. -/
theorem trace_density_incl (n : ℕ) (x : Matrix (ι n) (ι n) ℂ) :
    (D.density (n + 1) * D.incl n x).trace = (D.density n * x).trace := by
  rw [← D.vector_state (n + 1) (D.incl n x), ← D.vector_state n x, D.pi_incl n x]

/-- The finite-stage operator ranges increase. -/
theorem range_pi_monotone : Monotone fun n => Set.range (D.pi n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨D.incl n x, D.pi_incl n x⟩

end CompatibleFiniteCodespaceSystem

end System

/-! ## §4  Passing the finite-stage identity to the limit projection `q` -/

section Limit

variable {p : ℕ → H →L[ℂ] H} {Ω : H}

/-- If every `p n` fixes `Ω`, so does the limit projection `q`. -/
theorem limitProj_apply_self (hΩ : ∀ n, p n Ω = Ω) : limitProj p Ω = Ω :=
  Submodule.starProjection_eq_self_iff.2 (mem_limitSpace.2 hΩ)

omit [CompleteSpace H] in
/-- Compression of a product: `(q a q)(q b q) = q a q b q` for an idempotent `q`. -/
theorem compress_mul_compress {q : H →L[ℂ] H} (hq : q * q = q) (a b : H →L[ℂ] H) :
    (q * a * q) * (q * b * q) = q * a * q * b * q := by
  calc (q * a * q) * (q * b * q) = q * a * (q * q) * b * q := by noncomm_ring
    _ = q * a * q * b * q := by rw [hq]

/-- The finite-stage sandwich functional, rewritten as a single inner product. -/
theorem tauVec_sandwich_eq (hp : IsDecreasingProjTower p) (hΩ : ∀ n, p n Ω = Ω)
    (a b : H →L[ℂ] H) (n : ℕ) :
    tauVec Ω (p n * a * p n * b * p n) = ⟪Ω, a (p n (b Ω))⟫_ℂ := by
  have hsa : IsSelfAdjoint (p n) := (hp.isStarProjection n).isSelfAdjoint
  have h : (p n * a * p n * b * p n) Ω = p n (a (p n (b Ω))) := by
    show p n (a (p n (b (p n Ω)))) = _
    rw [hΩ n]
  rw [tauVec_apply, h, ← inner_isSelfAdjoint hsa, hΩ n]

/-- **The strong-limit passage.**  `⟪Ω, p_n a p_n b p_n Ω⟫ → ⟪Ω, q a q b q Ω⟫`.

The manuscript argues via joint strong continuity of multiplication on bounded
sets; since `q Ω = Ω`, strong convergence `p_n → q` alone suffices. -/
theorem tendsto_tauVec_sandwich (hp : IsDecreasingProjTower p) (hΩ : ∀ n, p n Ω = Ω)
    (a b : H →L[ℂ] H) :
    Tendsto (fun n => tauVec Ω (p n * a * p n * b * p n)) atTop
      (𝓝 (tauVec Ω (limitProj p * a * limitProj p * b * limitProj p))) := by
  have hq : limitProj p Ω = Ω := limitProj_apply_self hΩ
  have hqsa : IsSelfAdjoint (limitProj p) := (limitProj_isStarProjection p).isSelfAdjoint
  have hlim : tauVec Ω (limitProj p * a * limitProj p * b * limitProj p) =
      ⟪Ω, a (limitProj p (b Ω))⟫_ℂ := by
    have h : (limitProj p * a * limitProj p * b * limitProj p) Ω =
        limitProj p (a (limitProj p (b Ω))) := by
      show limitProj p (a (limitProj p (b (limitProj p Ω)))) = _
      rw [hq]
    rw [tauVec_apply, h, ← inner_isSelfAdjoint hqsa, hq]
  rw [hlim]
  have hcong : (fun n => tauVec Ω (p n * a * p n * b * p n)) =
      fun n => ⟪Ω, a (p n (b Ω))⟫_ℂ :=
    funext fun n => tauVec_sandwich_eq hp hΩ a b n
  rw [hcong]
  have hcont : Continuous fun y : H => ⟪Ω, a y⟫_ℂ :=
    (innerSL ℂ Ω).continuous.comp a.continuous
  exact (hcont.tendsto _).comp (hp.tendsto_limitProj (b Ω))

/-- **Cyclicity on the corner from eventual finite-stage cyclicity.** -/
theorem cornerTau_cyclic_of_stage (hp : IsDecreasingProjTower p) (hΩ : ∀ n, p n Ω = Ω)
    {a b : H →L[ℂ] H} {m : ℕ}
    (h : ∀ n, m ≤ n → tauVec Ω (p n * a * p n * b * p n) =
      tauVec Ω (p n * b * p n * a * p n)) :
    tauVec Ω ((limitProj p * a * limitProj p) * (limitProj p * b * limitProj p)) =
      tauVec Ω ((limitProj p * b * limitProj p) * (limitProj p * a * limitProj p)) := by
  have hqidem : limitProj p * limitProj p = limitProj p :=
    (limitProj_isStarProjection p).isIdempotentElem
  rw [compress_mul_compress hqidem, compress_mul_compress hqidem]
  have h1 := tendsto_tauVec_sandwich hp hΩ a b
  have h2 := tendsto_tauVec_sandwich hp hΩ b a
  have heq : (fun n => tauVec Ω (p n * a * p n * b * p n)) =ᶠ[atTop]
      fun n => tauVec Ω (p n * b * p n * a * p n) :=
    eventually_atTop.2 ⟨m, h⟩
  exact tendsto_nhds_unique (h1.congr' heq) h2

end Limit

/-! ## §5  The tracial identity on a set of operators, and its norm closure -/

section Closure

/-- Density transfer for a continuous test function on a product: two continuous
functions agreeing on `S ×ˢ S` agree on `closure S ×ˢ closure S`. -/
theorem eqOn_closure_prod {A : Type*} [TopologicalSpace A] {S : Set A}
    {F G : A × A → ℂ} (hF : Continuous F) (hG : Continuous G) (hEq : Set.EqOn F G (S ×ˢ S)) :
    Set.EqOn F G (closure S ×ˢ closure S) := by
  have hcl := hEq.closure hF hG
  rwa [closure_prod_eq] at hcl

variable (q : H →L[ℂ] H) (Ω : H)

/-- `tau_q` is cyclic on the compressions of the operators in `S`. -/
def CornerTracialOn (S : Set (H →L[ℂ] H)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    tauVec Ω ((q * a * q) * (q * b * q)) = tauVec Ω ((q * b * q) * (q * a * q))

variable {q Ω}

omit [CompleteSpace H] in
theorem CornerTracialOn.mono {S T : Set (H →L[ℂ] H)} (h : CornerTracialOn q Ω T) (hST : S ⊆ T) :
    CornerTracialOn q Ω S := fun a ha b hb => h a (hST ha) b (hST hb)

/-- **`main.tex` Lemma `lem:cstar_trace`.**  Cyclicity of the compressed vector
functional passes to norm limits, because `tau_q` and the compression map are
continuous. -/
theorem CornerTracialOn.closure {S : Set (H →L[ℂ] H)} (h : CornerTracialOn q Ω S) :
    CornerTracialOn q Ω (_root_.closure S) := by
  set f : (H →L[ℂ] H) × (H →L[ℂ] H) → ℂ :=
    fun z => tauVec Ω ((q * z.1 * q) * (q * z.2 * q)) with hf
  set g : (H →L[ℂ] H) × (H →L[ℂ] H) → ℂ :=
    fun z => tauVec Ω ((q * z.2 * q) * (q * z.1 * q)) with hg
  have h1 : Continuous fun z : (H →L[ℂ] H) × (H →L[ℂ] H) => q * z.1 * q :=
    (compressL q).continuous.comp continuous_fst
  have h2 : Continuous fun z : (H →L[ℂ] H) × (H →L[ℂ] H) => q * z.2 * q :=
    (compressL q).continuous.comp continuous_snd
  have hfc : Continuous f := (tauVec Ω).continuous.comp (h1.mul h2)
  have hgc : Continuous g := (tauVec Ω).continuous.comp (h2.mul h1)
  have hEq : Set.EqOn f g (S ×ˢ S) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact h a ha b hb
  have hcl : Set.EqOn f g (_root_.closure S ×ˢ _root_.closure S) :=
    eqOn_closure_prod hfc hgc hEq
  intro a ha b hb
  have hmem : ((a, b) : (H →L[ℂ] H) × (H →L[ℂ] H)) ∈
      _root_.closure S ×ˢ _root_.closure S := ⟨ha, hb⟩
  have hab := hcl hmem
  simpa [hf, hg] using hab

end Closure

/-! ## §6  The compressed quasi-local C⋆-algebra -/

section Quasilocal

open StabilizerHyperfinite.ConcreteQuasilocalCStarModel

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]
variable (rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H))
    (compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x)

omit [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem A (f · · ·)] in
include compat in
theorem range_rho_monotone : Monotone fun i => Set.range (rho i) := by
  rintro i j hij _ ⟨x, rfl⟩
  exact ⟨f i j hij x, compat i j hij x⟩

variable {q : H →L[ℂ] H} {Ω : H}

omit [Nonempty ι] [DirectedSystem A (f · · ·)] in
include compat in
/-- Stagewise cyclicity implies cyclicity on the union of the finite-stage
operator ranges, by directedness of the index set. -/
theorem cornerTracialOn_iUnion_range (h : ∀ i, CornerTracialOn q Ω (Set.range (rho i))) :
    CornerTracialOn q Ω (⋃ i, Set.range (rho i)) := by
  rintro a ha b hb
  simp only [Set.mem_iUnion] at ha hb
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact h k a (range_rho_monotone rho compat hik hi) b (range_rho_monotone rho compat hjk hj)

/-- **The compressed quasi-local C⋆-corner.**  If the compressed vector
functional is cyclic on every finite stage, it is cyclic on the whole concrete
quasi-local C⋆-algebra.  No von Neumann algebra, normality, or faithfulness
statement is involved. -/
theorem cornerTracialOn_quasilocalCStarAlgebra
    (h : ∀ i, CornerTracialOn q Ω (Set.range (rho i))) :
    CornerTracialOn q Ω
      ((quasilocalCStarAlgebra rho compat : StarSubalgebra ℂ (H →L[ℂ] H)) :
        Set (H →L[ℂ] H)) := by
  have hcl := (cornerTracialOn_iUnion_range rho compat h).closure
  rw [coe_quasilocalCStarAlgebra_eq_closure_iUnion rho compat]
  exact hcl

end Quasilocal

/-! ## §7  The packaged conditional theorem -/

section Main

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {Ω : H} (D : CompatibleFiniteCodespaceSystem Ω ι)
    (hp : IsDecreasingProjTower D.toFiniteCodespaceSystem.stageProj)

include hp

/-- Every finite stage is cyclic for the compressed functional attached to the
limit projection `q`. -/
theorem CompatibleFiniteCodespaceSystem.cornerTracialOn_stage (n : ℕ) :
    CornerTracialOn (limitProj D.toFiniteCodespaceSystem.stageProj) Ω
      (Set.range (D.pi n)) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  refine cornerTau_cyclic_of_stage (m := n) hp
    (fun k => D.toFiniteCodespaceSystem.stageProj_apply_self k) ?_
  intro k hk
  obtain ⟨u', hu'⟩ := D.range_pi_monotone hk (Set.mem_range_self u)
  obtain ⟨v', hv'⟩ := D.range_pi_monotone hk (Set.mem_range_self v)
  rw [← hu', ← hv']
  exact D.toFiniteCodespaceSystem.stage_cyclic k u' v'

/-- Cyclicity on the norm closure of the finite-stage operators. -/
theorem CompatibleFiniteCodespaceSystem.cornerTracialOn_closure :
    CornerTracialOn (limitProj D.toFiniteCodespaceSystem.stageProj) Ω
      (closure (⋃ n, Set.range (D.pi n))) := by
  refine CornerTracialOn.closure ?_
  rintro a ha b hb
  simp only [Set.mem_iUnion] at ha hb
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact D.cornerTracialOn_stage hp (max i j) a (D.range_pi_monotone (le_max_left i j) hi) b
    (D.range_pi_monotone (le_max_right i j) hj)

/-- **P49, packaged conditional theorem.**

Let `D` be explicit finite codespace data (finite-stage star representations,
hermitian idempotent code projections, densities `rho_n = weight n • P_n` of
trace one, and the GNS vector-state identity), with compatible stage
inclusions, and assume — this is the only unproved analytic premise, and it is
exactly `main.tex` Lemma `lema:proj_inequality` — that the stage projections
form a decreasing tower.  Let `q` be their strong limit and `A` any set of
operators contained in the norm closure of the finite-stage operators (for
instance the compressed quasi-local C⋆-algebra).

Then the compressed vector functional `tau_q(x) = ⟪Ω, x Ω⟫` is cyclic on the
`q`-compressions of `A`, is positive, is normalized, and is norm continuous.

No normality, faithfulness on a von Neumann corner, fullness, global weight, or
type-III statement is claimed. -/
theorem CompatibleFiniteCodespaceSystem.finite_corner_trace
    (S : Set (H →L[ℂ] H)) (hS : S ⊆ closure (⋃ n, Set.range (D.pi n))) :
    CornerTracialOn (limitProj D.toFiniteCodespaceSystem.stageProj) Ω S ∧
      cornerTau (limitProj D.toFiniteCodespaceSystem.stageProj) Ω 1 = 1 ∧
      (∀ x : H →L[ℂ] H,
        0 ≤ (cornerTau (limitProj D.toFiniteCodespaceSystem.stageProj) Ω
          (star x * x)).re) := by
  have hΩfix : ∀ n, D.toFiniteCodespaceSystem.stageProj n Ω = Ω :=
    fun n => D.toFiniteCodespaceSystem.stageProj_apply_self n
  have hq : limitProj D.toFiniteCodespaceSystem.stageProj Ω = Ω :=
    limitProj_apply_self hΩfix
  have hqsa : IsSelfAdjoint (limitProj D.toFiniteCodespaceSystem.stageProj) :=
    (limitProj_isStarProjection _).isSelfAdjoint
  refine ⟨(D.cornerTracialOn_closure hp).mono hS, ?_, ?_⟩
  · exact cornerTau_one hq D.toFiniteCodespaceSystem.inner_self_eq_one
  · exact fun x => cornerTau_nonneg hqsa Ω x

end Main

/-! ## §8  Non-vacuity: the hypotheses are simultaneously satisfiable

The structures above bundle several assumptions at once, so it must be checked
that they are consistent.  The following one-dimensional model instantiates
*every* field of `CompatibleFiniteCodespaceSystem` and the decreasing-tower
premise of the main theorem.  It is a sanity witness only; it carries no
manuscript content. -/

section Sanity

open scoped InnerProductSpace

/-- The tautological star representation of the one-dimensional matrix algebra
on `EuclideanSpace ℂ (Fin 1)`. -/
noncomputable def sanityRep :
    Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) where
  toFun := Matrix.toEuclideanCLM (𝕜 := ℂ)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)).toAlgEquiv.commutes r
  map_star' := map_star _

/-- A concrete model of all the finite codespace data. -/
noncomputable def sanitySystem :
    CompatibleFiniteCodespaceSystem (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1))
      (fun _ : ℕ => Fin 1) where
  pi := fun _ => sanityRep
  codeProj := fun _ => 1
  codeProj_mul_self := fun _ => by simp
  codeProj_isHermitian := fun _ => Matrix.isHermitian_one
  weight := fun _ => 1
  density := fun _ => 1
  density_eq := fun _ => by simp
  trace_density := fun _ => by simp
  vector_state := fun _ M => by
    show ⟪_, (Matrix.toEuclideanCLM (𝕜 := ℂ) M) _⟫_ℂ = _
    rw [PiLp.inner_apply]
    simp [Matrix.trace_fin_one, EuclideanSpace.single_apply]
  incl := fun _ => StarAlgHom.id ℂ _
  pi_incl := fun _ _ => rfl

theorem sanitySystem_stageProj (n : ℕ) :
    sanitySystem.toFiniteCodespaceSystem.stageProj n = 1 := map_one sanityRep

/-- The decreasing-tower premise of the main theorem is also satisfied by the
witness, so the conditional theorem is not vacuous. -/
theorem sanitySystem_isDecreasingProjTower :
    IsDecreasingProjTower sanitySystem.toFiniteCodespaceSystem.stageProj where
  isStarProjection n := sanitySystem.toFiniteCodespaceSystem.stageProj_isStarProjection n
  mul_of_le := by
    intro n m _
    rw [sanitySystem_stageProj, sanitySystem_stageProj, one_mul]

end Sanity

end FiniteCornerTrace
end AristotleCandidates

