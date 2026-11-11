# Von Neumann Foundation Blueprint Scope

Date: 2026-06-24.

This note records the approved scope for the next blueprint-audit phase.  It is
not itself a blueprint target and it does not change the Lean target chain.  It
is the reference specification for adversarial reviews of the current blueprint
suite before continuing the formalization.

## Vision

The blueprints should become a statement-complete and proof-detailed informal
specification for the Lean project.  They should not merely cite theorem names
from Takesaki or list future Lean declarations.  For the foundational von
Neumann algebra layer, proof sketches should be replaced by complete enough
proofs that an Aristotle or Lean formalization attempt has a concrete route.

The main near-term objective is not to prove the final type-classification
theorems.  It is to make it possible to define all objects and state the final
theorems without hidden mathematical debt.

## Source Style

Use Takesaki, Kadison--Ringrose, Blackadar, and other references as source
authorities, but translate them into direct concrete statements whenever that
is better for Lean.

The blueprint surface language should usually be concrete:

- Hilbert spaces;
- bounded operators `B(H)`;
- unital `*`-subalgebras;
- commutants and double commutants;
- concrete von Neumann algebras `M <= B(H)`;
- normal states, traces, projections, and GNS representations.

The optional title of a TeX environment should carry the Lean-facing name, the
stable target ID, and source locator when the statement is source-backed.  The
body should state the actual definition, theorem, proposition, or lemma
directly.  It should not say only "by Takesaki theorem X".

## Required Foundation Content

The blueprint suite should contain, in dependency order, at least the following
mathematical content.

### 1. Stabilizer and Quasilocal System

- The underlying qubit or Pauli-label index set.
- Finite regions and their local Pauli or matrix algebras.
- Inclusion maps for nested finite regions.
- The quasilocal algebra as the inductive-limit C*-algebra, or a precise
  project-local abstraction with enough universal properties to define states
  and local subalgebras.
- Region subalgebras `A_R` and their functoriality under inclusions.

### 2. Projection-Code State

- Local code subspace projections and their algebraic properties.
- The local state obtained from projection onto the code subspace.
- Consistency of the local states under region inclusions.
- Existence and uniqueness of the induced state `omega` on the quasilocal
  algebra.
- Positivity and normalization of `omega`.
- Any tracial, factorial, purity, or support property of `omega` that is later
  needed for type statements.

### 3. GNS Construction and Application

- A theorem giving the GNS construction for an arbitrary state on a C*-algebra:
  a Hilbert space `H_omega`, representation `pi_omega`, and cyclic vector
  `Omega_omega`.
- The equality
  `omega(a) = <Omega_omega, pi_omega(a) Omega_omega>`.
- The null-space quotient construction or a source-backed theorem that exposes
  enough structure for Lean use.
- The specialization of this theorem to the projection-code state on the
  quasilocal algebra.

### 4. Concrete Von Neumann Algebras

- The commutant `S'` of a set of bounded operators.
- The double commutant `S''`.
- A concrete von Neumann algebra on `H` as a unital `*`-subalgebra of `B(H)`
  satisfying `M = M''`, or an equivalent strong/weak closure formulation if
  Lean's available API makes that better.
- The generated von Neumann algebra of a set `S` as `S''`.
- For every region `R`, the represented region von Neumann algebra
  `M_R := pi_omega(A_R)''`.
- Basic net properties: isotony, generated-algebra monotonicity, and spatial
  covariance/unitary conjugacy where needed.

### 5. Double Commutant Theorem

Include the von Neumann double commutant theorem as a foundation theorem, not
only as a citation.  The direct form needed for the project is:

For a unital `*`-subalgebra `A <= B(H)`, the following closures agree:

- the double commutant `A''`;
- the strong operator closure of `A`;
- the weak operator closure of `A`.

The blueprint should decide which direction is actually needed for Lean.  If
the formalization defines concrete von Neumann algebras by `M = M''`, then the
theorem is still needed to connect this definition with source conventions and
with strong limits of operators/projections.

### 6. Monotone Limits of Projections

Include a projection-limit theorem, since it is used in the repository's
operator-algebra arguments.

The minimal useful form is:

Let `(p_n)` be a decreasing sequence of orthogonal projections on a Hilbert
space `H`.  Then there exists an orthogonal projection `p` such that

- `p_n` converges strongly to `p`;
- `range(p) = intersection_n range(p_n)`;
- `p <= p_n` for every `n`;
- `p` is the infimum of the projections `(p_n)`.

If each `p_n` lies in a von Neumann algebra `M`, then `p` lies in `M`, using
strong closure or the double commutant theorem.

If later proofs require nets rather than sequences, the blueprint should add
the directed-net version separately instead of silently using it.

### 7. Projection Equivalence and Type Predicates

To state final type theorems, the blueprints must define:

- projections in a concrete von Neumann algebra;
- Murray--von Neumann equivalence and subequivalence;
- finite, infinite, and properly infinite projections;
- center and factor;
- normal positive functionals, weights, and traces to the extent needed;
- finite and semifinite von Neumann algebras;
- type I, type II, and type III predicates in a source-backed form.

The first-pass target should be statement-complete definitions and criterion
theorems, not a full central-decomposition theory unless it is unavoidable for
the final theorem statements.

### 8. Tracial/Vacuum Criteria for Region Types

The blueprint suite should contain the criteria that connect the projection-code
state and the type of `M_R`.

At minimum it should specify:

- what it means for the GNS vector state to be tracial on `M_R`;
- when such a tracial vector state is faithful or normal;
- what type consequence follows from a faithful normal tracial state;
- what additional hypotheses distinguish finite type I, type II_1, semifinite
  type II, or type III exclusion.

The final type theorems can initially be stated conditionally, with explicit
hypotheses, provided all terms in the statement are already defined.

## Direct Formulation Versus Takesaki Formulation

The preferred blueprint formulation is direct and Lean-facing.  Takesaki's
formulation should be used verbatim only when it is already close to the Lean
object being defined or proved.  Otherwise the blueprint should:

1. record the Takesaki/KR/Blackadar locator;
2. restate the result in the concrete form needed here;
3. prove or derive that concrete form, with enough detail to make the
   dependency on the source theorem explicit.

## Adversarial Review Questions

The adversaries should attack the current blueprint suite with these questions.

- Can the projection-code state on the quasilocal algebra actually be defined
  from the stated hypotheses?
- Does the GNS theorem in the blueprints expose enough data to define
  `H_omega`, `pi_omega`, and `Omega_omega` and then specialize to this state?
- Are represented region von Neumann algebras defined as
  `pi_omega(A_R)''` only after the representation layer exists?
- Are commutants, double commutants, generated von Neumann algebras, and the
  bicommutant theorem stated in a form useful for Lean?
- Are decreasing projection limits available in the exact strength used by the
  intended proofs?
- Can type predicates be stated before the full classification proof?
- Are any proof sketches too vague for formalization, especially in the
  double-commutant, projection-limit, GNS, trace, and type-definition layers?
- Are source locators present for all textbook-backed assertions?
- Are project-local definitions clearly separated from source-backed theorems?

## Immediate Next Use

Before submitting further Lean formalization tasks, run adversarial reviews of
the current blueprints against this scope.  The expected output is a gap list:
missing definitions, missing theorem statements, proof sketches that must be
expanded to proofs, source locators that must be added, and targets whose
Lean-facing formulation should be simplified away from a Takesaki surface
statement.
