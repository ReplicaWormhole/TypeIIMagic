# Complete Type-Classification Blueprint Goal

Date: 2026-06-21

## Goal

Write a complete source-backed TeX blueprint theory, with relevant proofs, for
all mathematical layers needed before Lean formalization of the full canonical
stabilizer projection-state von Neumann algebra type classification.

The goal is not merely to state the final classification theorem.  The
blueprints must provide enough standard and project-specific theory to prove
the classification theorem in Lean later.

This goal is informed by the mathlib coverage audit in
`agents/2026-06-21-mathlib-operator-algebra-coverage-audit.md`.  The blueprint
suite should rely on mathlib where it has usable infrastructure, but must not
assume that mathlib already contains the von Neumann factor/type classification
machinery.  In particular, the standard von Neumann algebra theory needed for
the classification must itself be part of the blueprint suite, with source
locators and proof plans.

## Required Scope

The blueprint suite must include:

- finite-support Pauli label systems and stabilizer subspaces;
- finite Pauli algebras, local matrix algebras, and the quasi-local/infinite
  spin algebra or a local-net abstraction adequate for the theorem;
- canonical stabilizer projection states, including consistency, positivity,
  and restriction to regions;
- infinite Hilbert spaces, either through infinite tensor products where needed
  or through the GNS construction;
- GNS representations of the canonical states;
- represented region von Neumann algebras as concrete algebras on Hilbert
  spaces, including bicommutants and commutants;
- the von Neumann algebra background needed for the proof: factors, centers,
  projections, Murray-von Neumann equivalence as needed, finite and semifinite
  traces, type `I_n`, type `I_infty`, type `II_1`, type `II_infty`, and type
  III exclusion criteria;
- tensor-product and infinite-product von Neumann algebra facts needed to
  identify the represented region algebras;
- the internal stabilizer reduction, adapted symplectic basis theorem, and
  product-form theorem for canonical projection states;
- the final type classification theorem for canonical stabilizer projection
  states, including all cases and the proof that type III does not occur in
  this sector.

## Mathlib-Backed Foundations

The blueprints may plan to rely on existing mathlib declarations for:

- Hilbert spaces and complete inner product spaces;
- bounded operators `H ->L[ℂ] H` and adjoints;
- `CStarAlgebra`, `NonUnitalCStarAlgebra`, spectral order, and positivity;
- positive linear maps `A ->ₚ[ℂ] ℂ`;
- GNS infrastructure via `PositiveLinearMap.GNS` and
  `PositiveLinearMap.gnsStarAlgHom`;
- concrete von Neumann algebras `VonNeumannAlgebra H`, commutants, and
  `VonNeumannAlgebra.commutant_commutant`;
- star projections and `VonNeumannAlgebra.IsStarProjection.mem_iff`;
- finite matrix traces, linear-map traces, Kronecker products, and
  `CStarMatrix`;
- finite Hilbert-space tensor products and algebraic `PiTensorProduct`.

These should be cited in blueprint target notes as available Lean
infrastructure, not reproved project-locally unless the later Lean attempt
exposes a gap.

## Project-Local Theory Required

The audit found no apparent mathlib API for the high-level type classification
machinery.  Therefore the blueprint suite must include project-local,
source-backed theory for:

- centers and factor criteria for concrete `VonNeumannAlgebra H`;
- Murray-von Neumann equivalence and the projection comparison facts actually
  needed by the stabilizer proof;
- finite, infinite, properly infinite, and semifinite projections in the
  concrete-von-Neumann setting;
- tracial, faithful, normal, finite, and semifinite trace interfaces, or
  narrowly scoped substitutes adequate for the theorem;
- definitions and recognition criteria for type `I_n`, type `I_infty`, type
  `II_1`, type `II_infty`, and type III exclusion;
- finite tensor/product factor classification facts for matrix blocks and
  tracial defect modes;
- infinite product or GNS-based replacement theorems needed to identify the
  represented region algebra in countably infinite regions.

The goal is allowed to use standard operator-algebra theorems as sourced
blueprint targets, but each theorem needed in the final proof must be stated
explicitly, with assumptions and locators, so it can later become a Lean target
or a deliberately scoped axiom-free abstraction.

## Blueprint Requirements

Each blueprint target must include:

- a stable target ID;
- all definitions before use;
- precise assumptions and conventions;
- theorem or lemma statements where applicable;
- proof sketches or complete informal proofs sufficient to guide Lean work;
- exact source locators for external stabilizer, Hilbert-space, GNS,
  tensor-product, and von Neumann algebra facts;
- an intended Lean declaration name and file path;
- a clear distinction between facts expected to be imported from mathlib and
  facts that must be formalized project-locally.

## Completed Planning Step

The manifest-level dependency plan has been written as
`blueprints/006-full-type-classification-dependency-plan.tex`.  It lists the
required target IDs from Pauli/quasi-local algebra through the final type
theorem, marks targets as mathlib-backed or project-local, and records the
standard operator-algebra locators currently available:

- Kadison--Ringrose I, Theorem 4.5.2 and Proposition 4.5.3, PDF pp. 287--288,
  for GNS construction and uniqueness;
- Kadison--Ringrose II, Definition 6.5.1, Theorem 6.5.2, Corollary 6.5.3,
  Remark 6.5.4, and Theorem 6.6.1, PDF pp. 57--63, for factor types and type
  recognition;
- Blackadar III.3.1.1--III.3.1.6, PDF pp. 301--304, for infinite tensor
  products and product-state factors;
- Blackadar III.3.4.1--III.3.4.2, PDF p. 317, for hyperfiniteness and
  infinite tensor products of finite-dimensional algebras.

`MANIFEST.toml` has been expanded with the planned targets.  Targets whose
source locators are still too coarse are marked with partial-locator status,
especially the quasi-local state extension, center/factor definitions, and
projection-comparison definitions.

## Immediate Next Step

Choose the next target and upgrade it from `planned_in_master_blueprint` to a
dedicated complete blueprint note.  The highest-leverage next target is
`PAULI-002` plus `QL-001`, because finite Pauli algebras and the quasi-local
local-net interface are prerequisites for positivity, GNS, and region von
Neumann algebras.
