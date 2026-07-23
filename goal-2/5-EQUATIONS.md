# 5-EQUATIONS

## Status

- In progress.

## Current Facts

- Stages 3 and 4 closed all previously substantive gaps except Equation (17): literal four-wire
  proofs now exist for Equations (28), (40), and (41), and the direct finite-expectation route now
  exists for Equations (42)--(46).
- The Stage 1 map classified 31 equations as already having direct mathematical substance, seven
  as needing source-shaped packaging, and eight as needing substantive proof.
- Every numbered display must receive exactly one canonical `Deutsch.Paper` entry. A ledger label
  or test-only theorem does not count.
- Equation (8) requires an explicitly supplied simultaneous eigenfamily and an explicit transported
  representative; the source display must not be read as selecting a canonical phase or basis
  inside a degenerate eigenspace.
- Equation (17) must use a genuine arbitrary real unit axis, a Pauli-axis operator, a true matrix
  exponential, unitarity, and the project's Heisenberg conjugation convention.
- Equations (22) and (38) are exact only up to the already exposed global phase.
- The production façade must remain historically neutral and must distinguish definitions,
  schemas, operator equalities, phase equivalences, probability equalities, and stochastic
  almost-sure statements.

## Updated Assumptions

- The façade can be organized by source sections while retaining descriptive reusable theorems in
  their existing topical modules.
- Most façade entries can be thin theorem statements that expose the source variables and exact
  assumptions while delegating the proof to already audited production declarations.
- A genuine Equation (17) proof is feasible in the pinned mathlib using the Banach-algebra matrix
  exponential series for an involutive unit-axis Pauli operator.
- A machine-checked registry can enforce the exact contiguous names `equation01` through
  `equation46`, their production location, and their importability from one `Deutsch.Paper` root.

## Big Picture Objective

- Expose a clean, source-shaped production façade with exact compiled coverage of all forty-six
  numbered equations, including a genuine arbitrary-axis Equation (17).

## Detailed Implementation Plan

- Add a neutral arbitrary-axis rotation module with:
  - real three-vectors, dot and cross products;
  - bundled unit axes and `n · sigma`;
  - Hermiticity, square-one, and unitarity;
  - the generator `-i theta (n · sigma)/2`;
  - equality between its actual matrix exponential and the closed Pauli form;
  - exact exponential Heisenberg conjugation and Rodrigues form; and
  - an `x`-axis specialization equal to the existing `rotationX`.
- Add `Deutsch/Paper` modules grouped by source section and a `Deutsch/Paper.lean` root.
- Give each display exactly one entry named `equation01` through `equation46`, using definitions
  where the display introduces notation and theorems where it asserts a derived equality.
- Package the wrapper gaps E08, E09, E13, E14, E19, and E26 with the necessary explicit scope and
  use the neutral Equation (45) result from Stage 4.
- Add a compiled `DeutschTests/Paper.lean` registry plus integrity checks that require exactly the
  contiguous E01--E46 public contract.
- Export `Deutsch.Paper` from `Deutsch`, add focused axiom reports, and document how to reuse the
  façade without making the topical core source-shaped.

## No-Cheating Checks

- Equation (17) must mention and be connected to `Matrix.exp`; a closed `x`-axis formula alone is
  insufficient.
- No façade theorem may assume its own displayed conclusion or choose a definition solely to make a
  desired result reflexive without an implementation theorem.
- The Equation (28), (40), and (41) façade entries must use the four-wire record/comparison state,
  not only `pairDensity`.
- Equations (42)--(46) must route to the direct moment chain, not the agreement/pigeonhole theorem.
- Equation (43) must retain a positive-weight support premise.
- Equation (35)'s source prose remains untouched; the façade states the compiled certainty theorem
  and does not add a source qualifier.
- Global-phase qualifications remain visible for Equations (22) and (38).
- No historical comparison or compatibility alias appears under `Deutsch.Paper`.

## Completion Requirements

- `Deutsch.Paper.equation01` through `Deutsch.Paper.equation46` all compile from production code.
- The exact registry rejects missing, duplicate, noncontiguous, test-only, or historically named
  entries.
- The arbitrary-axis exponential and its `x`-axis specialization compile and are independently
  tested.
- Focused Paper/Gates tests, all public/test builds, integrity and axiom audits, source/provenance
  checks, documentation links, whitespace scan, and `git diff --check` pass.

## Stage Results

- In progress. The arbitrary-axis module and first source-section façade module are under direct
  compilation; integration, remaining sections, the registry, and full verification remain.
