# 5-EQUATIONS

## Status

- Complete.

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

- Added `Deutsch/Gates/AxisRotation.lean`. Its unit-axis Pauli operator is proved Hermitian,
  involutive, and unitary; the closed rotation is proved equal to the genuine
  `NormedSpace.exp`; exponential conjugation and the full Rodrigues formula are derived; and the
  positive `x`-axis specialization is proved equal to the existing `rotationX`.
- Added `Deutsch/Gates/AxisRotationRegister.lean`. It embeds the construction at an arbitrary
  named wire, proves the global exponential identity, transports the generator and gate through an
  arbitrary unitary current frame, and proves Equation (17)'s componentwise exponential
  conjugation and current-frame Rodrigues form.
- Added the section-organized `Deutsch.Paper` façade:
  - `QuantumTheory.lean`: Equations (1)--(8);
  - `Gates.lean`: Equations (9)--(21);
  - `EPRExperiment.lean`: Equations (22)--(27);
  - `EPRComparison.lean`: Equation (28);
  - `Teleportation.lean`: Equations (29)--(37), including the unnumbered fixed-reference
    probability following Equation (37);
  - `LocallyInaccessible.lean`: Equations (38)--(39); and
  - `Bell.lean`: Equations (40)--(46).
- The façade preserves the required distinctions: Equation (8) accepts an explicitly supplied
  simultaneous eigenfamily; Equations (22) and (38) retain their exact phases; Equation (35) is the
  literal fixed-reference observable statement; Equation (36) states both endpoint descriptor
  triples; and Equation (43) requires positive hidden-variable weight.
- Strengthened the EPR bridge so Equation (28) first reaches the explicit unequal-basis-event sum
  through the four-wire comparison circuit before reaching the pair effect and trigonometric law.
  Equations (40) and (41) likewise expose the literal record effects and their pair-state bridges.
- Added `Deutsch.Bell.AngleMoments`, which states moment reproduction for arbitrary real settings.
  The Paper entries for Equations (42)--(44) quantify over all real angles, and Equation (46)
  restricts that same model to the three displayed settings before invoking the direct moment
  chain.
- Added `DeutschTests/Paper.lean` with exactly 46 `#check` commands and eight focused wrappers
  guarding current-frame Equation (9), true-exponential Equation (17), the structural four-wire
  Equation (28), literal four-wire Equations (40)--(41), positive-support Equation (43), all-angle
  Equation (44), and the direct Equation (46) chain.
- Extended the integrity audit to require exactly one bare production declaration for every
  `equation01` through `equation46`, the exact contiguous compile registry, all eight wrappers, and
  an axiom report for every canonical entry. Added `docs/paper.md` and linked it from the public
  entry points.

### No-cheating evidence

- Equation (17)'s public statement contains `NormedSpace.exp` on both sides of the Heisenberg
  conjugation, and its proof routes through the actual embedded and transported arbitrary-axis
  gate. The independently checked Rodrigues theorem and `x`-axis specialization pin the
  convention.
- Equations (28), (40), and (41) mention `fourWireTimeFourDensity` or
  `fourWireTimeThreeDensity` and the actual record/comparison effects. Their pair-density equalities
  are explicit conjuncts, not substitutions for the circuit statements.
- Equations (42)--(46) route through `ReproducesAngleEPRMoments` and the finite-moment theorems.
  The Equation (46) wrapper checks the direct chain and contains no reference to the
  agreement/pigeonhole contradiction.
- The source audit reconfirmed that the Equation (35) prose guard is unchanged.

### Verification evidence

- `lake build Deutsch.Paper DeutschTests.Paper` passed: 2744 jobs.
- `lake build` passed: 3327 jobs.
- `python3 goal-1/check_lean_integrity.py` passed:
  - 79 Lean sources scanned;
  - 46/46/46 exact declarations, compile checks, and axiom targets;
  - eight Paper no-cheating wrappers;
  - 517 representative axiom reports;
  - only `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 goal-1/check_source_audit.py` passed: 46 equation tags, 47 displays, protected
  Equation (35) prose, and all source/PDF/figure provenance hashes.
- `python3 goal-1/check_doc_links.py` passed: 15 expected and discovered documents, 125 local
  links.
- Bare-declaration and compile-registry scans each returned exactly 46 entries.
- `git diff --check` passed.

### Result carried forward

- Every corrected numbered display now has a compiled, source-shaped production entry with no
  remaining Stage 5 proof or packaging gap.
- Stage 6 can isolate the few printed-form fixtures in `DeutschErrata`; Stage 7 must then remove
  every historical declaration and historical word from `Deutsch` without compatibility aliases.
