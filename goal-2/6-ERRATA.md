# 6-ERRATA

## Status

- In progress.

## Current Facts

- The canonical corrected source and the neutral `Deutsch.Paper` façade are complete. Historical
  comparison is no longer needed to establish any corrected equation.
- Printed-form material still resides in production in four places:
  - two Equation (18) special-angle inequalities in `Deutsch.Gates.OneQubit`;
  - Equation (28)/(41) equal-setting counterexamples in `Deutsch.EPR.Statistics`;
  - propagated teleportation inequalities and the printed Equation (35) effect in
    `Deutsch.Teleportation`; and
  - the standalone `Deutsch.Bell.SourceCorrection` module for Equation (45).
- The three decisive root comparisons can be much smaller than that current inventory:
  Equation (18) fixes the rotation orientation; the equal-setting four-wire record probabilities
  fix the EPR same/different swap; and the Boolean assignment `(1,0,1)` fixes the missing
  complement in Equation (45).
- Receiver-effect and final-operator witnesses at `theta = pi/2` and `theta = pi/4` show that the
  Equation (18) orientation propagates to late teleportation predictions without duplicating the
  five-wire circuit.
- The neutral main library already supplies the positive results needed by the historical
  comparison: the arbitrary/current-frame rotation identities, literal four-wire EPR
  probabilities, receiver-density Bloch operator and circuit correctness, complementary Boolean
  partition, and direct Equation (46) contradiction.
- The repository PDF and Git history are sufficient provenance for the original forms. The PDF has
  stable SHA-256
  `d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb`;
  the sibling BQP checkout will not be imported or read by any build or verifier.

## Updated Assumptions

- A small errata library can state every printed fixture locally and import only the narrow neutral
  module that derives the corresponding result.
- The Equation (35) endpoint can be checked using its one-qubit receiver effect and the already
  proved five-wire-to-receiver bridge, so no second copy of the teleportation chronology is needed.
- Equation (37)'s printed and derived operators can have the same fixed-reference expectation,
  because the disputed middle term has zero reference expectation. It therefore needs an operator
  inequality rather than a probability witness. The existing short comparison-only nonzero proof
  can be relocated privately without duplicating any circuit.
- Equation (46)'s restored contradiction should be a direct corollary of the moment-chain theorem,
  not a second implementation of the Bell derivation and not the independent pigeonhole proof.

## Big Picture Objective

- Add a deliberately small `DeutschErrata` companion that records the original printed fixtures,
  gives decisive counterexamples, and points back to the neutral derived results, while preserving
  a strict one-way dependency on `Deutsch`.

## Detailed Implementation Plan

- Add `DeutschErrata` and `DeutschErrataTests` as separate Lake libraries and default targets.
- Add `DeutschErrata/Rotation.lean`:
  - state the two printed Equation (18) component formulas locally;
  - expose the derived formulas from the neutral arbitrary-axis/gate layer; and
  - prove both disagreements at `theta = pi/2`.
- Add `DeutschErrata/EPR.lean`:
  - state the printed Equation (28) and Equation (41) probability laws locally;
  - use the literal four-wire comparison and record effects; and
  - prove the decisive equal-setting values (`0` versus `1`, and `1/2` versus `0`).
- Add `DeutschErrata/Teleportation.lean`:
  - define only the printed minus-sine Equation (35) receiver effect at `theta = pi/2`;
  - prove that the actual five-wire receiver accepts the derived effect with probability one but
    the printed effect with probability zero; and
  - define the printed plus-middle-sign Equation (37) operator and prove its inequality with the
    derived circuit operator at `theta = pi/4`; and
  - reuse the neutral receiver reduction and `timeFive_q5_z` rather than restating the circuit.
- Add a Mathlib-only `DeutschErrata/Equation45.lean`:
  - state the printed Equation (45) right-hand side locally;
  - prove its `(1,0,1)` values and failure;
  - prove the universal complementary partition by the eight Boolean cases.
- Add `DeutschErrata/Bell.lean`:
  - connect the elementary complement result to the neutral real-valued partition; and
  - derive `False` from the corrected Equation (42)--(46) moment contract.
- Add the `DeutschErrata.lean` root, focused smoke tests, a separate axiom-audit test, and an import
  boundary/provenance checker.
- Add concise errata documentation. Record the harmless `k`/`n` index typo as prose rather than an
  artificial theorem, identify the stable PDF and canonical-source hashes, and explain that all
  downstream display changes are mechanical consequences of three root slips.

## No-Cheating Checks

- Every printed formula must be declared under `DeutschErrata`, not passed in as a hypothesis.
- Rotation counterexamples must use the neutral matrix-derived `rotationX` results.
- EPR counterexamples must mention the literal four-wire record/comparison density and effects,
  not just a two-qubit surrogate.
- The teleportation witness must pass through the proved five-wire-to-receiver statistical bridge;
  it must not define an unrelated one-qubit example and call it the circuit result.
- The Equation (45) counterexample must compute both sides at the explicit Boolean assignment.
- The Equation (46) theorem must route through the direct moment chain and remain independent of
  the pigeonhole proof.
- An automated import scan must reject any `Deutsch -> DeutschErrata` edge and any BQP path.

## Completion Requirements

- `DeutschErrata` and `DeutschErrataTests` are independently importable Lake targets.
- The root exports only the four narrow comparison modules; no full circuit is duplicated.
- Printed fixtures, decisive witnesses, universal derived replacements, and direct restored
  contradiction all compile.
- Axiom reports contain only the accepted mathlib foundations and no `sorryAx`.
- The errata documentation is polite, concise, provenance-backed, and treats propagated displays
  as consequences rather than independent mistakes.
- Focused errata builds/tests, all four public/test targets, import-boundary and provenance checks,
  source/doc checks, full build, whitespace, and `git diff --check` pass.

## Stage Results

- In progress.
