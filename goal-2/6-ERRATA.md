# 6-ERRATA

## Status

- Complete.

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

- Added four Lake targets to the default build:
  `Deutsch`, `DeutschErrata`, `DeutschTests`, and `DeutschErrataTests`.
- Added the production companion:
  - `DeutschErrata.Rotation` locally states the two printed Equation (18) components,
    packages the genuine exponential, `x`-axis specialization, and derived component maps, and
    proves both quarter-turn mismatches;
  - `DeutschErrata.EPR` locally states the printed Equation (28)/(41) laws, packages the derived
    literal four-wire laws and pair bridges, and proves the equal-setting `0` versus `1` and `1/2`
    versus `0` comparisons;
  - `DeutschErrata.Teleportation` locally states the printed Equation (35) receiver effect and
    Equation (37) operator, proves actual five-wire probabilities `1` versus `0`, and proves the
    final operators unequal at `pi/4`;
  - the Mathlib-only `DeutschErrata.Equation45` computes the printed sides as `1` and `2` at
    `(1,0,1)` and proves the complementary partition for all eight Boolean triples; and
  - `DeutschErrata.Bell` connects that partition to the real indicator form and derives the
    Equation (46) contradiction through `Deutsch.Bell.Moments`.
- The Equation (37) module relocates only the private operator-nonzero comparison chain. It reuses
  the neutral `timeFive_q5_z` theorem and contains no second circuit, chronology, or descriptor
  derivation. The operator witness is necessary because the disputed middle term can disappear
  under the following fixed-reference expectation.
- Added `DeutschErrata.lean`, whose exact imports are the four topical comparison modules.
  `Equation45` remains a narrow internal dependency of `Bell`.
- Added `DeutschErrataTests.Comparisons` with 11 focused public-interface wrappers and
  `DeutschErrataTests.Audit` with 26 axiom commands covering every public comparison theorem and
  every printed fixture used by one.
- Added `docs/errata.md`. It presents three root bookkeeping slips, treats the teleportation
  displays as mechanical propagation, records the harmless `k`/`n` typo in prose, and records the
  stable PDF, canonical Markdown, verified-transcription, and compact-transcription hashes.
- Added `goal-2/check_errata_boundary.py`. It checks the exact Lake targets, exact Errata import DAG,
  test registry, one-way dependency, absence of BQP runtime paths, canonical artifact hashes, and
  historical Git-object hashes.

### No-cheating evidence

- Rotation routes through `exp_axisRotationGenerator` and the proved `x`-axis specialization; it
  does not call the older production `*_ne_printed` declarations.
- EPR uses `fourWireTimeFourDensity`, `fourWireTimeThreeDensity`, the actual comparison/record
  effects, and explicit pair bridges.
- The Equation (35) endpoint first uses `equation36_receiver_all_effects` to reduce the actual
  five-wire density, then proves one-qubit orthogonality. The Equation (37) endpoint uses the actual
  `timeFiveDescriptors`.
- Equation (45)'s printed sides are concrete definitions and are evaluated at an explicit
  assignment. Its complementary result is independently checked by Boolean cases.
- Equation (46) imports and invokes `Deutsch.Bell.Moments.equation46_contradiction`; it does not
  import or route through the agreement/pigeonhole module.

### Verification evidence

- `lake build DeutschErrata` passed: 2739 jobs.
- `lake build DeutschErrataTests` passed: 2742 jobs.
- `lake build` passed with all four default targets: 3338 jobs.
- `lake env lean DeutschErrataTests/Audit.lean` emitted 26 reports. The elementary definitions use
  no axioms; all other reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with
  no `sorryAx`.
- `python3 goal-2/check_errata_boundary.py` passed:
  - zero reverse production imports;
  - five Errata production modules;
  - four Lake targets;
  - 11 focused comparison declarations and 26 exact axiom targets;
  - two canonical file hashes and two historical Git-object hashes;
  - no runtime BQP dependency.
- `python3 goal-1/check_lean_integrity.py` passed after scanning 88 Lean sources; the 517 main
  representative reports still contain only the accepted foundations.
- Source audit passed with the protected Equation (35) prose and all provenance hashes unchanged.
- Documentation audit passed with 16 expected/discovered files and 128 repository-local links.
- `git diff --check` passed.

### Result carried forward

- The printed-form evidence is now independently available under `DeutschErrata`, so Stage 7 can
  delete every historical production declaration and the entire
  `Deutsch.Bell.SourceCorrection` module without aliases.
- Stage 7 must also rename the remaining correction-oriented neutral APIs, tests, examples, and
  documentation while keeping the Errata imports working against only the replacement names.
