# 7-CUTOVER

## Status

- Complete.

## Current Facts

- `DeutschErrata` now contains every decisive original-form fixture and comparison needed by the
  public historical account. No corrected theorem depends on those fixtures.
- `Deutsch` still has one wholly historical module/import,
  `Deutsch.Bell.SourceCorrection`, and nine families of embedded comparison declarations:
  - two `rotationX_*_ne_printed` theorems;
  - two pair-only Equation (28)/(41) counterexamples;
  - three propagated Equation (29)/(31)/(32) counterexamples;
  - two propagated Equation (34)/(37) counterexamples; and
  - the printed Equation (35) effect and its two theorems.
- The remaining correction-oriented neutral APIs are:
  - `equation35CorrectedEffect` and `equation35_corrected_effect_op`; and
  - four `corrected_epr_*` / `*_corrected_epr_*` Bell contradiction names.
- The main tests, examples, axiom registry, integrity checker, and several public documents still
  use those names or discuss the historical comparison as though it belonged to `Deutsch`.
- Physical protocol names `Correction`, `correctionGate`, and their branch-correction terminology
  are semantically neutral and must remain.
- The full Stage 6 build and both axiom audits pass, so every historical production declaration can
  now be removed rather than aliased.

## Updated Assumptions

- Removing comparison-only private helpers from `Deutsch.Teleportation.Descriptors` is safe because
  the required operator comparison has been independently compiled inside `DeutschErrata`.
- Main-library tests should test only the derived formulas and operational results. Historical
  regressions belong exclusively to `DeutschErrataTests`.
- Public documentation can explain the neutral theorem contract without erasing provenance:
  one short link to `docs/errata.md` is sufficient wherever readers need the separate comparison.
- Dated goal ledgers may retain historical evidence, but current source mappings and public reports
  must point to the new neutral APIs and separate Errata layer.

## Big Picture Objective

- Make `Deutsch` read exactly like a direct formalization of the canonical source: neutral names,
  neutral comments, no printed-form fixtures, no historical imports, and no compatibility aliases.

## Detailed Implementation Plan

- Delete `Deutsch/Bell/SourceCorrection.lean` and remove its root/import-closure/audit entries.
- Remove the comparison-only declarations and their private support from:
  - `Deutsch/Gates/OneQubit.lean`;
  - `Deutsch/EPR/Statistics.lean`;
  - `Deutsch/Teleportation/Circuit.lean`;
  - `Deutsch/Teleportation/Descriptors.lean`; and
  - `Deutsch/Teleportation/Statistics.lean`.
- Rename without aliases:
  - `equation35CorrectedEffect` to `equation35Effect`;
  - `equation35_corrected_effect_op` to `equation35_effect_op`;
  - `corrected_epr_three_settings_refute_local_assignments` to
    `epr_three_settings_refute_local_assignments`;
  - `no_local_assignments_reproduce_corrected_epr_three_settings` to
    `no_local_assignments_reproduce_epr_three_settings`;
  - `corrected_epr_three_settings_refute_normalized_local_model` to
    `epr_three_settings_refute_normalized_local_model`; and
  - `no_normalized_local_model_reproduces_corrected_epr_three_settings` to
    `no_normalized_local_model_reproduces_epr_three_settings`.
- Rewrite every editorially historical comment/docstring under `Deutsch`, while leaving physical
  uses of correction terminology intact.
- Remove historical wrappers from `DeutschTests`, rename corrected-oriented examples and tests, and
  update all main axiom targets to the neutral API.
- Update the integrity checker to enforce:
  - the four Lake roots and separate test roots;
  - the exact one-way import boundary;
  - absence of historical tokens under `Deutsch`;
  - absence of superseded declaration names and `SourceCorrection`; and
  - exact neutral public declarations, examples, and axiom targets.
- Rewrite the current public documentation and source mapping around the neutral library. Keep
  original-form analysis only in `docs/errata.md` and the intentionally historical goal evidence.

## No-Cheating Checks

- A whole-tree declaration scan must find none of the superseded production names and no alias
  whose body is merely one of the renamed theorems.
- A case-insensitive production-source scan must find no editorial `printed`, `corrected`,
  `SourceCorrection`, `errata`, `source defect`, or equivalent historical language.
- The scan must not reject physical teleportation `Correction`/`correctionGate` terminology.
- `Deutsch.lean` and every file reachable from it must have no `DeutschErrata` import.
- `DeutschTests` must not import `DeutschErrata`; `DeutschErrataTests` remains the only historical
  verification root.
- Main examples and docs must compile/reference only the neutral names.
- The exact E01--E46 facade and all Stage 3--5 no-cheating checks must remain unchanged and green.

## Completion Requirements

- `Deutsch/Bell/SourceCorrection.lean` is absent and unreachable.
- No printed-form declaration or comparison-only helper remains under `Deutsch`.
- All six neutral rename targets compile, and no compatibility alias exists.
- The historical-token, superseded-name, import-boundary, test-root, documentation, source,
  integrity, axiom, whitespace, and diff audits pass.
- All four Lake targets and the full build pass.
- Public documentation presents `Deutsch` as a direct derivation and `DeutschErrata` as the
  separate concise comparison.

## Stage Results

- Removed `Deutsch/Bell/SourceCorrection.lean` and its production-root import.  No file under
  `Deutsch` or `DeutschTests` imports `DeutschErrata`.
- Removed all comparison-only gate, EPR, and teleportation declarations from `Deutsch`; the
  decisive original-form fixtures remain available only through the five-module
  `DeutschErrata` root.
- Renamed the six reusable public APIs without compatibility aliases:
  - `equation35Effect`;
  - `equation35_effect_op`;
  - `epr_three_settings_refute_local_assignments`;
  - `no_local_assignments_reproduce_epr_three_settings`;
  - `epr_three_settings_refute_normalized_local_model`; and
  - `no_normalized_local_model_reproduces_epr_three_settings`.
- Reworked `DeutschTests`, examples, axiom targets, public documentation, and the live source map
  around the neutral APIs.  Physical `Correction`, `correctionGate`, and branch-correction names
  remain because they describe the teleportation protocol.
- Strengthened `goal-1/check_lean_integrity.py` and `goal-2/check_errata_boundary.py` to reject
  reverse imports, historical production vocabulary, superseded names, and compatibility aliases
  while checking all four Lake roots.
- Verification completed successfully:
  - `lake build Deutsch DeutschTests DeutschErrata DeutschErrataTests` built 3337 jobs;
  - `python3 goal-1/check_lean_integrity.py` scanned 87 Lean sources, checked the exact
    46/46/46 paper registry and 503 axiom reports, and observed only `Classical.choice`,
    `Quot.sound`, and `propext`;
  - `python3 goal-2/check_errata_boundary.py` found zero reverse imports, zero main-test Errata
    imports, no production history tokens, no superseded names, and no BQP runtime dependency;
  - `python3 goal-1/check_source_audit.py` passed all 46 equations, 47 display blocks, source
    guards, and canonical provenance hashes;
  - `python3 goal-1/check_doc_links.py` passed all 16 public Markdown files and 126 local links;
  - focused forbidden-token and superseded-name scans were empty; and
  - `git diff --check` passed.
- The exact E01--E46 façade, literal four-wire EPR bridge, arbitrary-axis exponential result, and
  direct moment-chain Bell route were unchanged by the cutover and rebuilt successfully.
