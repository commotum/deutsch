# 1-BASELINE

## Current Facts

- The working tree began this stage clean on `master`, with `HEAD` and `origin/master` both at
  `f6b21ee`.
- The package is pinned to `leanprover/lean4:v4.32.0`; `lakefile.toml` pins mathlib `v4.32.0`, and
  `lake-manifest.json` resolves mathlib to
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- The current package has 49 production Lean files under `Deutsch/`, 14 focused files under
  `DeutschTests/`, and the two roots `Deutsch.lean` and `DeutschTests.lean`, for 65 Lean sources in
  the integrity audit.
- `lake build Deutsch DeutschTests` succeeds with 3309 jobs.
- `python3 -B goal-1/check_lean_integrity.py` succeeds with 402 representative axiom reports. The
  only observed foundational axioms are `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_doc_links.py` succeeds over 14 required Markdown documents and 118
  repository-local links.
- `python3 -B goal-1/check_source_audit.py` fails at the known section-heading check because the
  canonical source uses `### 1.` through `### 8.` while the checker requires `##`.
- The canonical Markdown currently has 1255 lines, 46 numbered equation tags, 47 display blocks
  (46 tagged and one untagged), eight numbered sections, and three linked figures. The old audit's
  U01 and U03 formulas are present inline, matching the PDF and verified transcription.
- The current source/PDF/image/toolchain hashes and the authoritative equation/leak inventories are
  being recorded in this stage before implementation begins.

## Updated Assumptions

- The previous Stage 12 build and integrity claims remain reproducible on the current commit.
- The source-audit failure is structural rather than mathematical, but the rest of that checker must
  be rerun after the heading mismatch is repaired; an early exit is not evidence that its later
  checks still pass.
- Most of the corrected finite mathematics is already reusable, but a lifecycle ledger entry does
  not establish literal E01–E46 production coverage.
- The current production import graph has no verification imports, but it deliberately imports
  historical source-comparison code through `Deutsch.Bell.SourceCorrection`; this must be separated
  later rather than treated as a baseline integrity failure.
- The sibling BQP files are useful comparison evidence but cannot be part of the final build or
  verification dependency graph.

## Big Picture Objective

- Freeze a trustworthy current-state baseline.
- Establish exact source provenance and current verification results.
- Classify each numbered equation as directly represented, needing a source-shaped wrapper, or
  needing substantive new proof.
- Inventory every historical declaration, comment, import, test, checker entry, and document that
  must move or change during the two-library cutover.
- Lock the source-edit and dependency boundaries before Stage 2 changes the canonical Markdown.

## Detailed Implementation Plan

- Inspect Git state, branch synchronization, toolchain pins, Lake targets, source/module counts,
  roots, and import edges.
- Hash the canonical Markdown, PDF, figures, toolchain, Lake configuration, and manifest.
- Compare the in-repository PDF/source hashes with the BQP review copies and identify stable
  provenance that does not create an external dependency.
- Run the current focused/full builds, integrity/axiom audit, source audit, documentation audit, and
  whitespace/diff checks.
- Derive the exact E01–E46 map from actual production declarations rather than trusting old status
  labels.
- Search production, tests, checkers, and public documentation for correction-oriented names and
  classify each destination.
- Locate stale source-fidelity and source-structure statements.
- Fold all established baseline facts and hashes into `goal-2/0-plan.md`.

## No-Cheating Checks

- Do not mark an equation directly covered merely because the source ledger says `Partial`,
  `Corrected`, or `Oracle verified`.
- Do not count a test theorem as a production declaration.
- Do not count a pair-state theorem as the literal four-wire Equation (28), (40), or (41) result.
- Do not count the current pigeonhole contradiction as corrected Equations (42)–(46).
- Do not count the closed `x`-axis rotation as arbitrary-axis Equation (17).
- Do not edit the canonical source, Lean implementation, public documentation, or old audit tooling
  in this stage except to record baseline evidence in `goal-2`.
- Do not modify the prose before Equation (35).
- Do not read BQP files at build time or introduce any repository dependency on the sibling
  checkout.

## Completion Requirements

- Current Git, toolchain, build, audit, source, and documentation states are recorded with commands
  and outcomes.
- Stable hashes are recorded for the canonical Markdown, PDF, figures, and relevant comparison
  copies.
- Every E01–E46 item is classified with exact current production declarations and exact remaining
  work.
- Every historical production leak has an identified move/rename/delete destination.
- Stale source-fidelity and source-structure documentation is enumerated.
- The source-edit boundary explicitly preserves the Equation (35) prose.
- The dependency contract explicitly requires `DeutschErrata -> Deutsch` and forbids the reverse.
- `goal-2/0-plan.md` is updated with all established facts before Stage 2 begins.

## Stage Results

### Git, Toolchain, and Verification Baseline

- Initial Git state:
  - branch `master`;
  - `HEAD = origin/master = f6b21ee`;
  - no tracked or untracked changes;
  - `git diff --check` passed.
- Toolchain/configuration hashes:
  - `lean-toolchain`:
    `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`;
  - `lakefile.toml`:
    `088b47be10eeff5a68ce77fd2fe6cd26ff459d57b55197c6dd2fafeb1549117f`;
  - `lake-manifest.json`:
    `9f1a16f9c4027d0ccf66260b952dcedfc2270cdb17c9ea93f529e861c2a5ec1d`.
- `lake build Deutsch DeutschTests` passed with 3309 jobs.
- `python3 -B goal-1/check_lean_integrity.py` passed:
  - 65 Lean sources;
  - no forbidden proof holes/declarations;
  - no production imports of verification modules;
  - 402 representative axiom reports;
  - observed foundations exactly `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_doc_links.py` passed with 14 required public documents and 118
  repository-local links.
- `python3 -B goal-1/check_source_audit.py` failed at the expected section-heading mismatch. Review
  established that after that repair it would also fail its stale display-count and U-signature
  assumptions, so no later source-check step is treated as having passed indirectly.

### Canonical Source and Provenance

- Canonical SHA-256 values:

  | Artifact | SHA-256 |
  | --- | --- |
  | `deutsch-2000/deutsch-2000.md` | `b07b7bdafb13db21021b7e0d77efe74c2711fa6841772b00d3f369a67481b208` |
  | `deutsch-2000/deutsch-2000.pdf` | `d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb` |
  | Figure 1 | `8c5070722164b9a804f26ad2931aaa357d382575be0e092c58f11cad1fafcbed` |
  | Figure 2 | `5f262a847f99cb25440a76783bac8b16c323a163e229bd9a164e4691e625c4e2` |
  | Figure 3 | `22a3b7c5e3dc95c61151ceef02338ed4e0573c731fc0d0c33dfe931a2cab87d3` |

- `pdfinfo` reports a 24-page A4 PDF, 267409 bytes, with creation metadata dated
  1999-06-02. It is byte-identical to the BQP PDF.
- The three repository figures are byte-identical to BQP's `images-verified` figures and to the
  former repository `images-verified` Git blobs before their directory move.
- The canonical Markdown is byte-identical to the deleted
  `deutsch-2000-corrected.md` at `fd2e2d1^`.
- The compact original remains in Git at `fd2e2d1^:deutsch-2000/deutsch-2000.md`, is byte-identical
  to the current BQP compact original, and has SHA-256
  `0e16b16e9308beb01f3eb4d746951cb0a8a40971a434b1bcb71b6a03d910cb3b`.
- The historical verified transcription remains in Git at
  `fd2e2d1^:deutsch-2000/deutsch-2000-verified.md`, SHA-256
  `02468f4b0a6b731a4f733bab928c858b6f7ddcaf6142ac952a5495b404ed785b`.
  The current BQP verified file has SHA-256
  `432cbf63d9bcad5af26930e9f5b5aa9881ca735a9e084fd7bfe587eb1cef8399`;
  the differences are abstract italics, image paths, and final-newline presentation.
- The unchanged PDF entered Git at `71cf9755`; the canonical cutover and deletion of the redundant
  Markdown variants occurred at `fd2e2d1`.
- The verified source structure is:
  - 1255 lines and a final newline;
  - exactly 47 `$$` blocks, comprising equations (1)–(46) exactly once and one unnumbered
    post-(37) verification display;
  - U01 and U03 present inline, as they are in the PDF;
  - eight numbered sections and three valid image links.

### E01–E46 Production Map

The classification describes existing core mathematical substance. Stage 5 will still give every
item a canonical, source-shaped `Deutsch.Paper` entry.

| ID | Existing production evidence | Baseline classification and exact gap |
| --- | --- | --- |
| E01 | `Descriptor`, `Descriptor.Valid`, `DescriptorFamily.Valid` in `Deutsch/Descriptor/Basic.lean` | Direct finite descriptor triple/family |
| E02 | `Descriptor.Valid.square`, cyclic products, derived reverse laws, family cross-commutation, validity evolution | Direct algebra schema |
| E03 | `Foundations.pauliX/Y/Z` and embedded Pauli algebra/Hermiticity | Direct concrete matrices |
| E04 | `bitOneProjector`, `paperBitOneProjectorAt`, `zPlusEffect_op_eq_paperBitOneProjectorAt` | Direct Boolean projector/effect |
| E05 | `Descriptor.initial`, `initial_component`, `Register.embedQubit` | Direct finite tensor embedding |
| E06 | `Register.referenceKet`, `expectation`, `fixed_reference_prediction` | Direct fixed-reference expectation |
| E07 | `Register.heisenberg`, `Descriptor.evolve`, `evolve_component` | Direct finite Heisenberg evolution |
| E08 | `Register.heisenberg_eigenvector` | Wrapper gap: package simultaneous indexed eigenbasis with phase/degeneracy qualifications |
| E09 | `not_mulVec_ketOne`, `not_mulVec_ketZero`, plus E08 transport | Wrapper gap: source-shaped time-indexed eigenket statement |
| E10 | `Gates.not_matrix_entry` | Direct matrix-element identity |
| E11 | `Gates.notGate := pauliX` | Direct matrix identity |
| E12 | `Gates.descriptorNot`, `embed_notGate_eq_xAt` | Direct current/named descriptor gate |
| E13 | `descriptorNot_evolve` plus family commutation/locality | Wrapper gap: bundle triple with all-other-qubits clause |
| E14 | `paperSqrtNot_square`, local/named Heisenberg component theorems | Wrapper gap: current-descriptor package |
| E15 | `cnotFromDescriptors`, `cnotAt_eq_global_formula`, `cnotAt_act_basisKet` | Direct CNOT definition/truth table |
| E16 | Six `cnotFromDescriptors_conjugates_*` theorems and named-register checks | Direct six-component map |
| E17 | Existing `rotationX` is only the closed `x`-axis case | Substantive: unit-axis `n·sigma`, exponential, unitarity, and arbitrary-axis conjugation |
| E18 | `rotationX_heisenberg_x/y/z` and named lifts | Direct corrected component algebra; historical witnesses must move |
| E19 | Local/named `hadamard_heisenberg_*` and `hadamardAt_*` | Wrapper gap: current-descriptor package |
| E20 | Six `bellAt_conjugates_*` and two bundled descriptor results | Direct named-register map; paper façade may add a covariance/current-frame wrapper |
| E21 | Six inverse-Bell component results, bundles, and both inverse products | Direct named-register map; paper façade may add a covariance/current-frame wrapper |
| E22 | `equation22Ket`, `pairKet_eq`, `equation22Ket_eq_globalPhase` | Direct phase-aware state identity |
| E23 | `EPR.equation23_q2/q3` | Direct two descriptor triples |
| E24 | `equation24_q1/q4` | Direct untouched-record locality statements |
| E25 | `equation25_q2/q3` | Direct rotated descriptor triples |
| E26 | `pairDensity_reduce_singleton`, `pairDensity_z_expectation`, local-statistics independence | Wrapper gap: displayed zero Bloch triple/literal time-two package |
| E27 | `equation27_q1/q2/q3/q4` | Direct four record/post-CNOT triples |
| E28 | `pairDensity_different_probability` is pair-only | Substantive: literal four-wire time-four comparison probability and bridge |
| E29 | `Teleportation.equation29_q1` | Direct input descriptor |
| E30 | `equation30_q4/q5` | Direct resource descriptors |
| E31 | `equation31_q1/q4` | Direct Bell-evolved descriptors |
| E32 | `equation32_q2/q3` | Direct coherent-record descriptors |
| E33 | Nine `equation33_{k,l,m}_{x,y,z}` theorems backed by `correctionGate` | Direct explicit generator map; façade may package covariance/current-frame scope |
| E34 | `equation34_q5` | Direct receiver descriptor |
| E35 | Effect operator, receiver/five-wire certainty theorems in `Teleportation/Statistics.lean` | Direct substance; neutral rename and literal expectation façade needed |
| E36 | Receiver Bloch operator/vector/density/all-effect theorems | Direct strengthened prediction equality |
| E37 | `timeFive_q5_z` plus independent final probability theorems | Direct operator/probability substance; printed witness must move |
| E38 | `equation38Ket`, `equation38Ket_eq_globalPhase_pairPureState` | Direct phase-aware state identity |
| E39 | Route ket, pure-ket, and density equalities | Direct state/provenance identity |
| E40 | Pair marginal theorems only | Substantive: literal `q1/q4` four-wire record marginals |
| E41 | Pair joint-paper-one theorem only | Substantive: literal time-three record-joint effect and bridge |
| E42 | Equal-setting agreement exists only in alternate probability form | Substantive: direct real Boolean mean-square theorem |
| E43 | `perfectEqualSettingSupport_of_agreementProbability_one` is reusable but bypasses E42 | Substantive: direct E42-to-positive-support/almost-sure equality |
| E44 | Current Bell modules use agreement probabilities | Substantive: displayed Alice–Alice joint moment on a common finite space |
| E45 | Historical `Nat` truth-table partition in `SourceCorrection` | Wrapper gap: neutral real-indicator complement identity feeding expectation |
| E46 | Existing finite pigeonhole/agreement contradiction is a different proof | Substantive: literal corrected expectation chain and contradiction |

Totals: 31 direct implementations, seven wrapper/packaging gaps, and eight substantive proof gaps.

### Historical Production Inventory and Destinations

- Direct import leak:
  - `Deutsch/Bell.lean` imports the wholly historical
    `Deutsch.Bell.SourceCorrection`, so every `import Deutsch` currently exposes errata.
  - Stage 6 destination: minimal replacement under `DeutschErrata.Bell`; remove the production
    import without an alias.
- Embedded historical witnesses to move or replace minimally:
  - `Deutsch/Gates/OneQubit.lean`: two Equation (18) `*_ne_printed` theorems;
  - `Deutsch/EPR/Statistics.lean`: Equation (28)/(41) equal-angle printed counterexamples;
  - `Deutsch/Teleportation/Circuit.lean`: three printed sign witnesses and their private
    `neg_unitary_ne_self` support;
  - `Deutsch/Teleportation/Descriptors.lean`: Equation (34)/(37) witnesses and all private lemmas
    used only by them;
  - `Deutsch/Teleportation/Statistics.lean`: printed Equation (35) effect and its two theorems.
- Neutral production renames:
  - `equation35CorrectedEffect -> equation35Effect`;
  - `equation35_corrected_effect_op -> equation35_effect_op`;
  - remove `corrected_` from the four final Bell theorem names.
- Production comments/docstrings throughout Gates, EPR, Teleportation, and Bell must describe the
  canonical identities without printed/corrected comparison language.
- Intentional names to retain:
  - physical teleportation `Correction`, `correctionGate`, and branch-correction identifiers;
  - `paperBit*`, `paperOne*`, `paperZero*`, and `paperSqrtNot*`, which encode the source convention;
  - preparation/information provenance terminology.
- Historical focused tests and axiom targets have exact Stage 6 destinations under
  `DeutschErrataTests`; neutral corrected-named examples/tests will be renamed in place.
- `goal-1/check_lean_integrity.py` hardcodes `SourceCorrection`, historical declarations, corrected
  names, and one combined axiom file. It must enforce four roots and separate production/errata
  axiom registries after the split.

### Stale Audit and Documentation Obligations

- `goal-1/check_source_audit.py`:
  - expects `##` sections while the source currently uses `###`;
  - expects obsolete `49/46/3` display counts rather than `47/46/1`;
  - treats inline U01/U03 as compact-source display signatures;
  - embeds the printed Equation (45) truth table;
  - rejects `Proved` lifecycle states and therefore cannot certify Goal 2's compiled E01–E46
    contract unchanged.
- The final checker architecture must separate:
  1. neutral canonical source/provenance and exact production declaration coverage; and
  2. original-form fixtures and counterexamples owned by `DeutschErrata`.
- Stale source-fidelity statements:
  - `goal-1/1-SOURCE-AUDIT.md` says 760 lines and no PDF;
  - `goal-1/0-plan.md` says no PDF/facsimile;
  - `goal-1/12-LIBRARY-AUDIT.md` repeats the facsimile limitation;
  - `docs/project-report.md` says no independent PDF comparison.
- Old ledger rows for E42–E46 still say the corrected source chain is invalid or replaced. The
  original PDF chain is invalid; the canonical corrected chain is valid but not yet directly
  formalized.
- The old E35 audit treats a nontrivial/rank-one qualifier as a required source correction. That
  conflicts with the settled editorial boundary. The strong rank-one witness remains useful Lean
  mathematics, but the source prose will remain unchanged.

### Stage Conclusion

- Every Stage 1 completion requirement has direct evidence.
- No canonical source, Lean implementation, public documentation, or old audit tool was changed.
- Only `goal-2/0-plan.md` and this stage record changed.
- The two-library dependency contract is locked as `DeutschErrata -> Deutsch`, never the reverse.
- Stage 2 may begin from the corrected 47-display source model and the recorded provenance.
