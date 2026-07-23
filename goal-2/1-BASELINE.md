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
- The canonical Markdown currently has 1255 lines, 46 numbered equation tags, 49 display blocks,
  eight numbered sections, and three linked figures.
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

- In progress.

