# 10-AUDIT

## Status

- In progress.

## Current Facts

- Stages 1 through 9 are complete with evidence in their stage reports.
- The repository exposes exactly four Lake libraries/default targets: `Deutsch`, `DeutschTests`,
  `DeutschErrata`, and `DeutschErrataTests`.
- The most recent pre-clean four-target build completed 3341 jobs.
- The integrity audit currently scans 91 Lean sources and 595 representative axiom targets.  It
  reports only `Classical.choice`, `Quot.sound`, and `propext`.
- The source audit maps exactly 46 unique tagged equations to 46 `Deutsch.Paper` declarations,
  compile checks, and axiom targets.  The literal four-wire EPR route, direct Equations (42)--(46)
  route, independent Bell route, stochastic refinement, purification, actual-resource
  entanglement, and literal teleportation channel all compile.
- The canonical source SHA-256 is
  `f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032`;
  the PDF SHA-256 is
  `d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb`.
- The three figure SHA-256 values are, in order,
  `8c5070722164b9a804f26ad2931aaa357d382575be0e092c58f11cad1fafcbed`,
  `5f262a847f99cb25440a76783bac8b16c323a163e229bd9a164e4691e625c4e2`, and
  `22a3b7c5e3dc95c61151ceef02338ed4e0573c731fc0d0c33dfe931a2cab87d3`.

## Updated Assumptions

- `lake clean deutsch` should remove only this package's generated build directory while
  preserving dependency builds, source files, and unrelated worktree state.
- A clean four-target build is the decisive check that no result depends on stale local oleans.
- The integrity, source, Errata-boundary/provenance, documentation-link, axiom, and diff checks
  together cover the public contract, provided their exact registries are also inspected against
  the final module roots and theorem names.
- No final claim should exceed the compiled finite-dimensional scope.  In particular, the final
  report must not claim authorial intent, ontology, continuum Bell models, measurement/collapse,
  or an arbitrary-reference teleportation theorem.

## Big Picture Objective

- Rebuild the entire corrected-paper cutover from a clean project-generated state, rerun every
  independent audit, review the final public theorem and documentation contract, and leave exact
  reproducible evidence that the two-library result is complete.

## Detailed Implementation Plan

- Record the pre-clean Git status, toolchain revisions, source/PDF/figure hashes, and generated
  project directory.
- Run `lake clean deutsch`, confirm the package build outputs were removed, and verify that no
  source or unrelated worktree path changed.
- Build all four public/test targets together from that clean state.
- Run:
  - the production and Errata axiom inventories;
  - the Lean integrity verifier and its exact E01--E46 registry;
  - the Errata import-boundary/provenance verifier;
  - the source/PDF/figure audit;
  - the documentation-link audit;
  - explicit editorial-history, reverse-import, proof-hole, and BQP runtime scans;
  - whitespace and `git diff --check`.
- Review README and public documentation claims against the actual theorem statements, tightening
  only unsupported wording if any remains.
- Record exact commands, counts, hashes, revisions, results, and residual limitations here and in
  `goal-2/0-plan.md`.

## No-Cheating Checks

- Confirm the clean removed this package's generated outputs before the successful build.
- Require all four targets in one clean build; a focused or cached module build is not sufficient.
- Require all 46 source-facing declarations, tests, and axiom targets to remain exact and
  contiguous.
- Require both the literal four-wire and pair-state EPR bridges, both direct and independent Bell
  proofs, and the literal-circuit teleportation channel checks to remain in the verifier.
- Confirm `Deutsch` never imports `DeutschErrata`, and that editorial-history fixtures remain
  confined to the small Errata layer.
- Confirm no audit reads the sibling BQP checkout and that the stable in-repository source,
  PDF, figure, and historical-object provenance checks pass.
- Confirm no `sorry`, `admit`, project axiom, `unsafe`, `opaque`, or unexpected foundational axiom
  is accepted.
- Treat an omitted arbitrary-reference teleportation theorem as an explicit scope limitation, not
  as an inferred corollary.

## Completion Requirements

- All four targets build after the package-generated outputs have been removed.
- Both axiom inventories and all integrity, source, provenance, import, documentation, hygiene, and
  diff checks pass.
- Exact hashes and pinned Lean/mathlib revisions are recorded.
- The final public claims match the compiled finite theorem contract and its stated limitations.
- The worktree preserves all unrelated user changes and contains no generated build artifact as a
  source patch.
- Stage 10 and the overall goal are marked complete only after every result above is recorded.

## Stage Results

- In progress.
