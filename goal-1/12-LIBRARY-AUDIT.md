# 12-LIBRARY-AUDIT

## Status

- Complete with clean-build, source, API/import, examples, documentation, integrity, axiom,
  checksum-preservation, and hygiene evidence.

## Current Facts

- The public root `Deutsch.lean` imports the foundation, register, locality, descriptor, gate,
  information, EPR, teleportation, decoherence, and corrected Bell umbrellas. The verification
  root imports every current focused test and the representative axiom audit.
- Lean and mathlib are pinned to `v4.32.0`; the resolved mathlib revision is
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- After `lake clean deutsch`, the default build completed 3309 jobs, including both public and
  verification roots. The integrity gate scans 65 Lean sources, requires every stage's focused
  oracles and principal declarations, and accepts 402 ordered axiom reports using only
  `Classical.choice`, `Quot.sound`, and `propext`.
- The source ledger contains every numbered equation E01–E46, unnumbered display U01–U03,
  definition D01–D11, figure F01–F03, prose claim C01–C66, and interpretation group I01–I10.
  Every row now has a final scoped lifecycle disposition and the checker rejects any future
  `Planned` regression.
- Public topic documentation covers conventions, representation, registers, locality,
  descriptors, gates, information, EPR, teleportation, decoherence, Bell, compiled reuse, and the
  final end-to-end report.
- The shared worktree remains intentionally dirty/untracked from the staged construction. A
  110-file non-generated checksum snapshot and `git status --short` were identical before and
  after the clean build; only the `deutsch` package's generated Lake outputs were removed/rebuilt.

## Updated Assumptions

- The accumulated public APIs are sufficient for small downstream examples; the seven compiled
  wrappers import only `Deutsch` and introduce no new production abstraction layer.
- A final source status may honestly remain `Partial`, `Corrected`, `Excluded`, or `Unresolved`.
  Completion requires an exact scope or obstruction and next-work path, not pretending that
  continuum, measure-theoretic, capacity, instrument, stochastic-refinement, or ontological claims
  were proved.
- The clean project build is reproducible by removing only generated project outputs with
  `lake clean deutsch`, retaining the pinned dependency checkout and every source file.
- The ordered `#print axioms` inventory represents all declarations designated principal by
  Stages 3–11. The final checker preserves exact inventory equality and also enforces the final
  example/import/document requirements.

## Big Picture Objective

- Turn the staged formalization into a coherent reusable library, close every bookkeeping and
  documentation obligation, and verify the original finite corrected objective end to end from a
  cleaned build without overstating unresolved source claims.

## Detailed Implementation Plan

1. Audit every public and verification umbrella so each intended module is reachable from exactly
   the documented root, and review namespace/theorem naming for silent collisions or orphan files.
2. Reconcile every source-ledger detailed row and LC summary. Remove all `Planned` statuses,
   preserve honest limitations, update stale future tense, and make the source checker reject any
   future `Planned` regression.
3. Add a compiled `DeutschTests.Examples` module importing the public root and demonstrating named
   register operators, gate/Heisenberg evolution, disjoint-support locality, operational
   state/information semantics, and the corrected Bell API. Mirror it in a concise reuse guide.
4. Produce a final project report covering formalized content, public exports, source corrections,
   EPR/teleportation/decoherence/Bell results, semantic distinctions, unresolved limitations,
   build/axiom evidence, and concrete reuse paths.
5. Extend the integrity and documentation gates to require the final examples and report while
   retaining exact stage-oracle, public-declaration, and axiom-target checks.
6. Run the focused example and audit targets, then clean only generated project build outputs and
   run the default pinned build from that state. Repeat source, integrity, axiom, documentation,
   forbidden-token, custom-axiom, whitespace, import-closure, and diff/status reviews.
7. Record exact commands/counts and fold the final facts into `0-plan.md`. Declare the goal complete
   only if every completion requirement below has direct evidence.

## Paper Mapping

- Finalize, rather than expand, E01–E46, U01–U03, D01–D11, F01–F03, and C01–C66. Any remaining
  `Partial` or `Unresolved` row must name the existing theorem boundary or exact missing theory.
- Retain the compiled corrections to Equations (18), (25), (27), (28), (29), (31), (32), (34),
  (35), (36), (37), (41), and (45), with the exact convention or counterexample responsible.
- Keep the fixed-reference mixed-state obstruction, general-dynamics/continuum extrapolation,
  communication-capacity claims, outcome-conditioned instruments, coherent-circuit/semantic-
  encoder identity, general stochastic Bell refinement, and philosophical diagnoses explicit as
  limitations or next work.
- Treat the paper transcription's lack of an independently checked facsimile as an external source
  fidelity limitation, not a Lean theorem gap.

## No-Cheating Checks

- A final status label cannot replace compilation: every example imports the public root and every
  principal declaration remains an exact ordered axiom target.
- The clean build removes only generated Lake outputs; no source, dependency pin, user file, or
  unrelated worktree change is deleted or reset.
- No lifecycle item remains `Planned`; `Partial`, `Corrected`, `Excluded`, and `Unresolved` entries
  retain explicit theorem scope or obstruction instead of being relabeled optimistically.
- No completed module contains `sorry`, `admit`, `by_contra!`, `unsafe`, or a project `axiom`/
  `opaque` escape, and public modules do not import the umbrella `Mathlib.Tactic`.
- Executable examples reuse existing public declarations and add no assumptions, axioms, or hidden
  convention redefinitions.
- Documentation keeps operator equality, one-state expectation equality, local/all-effect
  statistics, joint detectability, recovery, provenance, dynamical locality, no-signalling, and
  Bell counterfactual locality distinct.
- The final report gives exact finite-dimensional scope and does not claim continuum locality,
  arbitrary stochastic Bell equivalence, generic decoherence robustness, entanglement necessity,
  or an ontological conclusion.

## Completion Requirements

- [x] Every intended production module is reachable from `Deutsch`; every focused test/example is
      reachable from `DeutschTests`; no silent orphan or duplicate import boundary remains.
- [x] The source map has no `Planned` item or stale future-tense disposition, and its checker
      enforces the final lifecycle contract.
- [x] Compiled reuse examples and public guidance demonstrate embedding, gate evolution, locality,
      operational information semantics, and the corrected Bell result.
- [x] A final report answers the original end-of-project scope, corrections, results, limitations,
      audit, and reuse questions.
- [x] The integrity gate requires all final source/test/doc files, focused oracles, principal
      declarations, exact axiom targets, and accepted foundational axioms only.
- [x] The documented clean-start procedure succeeds through the default `lake build` after only
      generated project outputs are cleaned.
- [x] Source coverage, integrity/axiom, documentation-link, forbidden-token/custom-axiom,
      trailing-whitespace, import-closure, diff, and worktree-preservation checks pass with exact
      evidence.
- [x] Findings and final counts are folded into `0-plan.md`; no original objective remains silently
      open or falsely claimed.

## Stage Results

- `Deutsch.lean` has ten required topic-umbrella imports. The checker locks 49 ordered production
  import edges across the root and ten umbrellas, requires all 15 verification-root imports, and
  rejects any production import of `DeutschTests`. All 50 production modules and 15 verification
  modules are therefore rooted in their intended targets.
- `DeutschTests.Examples` imports only `Deutsch` and compiles seven public-API examples: named
  Pauli embedding, same-axis Heisenberg rotation, ordered named-CNOT placement, disjoint-support
  locality, operational one-time-pad local independence, corrected three-setting probability,
  and the integrated finite Bell contradiction. `docs/reuse.md` supplies a copy-paste prelude,
  exact snippets, narrow-import guidance, and convention/scope boundaries.
- The source checker covers E01–E46, U01–U03, D01–D11, F01–F03, C01–C66, and I01–I10. LC status
  counts are `Corrected=22`, `Partial=31`, `Excluded=8`, `Unresolved=5`, `Planned=0`; mathematical
  item counts are `Oracle verified=6`, `Corrected=25`, `Partial=31`, `Excluded=1`,
  `Unresolved=0`, `Planned=0`. It also guards the Equation (45) truth table and direct
  `Deutsch.Bell` namespace spelling.
- `docs/project-report.md` gives the final public entry points, formalized results, compiled source
  corrections, semantic distinctions, explicit limitations/unblock paths, reuse links, and
  reproducibility procedure. The documentation checker requires and validates all 14 public
  Markdown files and 118 repository-local links.
- `lake clean deutsch` removed only the local package's generated outputs. The subsequent
  `lake build` completed 3309 jobs. SHA-256 manifests over all 110 non-generated files and the
  complete `git status --short` output matched exactly before and after the clean/build sequence.
- `python3 -B goal-1/check_lean_integrity.py` scanned 65 Lean sources; rejected proof holes,
  `by_contra!`, unsafe, project `axiom`/`opaque`, public `Mathlib.Tactic`, and production-to-test
  imports; required seven final examples plus all Stage 2–11 oracles/declarations; and matched 402
  ordered `#print axioms` reports. The only observed axioms were `Classical.choice`, `Quot.sound`,
  and `propext`; `sorryAx` was absent.
- Focused compilation of `DeutschTests/Examples.lean`, the source/integrity/documentation scripts,
  `git diff --check`, the all-project trailing-whitespace scan, import-closure checks, and final
  worktree review all passed. The checksum proof confirms that generated-output cleaning preserved
  every user/source file.

## Resume Point

- The original finite corrected library objective is complete. Optional extensions are listed in
  `docs/project-report.md`: continuum/general-dynamics limits, an instrument/posterior-state API,
  an arbitrary-reference coherent teleportation wrapper, a coherent-circuit/semantic-encoder
  bridge, and stochastic Bell-model refinement. None is a hidden premise of the completed scope.
