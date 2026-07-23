# Goal 2 Execution Loop

Use this protocol to execute `goal-2/0-plan.md` incrementally while preserving a truthful,
resumable record.

## Repeatable Loop

1. Sync current state with the actual files, Git status, generated outputs, toolchain, tests, source,
   and documentation. Do not rely on a previous stage's status paragraph without checking it.
2. Update `goal-2/0-plan.md` with newly established current facts before starting the next stage.
3. Select the first incomplete stage whose prerequisites are satisfied.
4. Create or refresh `goal-2/[INDEX]-[SHORTHAND].md` using the stage template below.
5. Implement only that stage. If a prerequisite or contradiction appears, record it and revise the
   plan rather than silently absorbing another stage.
6. Add focused verification and explicit no-cheating checks that exercise the actual requirement.
7. Run the focused tests, all affected-library builds, the full verification appropriate to the
   repository, and whitespace/diff checks.
8. Record commands, outcomes, changed files, proof assumptions, failures, and lessons in the stage
   file.
9. Fold confirmed results, changed assumptions, residual risks, and next work back into
   `goal-2/0-plan.md`.
10. Continue toward the original objective. If stopping for the session, leave the goal resumable
    with current evidence, the next concrete experiment or implementation step, unblock actions,
    and assumptions that still need to be challenged.

## Invariants

- Do not narrow the user's objective without saying so and recording the resulting gap.
- Do not mark a stage complete without requirement-by-requirement evidence.
- Do not use a green test as evidence unless that test actually covers the stated requirement.
- Prefer small, low-complexity changes that narrow uncertainty and keep the project compiling.
- Convert blockers into work items: decompose them, route around them, or make them explicit proof,
  diagnostic, verifier, or design obligations.
- Preserve the distinction between implementation, verifier, diagnostic, independent cross-check,
  and fallback paths.
- Inspect the shared worktree before editing. Preserve unrelated user changes and do not clean,
  reset, delete, or overwrite them.
- Use the corrected Markdown as the canonical mathematical source. The BQP copies are comparison
  inputs during review, never build dependencies.
- Do not change the prose before Equation (35) to add a nontrivial/rank-one qualifier. This is a
  settled editorial decision.
- Do not alter another source formula or substantive passage without surfacing the evidence and
  obtaining review first.
- Keep `Deutsch` independent of `DeutschErrata`; verify the direction after every import change.
- Keep physical teleportation correction terminology distinct from editorial correction history.
- Do not count pair-only statistics as the Figure 2 circuit proof.
- Do not count the independent pigeonhole theorem as the direct Equations (42)–(46) derivation.
- Do not constrain zero-weight assignments when formalizing Equation (43).
- Do not count an `x`-axis closed form as arbitrary-axis Equation (17).
- Do not encode a source conclusion as an axiom, premise, unproved definition contract, or
  reflexive theorem selected only to mimic the desired text.
- Keep operator equality, phase equivalence, density equality, effect-statistical equality,
  stochastic almost-sure equality, and interpretive prose separate.
- Do not use proof holes, unsafe escapes, project axioms, opaque shortcuts, or unexplained accepted
  assumptions.
- Completion means the full corrected finite theorem contract and two-library cutover are achieved,
  not merely that the old tests still pass.

## Verification Ladder

Apply the narrowest relevant checks after each edit and the full ladder at stage boundaries:

1. Inspect `git status --short` and the focused diff.
2. Build the directly affected Lean module or library.
3. Run its focused test root and targeted `#print axioms` checks.
4. Run the exact E01–E46 registry when paper-facing declarations change.
5. Run source/provenance checks when Markdown, PDF references, figures, or source mappings change.
6. Run import-boundary and historical-name scans when moving code between `Deutsch` and
   `DeutschErrata`.
7. Run the full public and test targets.
8. Run integrity, source, documentation-link, forbidden-token, unexpected-axiom, whitespace, and
   diff checks.
9. Before final completion, clean only generated project outputs and repeat the complete build and
   audit sequence while confirming source checksums and worktree preservation.

Exact commands may evolve with the staged tooling, but every stage file must record the commands
actually run and their complete pass/fail disposition.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden fallback paths.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test commands.
- Documentation updates required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and outcomes.
- Include what was learned.
- Include what should change in `0-plan.md` before the next stage.
```

## Pause and Resume Rule

When stopping before the objective is complete:

- leave the active stage marked incomplete;
- record the exact last successful command and current failure, if any;
- name the next file, theorem, test, or diagnostic to work on;
- preserve alternative approaches and why they were accepted or rejected;
- update `0-plan.md` with facts, not hopes; and
- never describe an optional fallback as though it completed the original requirement.

