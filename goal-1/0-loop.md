# Goal 1 Execution Loop

Use this protocol for every stage in `goal-1/0-plan.md`. The plan is authoritative, but it must be revised when Lean, mathlib, the source audit, or proved counterexamples change the facts.

## Repeatable Loop

1. Sync current state with actual files and tests. Read the current `git status`, relevant source and stage files, pinned toolchain files, and the latest test/build output; never rely only on a prior summary.
2. Update `goal-1/0-plan.md` with current facts before starting the next stage. Move disproved assumptions into findings and add newly exposed proof, diagnostic, or migration obligations.
3. Select the first incomplete stage whose prerequisites are satisfied.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the stage template below. Preserve prior evidence when refreshing it.
5. Implement only that stage. If an obstacle belongs to a later stage, record and route it instead of allowing silent scope growth.
6. Add verification and no-cheating checks that directly cover the stage requirements, relevant convention choices, and known failure modes.
7. Run focused tests, the full Lean verification available at that point, forbidden-token/axiom checks, and whitespace/diff checks appropriate to the repository.
8. Record commands, outputs, proof status, corrections to the paper, failures, and new facts in the stage file.
9. Fold the results back into `goal-1/0-plan.md`: update current facts, assumptions, stage status/evidence, downstream changes, and the paper claim map.
10. Continue toward the original objective. If stopping for the session, leave the goal resumable with current evidence, the first next experiment, concrete unblock actions, and assumptions still needing challenge.

## Invariants

- Do not narrow the user's objective without saying so and recording the reason in the plan.
- Do not mark a stage complete without requirement-by-requirement evidence.
- Do not use tests or green checks as evidence unless they actually cover the requirement.
- Prefer small, low-complexity stages that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn them into proof and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic, and fallback paths.
- Treat the paper as fallible. Recalculate identities and inspect theorem hypotheses independently.
- Keep the repository compiling incrementally; if an exploratory file cannot compile, isolate and label it rather than weakening public modules.
- Never close a proof with `sorry`, `admit`, an unexplained axiom, or a fabricated lemma.
- Never treat syntactic parameter occurrence as operational information location.
- Never conflate operator equality, equality in one state, equality of all local statistics, and equality of joint statistics.
- Preserve the current tensor/qubit/control-target conventions or update the convention document and every affected test in the same stage.
- Preserve unrelated user work and inspect untracked files before any cleanup or bulk rewrite.
- A stage failure is evidence: record the exact theorem statement, Lean error or mathematical counterexample, attempted representations, and strongest nearby result.

## Verification Ladder

At every stage, choose commands after inspecting the actual project scripts and toolchain. Record exact commands rather than assuming these placeholders exist.

1. Run the smallest compile/test target covering the changed definitions and proofs.
2. Run convention examples or computation checks that could falsify tensor/order/sign choices.
3. Run the full pinned project build.
4. Search completed project modules for `sorry`, `admit`, unsafe escapes, and project `axiom` declarations; review hits rather than trusting a raw count.
5. Run or compile `#print axioms` checks for newly principal theorems and record the output.
6. Inspect `git diff --check`, `git diff`, and `git status --short`; do not erase unrelated changes.
7. Reconcile the source equation/claim map and documentation links with renamed or corrected declarations.

The final stage must repeat the full ladder from a documented clean-start state and audit all principal exports, not only recently changed files.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Status

- Incomplete | In progress | Blocked with evidence | Complete with evidence

## Current Facts

- Facts from current code, tests, docs, repository status, source audit, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New proofs, counterexample checks, tests, or commands required.

## Paper Mapping

- Equations, figures, and prose claims addressed by this stage.
- Expected disposition: prove, correct, partial, exclude as interpretative, or leave unresolved with obstruction.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden fallback paths.
- Checks that distinguish operator equality from state-specific/statistical equality.
- Convention, scope, and hypothesis checks relevant to this stage.

## Completion Requirements

- Requirement-by-requirement checks copied and refined from `0-plan.md`.
- Required focused and full-build commands.
- Required forbidden-token and axiom-audit commands.
- Documentation and paper-map updates required.

## Stage Results

- Fill in at the end of the stage.
- Include exact commands run and outcomes.
- Include declarations added and their scope.
- Include corrections, obstructions, and what was learned.
- Include what should change in `0-plan.md` before the next stage.

## Resume Point

- First next action or experiment.
- Known blockers and explicit unblock paths.
- Assumptions still needing challenge.
```

## Completion Rule

Completion means the original library objective is genuinely met, not merely that all stage files have optimistic status labels. If a theorem in the original scope remains open, either resolve it, prove a documented strongest corrected substitute after demonstrating the obstruction, or carry it forward as explicit next work and do not call the overall goal complete.
