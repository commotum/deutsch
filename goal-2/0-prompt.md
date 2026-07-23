# Continuation Prompt

```text
Work through /home/jake/Developer/deutsch/goal-2/0-plan.md using
/home/jake/Developer/deutsch/goal-2/0-loop.md.

The objective is to complete the corrected Deutsch--Hayden paper cutover and produce two clean
public Lean libraries:

1. Deutsch: a historically neutral, reusable, direct finite-dimensional derivation of all 46
   corrected numbered equations and the supporting operational EPR, teleportation, locality, and
   Bell results.
2. DeutschErrata: a separate, very small and polite proof that the printed defects are localized
   bookkeeping errors and that the corrected forms are the natural results forced by Deutsch's own
   conventions.

Treat the current corrected equations in deutsch-2000/deutsch-2000.md as canonical. Rewrite the end
correction note around the three root bookkeeping slips and the harmless k/n typo. Preserve the
paper's prose before Equation (35): do not add “non-trivial,” “rank-one,” or similar wording.

Maintain a strict dependency direction: DeutschErrata may import narrow Deutsch modules, but
Deutsch must never import DeutschErrata. Remove all printed/corrected/source-history declarations
from Deutsch with no compatibility aliases, while retaining physical teleportation correction
terminology.

Do not assume source formulas, hide missing proofs, substitute pair-only statistics for the literal
four-wire EPR circuit, substitute the existing pigeonhole proof for corrected Equations (42)–(46),
or claim arbitrary-axis Equation (17) from an x-axis result. Keep operator, state, probability,
almost-sure, and interpretive claims distinct. Use no sorry/admit, unsafe, project axioms, opaque
escapes, or unexplained assumptions.

For each stage: inspect actual current state, update 0-plan.md with established facts, create the
stage file from the 0-loop.md template, implement only that stage, add focused no-cheating checks,
run focused and full verification, record exact evidence, and fold results back into the plan.

Completion means the original objective is genuinely achieved: exact compiled E01–E46 coverage,
literal four-wire EPR statistics, the direct corrected Bell expectation chain plus the independent
Bell proof, the clean two-library boundary, minimal errata, neutral production APIs, passing source
and provenance checks, clean builds, and clean axiom/integrity/documentation audits. Carry every
open issue forward as explicit next work rather than declaring success around it.
```
