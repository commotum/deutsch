# Continuation Prompt

```text
Act as an autonomous Lean 4 formalization agent. Work through /Users/jake/Developer/deutsch/goal-1/0-plan.md using the repeatable protocol and stage template in /Users/jake/Developer/deutsch/goal-1/0-loop.md.

The objective is to build a reusable, pinned Lean 4/mathlib library that independently reconstructs and verifies the mathematical content of Deutsch and Hayden's “Information Flow in Entangled Quantum Systems”: finite Heisenberg-picture quantum registers, global subsystem descriptors, disjoint-support locality, elementary gates and Bell transforms, operational information-dependence notions, EPR, teleportation, explicitly modeled decoherence claims, and the mathematical assumptions in the Bell discussion.

Treat the paper as fallible. Verify every definition, sign, tensor order, control/target convention, equation, circuit, and conclusion. Prove the strongest useful corrected result when a claim needs repair and document the difference. Keep operator equality separate from equality of predictions; keep local, joint, distinguishable, recoverable, and historical information notions separate. Do not encode interpretation as theorem, define information location by syntax, add unexplained axioms, or leave `sorry`/`admit` in completed modules.

For each stage: inspect actual files and tests; update 0-plan.md with current facts; select the first incomplete stage; create or refresh its stage file from 0-loop.md; implement only that stage; add direct no-cheating checks; run focused tests, the full available build, convention checks, forbidden-token checks, axiom audits, and diff/whitespace checks; record exact evidence; then fold results into the plan. Revise representations and downstream stages when Lean, mathlib, calculations, or counterexamples reveal a better path. Preserve unrelated changes and keep the project compiling incrementally.

Continue beyond planning and through the formalization as far as the environment permits. Completion means the original objective is actually achieved: a compiling reusable library, mapped paper claims, verified EPR and teleportation results, precise locality and information notions, documented corrections and unresolved interpretations, representative examples, and a recorded build/axiom audit. Carry every open issue forward as explicit next work with evidence and an unblock path; do not declare success based only on green checks or completed stage labels.
```
