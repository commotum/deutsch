# 6-GATES

## Status

- Complete with evidence on 2026-07-16.

## Current Facts

- Stages 1–6 are complete with evidence; Stage 7 is now the first incomplete stage.
- Stage 2 already verifies concrete paper-bit ordering, left-target/right-control CNOT truth tables,
  all six concrete CNOT Pauli conjugations, `U† A U` chronology, `R_x(π/2)` signs, and the Bell
  transform/inverse product order. Most named gate matrices remain verification-only definitions.
- Stage 3 exports exact arbitrary-coordinate embeddings and ordered-injection placement; Stage 4
  exports disjoint-support invariance; Stage 5 exports descriptor validity and shared-unitary
  evolution. The public gate layer should compose these APIs instead of rebuilding tensor algebra.
- Equation (18) is sign-sensitive. Under the fixed Schrödinger unitary
  `R_x(θ)=exp(-iθX/2)` and project Heisenberg direction `U† A U`, infinitesimal Pauli algebra gives
  `Y -> cos θ Y - sin θ Z` and `Z -> sin θ Y + cos θ Z`. At `π/2`, the compiled Stage 2
  oracle gives `Y -> -Z`, `Z -> Y`, opposite to the signs printed in (18). Stage 6 must reproduce
  and classify this discrepancy rather than silently choosing the source formula. The public
  symbolic proof and executable special-angle counterexamples now do so.

## Updated Assumptions

- Public gate definitions should reuse `Foundations.pauliX`, projectors, and
  `cnotTargetLeftControlRight`; reusable Hadamard, rotation, Bell, and inverse definitions can be
  promoted from verified formulas only after independent algebraic proofs.
- Exact matrix equality, basis-label action, equality up to global phase, and Heisenberg descriptor
  transformation are separate results.
- The source square-root-of-NOT transformation (14) corresponds to the opposite quarter-turn from
  the Stage 2 `R_x(π/2)` oracle. Its unitary should be exhibited explicitly and its square recorded
  both as an exact matrix (potentially a phase times `X`) and as a double Heisenberg action.
- Arbitrary-register two-qubit gates require distinct named target/control labels. The paper's
  tensor expression (15), which mixes local operands with already-global descriptors, should be
  replaced by a typed ordered placement and/or a proved global projector formula.
- CNOT is a coherent controlled bit flip. Calling it a measurement requires a later record and
  decoherence/channel definition and therefore remains Stage 10 terminology.
- The universality sentence after (19) is not required to verify this finite gate set. It may be
  documented as background rather than imported as an unused major theorem.

## Big Picture Objective

- Independently verify the paper's named elementary and Bell gate identities under the fixed
  conventions, lift them to arbitrary named registers, and provide descriptor transformations
  strong enough for the EPR and teleportation stages.

## Detailed Implementation Plan

1. Inventory equations (9)–(21), Fig. 1, and C20–C25 against the Stage 2 convention oracles.
2. Export one-qubit NOT, square-root-of-NOT, `R_x`, and Hadamard matrices with exact unitarity,
   basis action, phase distinctions, and all Pauli Heisenberg transformations.
3. Lift one-qubit gates through `embedQubit`; prove arbitrary-label unitarity, support, descriptor
   component action, and remote-coordinate invariance through existing locality results.
4. Export named-target/named-control CNOT using ordered placement or an equivalent proved global
   projector formula. Prove coherent truth-table action and all six arbitrary-register descriptor
   transformations with every sign/factor order explicit.
5. Export Bell and inverse Bell with the fixed CNOT-then-control-H chronology. Prove both matrices
   unitary, two-sided inverse, basis action, and all six transformations in (20)–(21).
6. State descriptor-dependent gate-expression theorems only with typed valid-family hypotheses;
   do not confuse a current global component with a local tensor operand.
7. Add one-/two-/three-register positive examples and negative/order/sign regressions, including
   reversed CNOT labels, reversed Bell chronology, rotation-sign disagreement, and phase-sensitive
   square-root/Hadamard comparisons.
8. Add public docs, source-ledger lifecycle updates, integrity/axiom targets, and the full build and
   hygiene evidence; fold results into `0-plan.md` before completion.

## Paper Mapping

- E09–E13/C20: exact NOT ket action, matrix elements, `X` matrix, current descriptor expression,
  and `(X,Y,Z)->(X,-Y,-Z)`.
- E14/C21: explicit square-root unitary, exact square/global phase, and double descriptor action.
- E15–E16/C22: typed left-target/right-control CNOT formula, coherent paper-bit truth table, and
  six Pauli/descriptor transformations.
- E17–E18: exponential/closed-form `R_x` convention, general-angle formulas, and special-angle
  regressions; correct the printed sign conflict if the independent proof confirms it.
- E19: usual Hadamard transformation and its exact global-phase relation to a π rotation about
  `(X+Z)/√2`.
- E20–E21/F01/C24–C25: Bell/inverse chronology, transformations, basis maps, and two-sided inverse.
- C23: universality is background unless a scoped downstream theorem actually requires it.

## No-Cheating Checks

- Basis action is proved from explicit matrices/permutations, not inferred only from a desired
  conjugation result; descriptor transformations are independently proved from conjugation.
- Rotation signs are derived symbolically and checked at `0`, `±π/2`, and `π` where practical.
- Exact equality is never replaced by equality up to phase without an explicit scalar theorem.
- CNOT target/control and paper-bit activation are named in types/arguments and tested on all four
  basis cases.
- Bell and inverse each receive direct transformation checks plus both composition orders.
- Arbitrary-register lifts reuse injective embeddings/ordered placement and do not prove only the
  fixed `Fin 2` case.
- Completed modules contain no proof holes, unsafe declarations, project axioms, or public umbrella
  tactic import; principal results enter `DeutschTests/Audit.lean`.

## Completion Requirements

- [x] Each public gate is unitary and has independently verified exact basis action where relevant.
- [x] NOT, square-root, rotations, Hadamard, CNOT, Bell, and inverse Bell have compiled Pauli or
      descriptor transformations under the documented Heisenberg convention.
- [x] CNOT target/control, paper-bit activation, arbitrary-register lift, and support are explicit.
- [x] Bell chronology and inverse are checked by basis action, six-generator action, and two-sided
      matrix composition.
- [x] Every discrepancy with equations (9)–(21) is reproduced and conservatively classified.
- [x] Focused positive/negative tests, full build, source/doc/integrity/axiom audits, and hygiene
      checks pass and are recorded.
- [x] Findings are folded into `0-plan.md`; Stage 7 is now the first incomplete stage.

## Stage Results

- `Deutsch.Gates.OneQubit` exports exact NOT, the distinct Equation (14) square-root branch,
  closed-form `rotationX`, Hadamard, the globally phased diagonal-axis rotation, and arbitrary-label
  lifts. Every gate is unitary; exact basis amplitudes, phase-sensitive equalities, Pauli maps, and
  explicit singleton support witnesses are proved. `descriptorNot` additionally acts on every
  valid current descriptor rather than only the initial family.
- The rotation calculation proves symbolically
  `Y ↦ cos θ Y - sin θ Z` and `Z ↦ sin θ Y + cos θ Z`, with checks at
  `0`, `±π/2`, and `π`. Equation (18) is therefore corrected and classified as contradicted as
  printed under Equation (17) and `U† A U`. Equation (17) remains conservatively partial: the
  exact `x`-axis closed form is established, but no arbitrary-axis or matrix-exponential theorem
  is claimed.
- `Deutsch.Gates.CNOT` exports an ordered arbitrary-register permutation gate with explicit target,
  control, distinctness proof, exact global entries, coherent basis action, Hermiticity,
  involution, unitarity, a pair-support witness, and the typed global-projector form of Equation
  (15). `cnotFromDescriptors` proves the corresponding unitary polynomial and all six Equation
  (16) maps for every valid current descriptor family, plus initial equality and shared-frame
  evolution covariance.
- `Deutsch.Gates.Bell` fixes Fig. 1 chronology definitionally as control-H after CNOT and reverses
  that order for the inverse. Both products are unitary, have pair-support witnesses and exact
  arbitrary-register basis amplitudes, satisfy both inverse products, and prove all twelve
  generator identities and four bundled descriptor identities from Equations (20)–(21).
- `DeutschTests.Gates` independently checks paper-labelled NOT action, square-root branch/phase,
  both erroneous Equation (18) signs, the negative quarter-turn signs, remote locality, all four
  CNOT basis cases, reversed target/control order, generic current-descriptor CNOT, both Bell
  inverse products, representative signs, a direct Bell amplitude, reversed Bell chronology, and
  remote Bell locality. `IsSupportedOn` is documented as an at-most support witness, not a
  minimal-support assertion.
- Equations (9)–(16) and (19)–(21) require no mathematical correction within the proved finite
  scope. The Equation (15) notation receives a typed global-operator replacement; the Equation
  (14) gate is a valid square-root branch distinct from `rotationX (π/2)`. The universality prose
  after Equation (19), measurement semantics, arbitrary-axis exponentials, and continuum
  extrapolation remain explicitly outside this stage.

## Evidence

- `lake build Deutsch.Gates.OneQubit Deutsch.Gates.CNOT Deutsch.Gates.Bell DeutschTests.Gates`
  succeeds; `lake build Deutsch.Gates.OneQubit DeutschTests.Gates DeutschTests.Audit` succeeds
  with 3265 jobs, including all representative axiom reports.
- The final repository-wide `lake build` succeeds with 3273 jobs. Public roots `Deutsch` and
  `DeutschTests` both include the gate layer.
- `goal-1/check_lean_integrity.py` scans 29 Lean sources, finds no forbidden proof holes or
  declarations, requires 29 gate verification oracles and 55 Stage 6 public declarations, and
  accepts all 132 representative axiom reports with only `Classical.choice`, `Quot.sound`, and
  `propext`.
- `goal-1/check_source_audit.py` passes exact coverage of all 46 numbered equations, three
  unnumbered displays, three figures, 11 definitions, 66 prose claims, and ten interpretation
  groups after the conservative E07–E21/D07/F01/C15–C25 lifecycle updates.
- `goal-1/check_doc_links.py` passes over 7 Markdown files and 49 repository-local links.
  `git diff --check` and the targeted trailing-whitespace scan have no findings; an adversarial
  review found no mathematical blocker and its API-boundary, support-wording, negative-angle, and
  direct-amplitude recommendations were incorporated before completion.

## Resume Point

- Begin Stage 7 by inventorying mathlib's finite density-operator, effect/POVM, trace, partial-trace,
  and channel APIs against the existing concrete register matrices and `matrixEndEquiv` bridge.
- First prove general Born probabilities are real, nonnegative, bounded by one, and normalized;
  then define local/joint statistical equivalence, distinguishability, recovery, and explicit
  provenance without equating any of them with syntactic descriptor occurrence.
