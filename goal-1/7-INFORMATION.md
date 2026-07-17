# 7-INFORMATION

## Status

- Complete with evidence on 2026-07-16.

## Current Facts

- Stages 1–7 are complete with evidence; Stage 8 is the first incomplete stage.
- The public register layer already supplies concrete finite matrices, selected-subsystem embeddings,
  the matrix/endomorphism bridge, normalized pure kets, and pure expectations. Stage 7 adds
  density/effect/channel semantics without replacing those stable APIs.
- The Stage 2 verification-only `MatrixSemanticsProbe` defines thin density, effect, finite
  measurement, and Born wrappers and proves normalization plus one maximally mixed calculation.
  It deliberately does not prove general Born probabilities real or bounded.
- The public Stage 7 layer proves `0 ≤ trace (ρE)` for arbitrary positive semidefinite
  complex matrices by factoring `E = C†C`, cycling the trace, and applying positivity to
  `CρC†`. Consequently general effect probabilities are real, nonnegative, and at most one.
- Mathlib does not appear to supply a ready-made finite quantum-information layer whose density,
  partial-trace, POVM, and channel types align directly with `Register.Operator`. Reuse the
  underlying matrix positivity, trace, and finite-sum theorems while keeping the project API small.

## Updated Assumptions

- A density state is a positive semidefinite register matrix of trace one. An effect is a positive
  semidefinite matrix whose complement is positive semidefinite. A finite POVM is an effect family
  summing to the identity. These definitions cover outcome probabilities only, not instruments or
  post-measurement states.
- Subsystem restriction should be an explicit selected-subsystem partial trace compatible with
  `splitBasis` and `embedSubsystem`, with positivity, trace preservation, and trace-duality proved.
  Local statistical equivalence can then be stated extensionally over local effects and related to
  reduced-density equality.
- A finite channel should use a typed finite Kraus family with the trace-preserving completeness
  equation. This makes complete positivity constructive, supports unitary channels and
  composition, and gives a direct dual action on effects. It should not be confused with a
  measurement instrument or a basis-dependent decoherence model.
- “Distinguishable” in the paper's information definition means weak operational detectability:
  some allowed effect has unequal probability. Perfect discrimination is a strictly stronger
  predicate and is not needed here.
- Descriptor-family dependence, local statistical dependence, joint statistical dependence,
  operational detectability, exact recovery, and historical provenance are distinct notions.
  Provenance must be explicit history/factorization data; it is not reconstructible merely from a
  final density matrix or from syntactic parameter occurrence.
- The source's same-register mixed-state extension of the fixed pure reference display is false:
  unitary conjugation preserves purity/spectrum/rank. Stage 7 compiles a maximally mixed
  obstruction and states a precise density-level substitute rather than silently accepting it.

## Big Picture Objective

- Define finite density states, effects/measurements, channels, subsystem statistics, and semantic
  parameter-dependence notions adequate for the later EPR, teleportation, decoherence, and Bell
  stages.

## Detailed Implementation Plan

1. Audit E04/E06/E26/E36/U01 and D02/D03/D05/D06/D08/D11 plus their routed prose claims; keep
   circuit-specific EPR, teleportation, decoherence, and Bell statements in their later stages.
2. Export density states, pure density matrices, effects, finite POVMs, complex Born weights and
   real probabilities. Prove reality, `[0,1]` bounds, finite normalization, density expectations,
   and unitary evolution laws from matrix algebra.
3. Prove the mixed-state fixed-reference obstruction using purity (or an equally exact unitary
   invariant), while preserving the existing pure-state theorem and exporting an honest
   trace-form density substitute.
4. Export selected-subsystem partial trace/restriction. Prove positivity, trace preservation,
   embedding duality, and the equivalence between reduced-state equality and equality of all local
   effect statistics. Add the one-qubit Pauli/tomography bridge required by E26 and E36.
5. Export finite Kraus channels, identity/composition/unitary channels, density preservation, dual
   effect action, and Schrödinger/Heisenberg Born duality. Prove fixed-channel data processing and
   parameter-independence preservation; do not add state-update/decoherence semantics.
6. Define extensional parameter-family predicates for local/joint statistical independence,
   detectability, exact recovery by a named decoder, descriptor nonconstancy, and explicit process
   provenance. State implications only where proved.
7. Formalize a two-bit classical one-time-pad density family: each one-bit marginal is independent,
   the joint parity effect detects/recovers the bit, and two distinct explicit construction
   histories yield the same final family. Use it to separate local/joint dependence, recovery, and
   provenance without consuming the paper's EPR example.
8. Add focused positive/negative/boundary tests, public documentation, source-ledger lifecycle
   updates, integrity/axiom targets, full build and hygiene evidence; fold conclusions into
   `0-plan.md` before completion.

## Paper Mapping

- E04/D05: give `(I+q_z)/2` exact effect and two-outcome Born semantics.
- E06/D06/U01/C12–C14: density expectations, the valid pure fixed-reference theorem, and the
  corrected mixed-state boundary.
- E26: generic qubit tomography bridge from Pauli moments to every local effect/POVM probability;
  the concrete EPR moments remain Stage 8.
- E36/C40: generic equivalence of one-qubit reduced-state equality, Pauli moments, and all local
  statistics; concrete teleportation values remain Stage 9.
- D02/D03/D08: separate semantic statistical dependence/detectability from descriptor syntax and
  from the source's asymmetric criteria.
- D11/C47/C52/C63: explicit provenance/history data and a same-final-state/two-history boundary.
- C02/C31: finite channel no-signalling/data processing and preservation of independence under a
  fixed parameter-independent channel.
- E39/U03: supply only reusable provenance/correlation vocabulary here; concrete calculations stay
  downstream.

## No-Cheating Checks

- Born positivity is proved for arbitrary positive semidefinite `ρ,E`; normalization alone and
  taking only the real part do not substitute for reality/nonnegativity.
- Local equivalence is extensional over all local effects (or proved equivalent data), not a finite
  sample of preferred measurements unless a tomography theorem closes the gap.
- Partial trace positivity and trace duality are proved, not encoded as structure fields.
- Channel trace preservation and positivity follow from the Kraus completeness equation; no
  arbitrary linear map is called a channel.
- A POVM is not called a measurement process or state update. Decoherence, discarded environments,
  repeated records, and wrong-basis behavior remain Stage 10.
- Weak detectability is not called perfect discrimination. Recovery names a decoder and exact
  success criterion. Provenance names history data and is not inferred from the final state.
- The mixed-state source sentence receives an executable obstruction; no rank-changing unitary is
  postulated.
- Completed modules contain no proof holes, unsafe declarations, project axioms, or public umbrella
  tactic import; principal results enter `DeutschTests/Audit.lean`.

## Completion Requirements

- [x] Density states, effects, finite POVMs, and Born probabilities have general compiled
      positivity, reality, upper-bound, and normalization theorems.
- [x] Selected-subsystem reduction preserves density states and is trace-dual to embedded local
      effects; reduced equality and all-local-statistics equality are connected in both directions.
- [x] The one-qubit Pauli/tomography bridge needed by E26/E36 compiles.
- [x] Finite channels preserve density states and have a dual effect action with Born-rule duality;
      fixed parameter-independent processing preserves statistical independence.
- [x] Local independence, joint dependence, weak distinguishability, recovery, descriptor
      dependence, and provenance have separate semantic APIs and boundary examples.
- [x] The mixed-state fixed-reference overreach is disproved and replaced by a precisely scoped
      valid statement.
- [x] Focused positive/negative tests, full build, source/doc/integrity/axiom audits, and hygiene
      checks pass and are recorded.
- [x] Findings are folded into `0-plan.md`; Stage 8 is the first incomplete stage.

## Stage Results

- `Deutsch.Information.State` exports density states, effects, finite POVMs, general Born weights
  and probabilities, pure-density bridges, unitary evolution, and purity. Positivity, reality,
  upper bounds, and POVM normalization are derived from the matrix hypotheses rather than stored
  as probability fields.
- `Deutsch.Information.Reduction` exports an explicit selected-subsystem partial trace with
  linearity, positivity, trace preservation, embedding duality, density reduction, and the exact
  equivalence between reduced-state equality and equality of every embedded local-effect
  probability. `Deutsch.Information.Qubit` adds one-qubit Pauli tomography.
- `Deutsch.Information.Channel` exports typed finite Kraus channels, identity, unitary, and
  composition channels, density and dual-effect actions, and Born duality.
  `Deutsch.Information.LocalChannel` proves that any selected-subsystem Kraus channel preserves
  the entire disjoint reduced density, including for entangled inputs.
- `Deutsch.Information.Dependence` keeps statistical equivalence, weak distinguishability,
  independence/detectability, recovery, descriptor nonconstancy, and explicit preparation/process
  provenance as separate APIs. Fixed-channel data processing is proved only for a fixed,
  parameter-independent channel.
- `maximallyMixedQubit_cannot_evolve_to_reference` gives an executable purity obstruction to the
  source's same-register fixed-pure-reference claim for arbitrary mixed states; density
  Schrödinger/Heisenberg expectation duality is the valid replacement.
- `Deutsch.Information.OneTimePad` supplies a classical diagonal two-qubit boundary example with
  independent singleton marginals, deterministic joint parity, an explicit Kraus decoder, and
  pointwise-distinct preparation histories with the same final density family.

## Evidence

- `lake env lean DeutschTests/Information.lean` and `lake env lean DeutschTests/Audit.lean` exit 0;
  the focused information suite contains 33 required positive, negative, and boundary oracles.
- The final `lake build` succeeds with 3282 jobs.
- `goal-1/check_lean_integrity.py` scans 38 Lean sources, requires all 33 information oracles and
  78 Stage 7 public declarations, compiles 210 representative axiom reports, and observes only
  `Classical.choice`, `Quot.sound`, and `propext`.
- `goal-1/check_source_audit.py` passes exact coverage for 46 numbered equations, all 49 displays,
  66 prose claims, definitions, figures, lifecycle classifications, and the Equation (45)
  correction oracle.
- `goal-1/check_doc_links.py` validates 68 repository-local links across 8 public Markdown files.
- `git diff --check` and the targeted completed-project trailing-whitespace scan report no findings.

## Resume Point

- Begin Stage 8 from Equations (22)–(28), (38)–(39), and (40)–(42) plus Fig. 2. Reuse the general
  partial-trace, all-effect tomography, channel no-signalling, dependence, recovery, and provenance
  APIs; do not replace the concrete EPR circuit calculations with those generic results.
