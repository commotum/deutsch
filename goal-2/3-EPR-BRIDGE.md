# 3-EPR-BRIDGE

## Status

- Complete.

## Current Facts

- The finalized source requires Equation (28)'s different-outcome probability, Equation (40)'s two
  marginal paper-one probabilities, and Equation (41)'s joint paper-one probability to arise from
  Figure 2's literal four-wire circuit.
- `Deutsch.EPR.Circuit` already defines the complete four-wire chronology through
  `timeThreeUnitary` and `timeFourUnitary`, proves every layer unitary, and derives the time-three
  record descriptors.
- `Deutsch.EPR.Statistics` independently proves the corresponding formulas for the two-qubit pair
  density, but the production tree has no compiled state/effect bridge from that shortcut to the
  four-wire records.
- `Deutsch.Decoherence.EPR` already pulls the final comparison effect backward to a two-record
  parity operator, but it is downstream of EPR and cannot serve as the foundational bridge without
  reversing the intended import direction.
- A scratch compilation established two reusable low-level routes:
  - an effect can be placed along any finite injection by reindexing and subsystem embedding while
    preserving positivity and complement positivity;
  - fixed-reference expectations of an operator placed along an injection equal the corresponding
    smaller-register fixed-reference expectation.
- The exact time-two four-wire unitary can be proved equal to the two-qubit `pairCircuit` placed on
  `q2,q3`; this proof compiled in scratch without assuming a source formula.

## Updated Assumptions

- A neutral `Deutsch.EPR.RecordStatistics` module can own the literal record densities, effects, circuit
  bridges, and source-facing Equation (28)/(40)/(41) theorems.
- Generic ordered effect placement and reference-expectation placement lemmas belong in
  `Deutsch.Information.Reduction`, where both EPR and future modules can reuse them.
- The most auditable proof should first establish equality between four-wire and pair probabilities,
  then obtain the trigonometric formulas from the independently proved pair calculation.
- Coherent record CNOTs are modeled as unitary evolution only. No collapse, outcome selection, or
  instrument semantics is required.

## Big Picture Objective

- Derive corrected Equations (28), (40), and (41) from Figure 2's actual four-wire chronology and
  prove those statistics equal the independent two-qubit pair-state statistics.

## Detailed Implementation Plan

- Add general `Effect.embedAlong` and fixed-reference expectation placement lemmas to the
  information/reduction layer, with positivity and exact-operator tests.
- Add `Deutsch/EPR/RecordStatistics.lean` containing:
  - ordered placements for the EPR pair (`q2,q3`) and records (`q1,q4`);
  - exact time-two placed-pair circuit equality;
  - time-three and time-four four-wire densities;
  - left/right record paper-one effects, a joint record effect, and the final comparison effect;
  - operator and probability bridges from record statistics to pair statistics;
  - direct source-facing theorems for Equations (28), (40), and (41);
  - equal-setting and relative-`pi` boundary theorems.
- Re-export Records from `Deutsch.EPR`, add focused tests, and add every principal declaration to
  the representative axiom audit and integrity registry.
- If an intermediate proof needs the explicit time-three ket, keep it as a circuit lemma and do not
  substitute the pair formula as a definition of the four-wire state.

## No-Cheating Checks

- Define the four-wire densities by evolving `referenceDensity EPRQubit` through
  `timeThreeUnitary`/`timeFourUnitary`; do not define them by lifting `pairDensity`.
- Define the final Equation (28) statistic on `timeFourDensity` and `q1` after the comparison CNOT.
- Prove four-wire/pair equality as a theorem before rewriting with the pair trigonometric formulas.
- Keep the time-three joint record effect distinct from the final time-four comparison effect and
  prove their probabilities agree.
- Make the raw-zero/paper-one convention visible in effect declarations and boundary tests.
- Do not import `Deutsch.Decoherence` into `Deutsch.EPR`.
- Do not use source equations, desired probabilities, or trigonometric conclusions as premises.

## Completion Requirements

- Canonical production theorems for Equations (28), (40), and (41) mention
  `timeFourDensity`/`timeThreeDensity` and the named record effects directly.
- Pair-state and four-wire results are linked by compiled probability equalities.
- Equal-setting and relative-`pi` four-wire boundary tests compile.
- The EPR import graph remains upstream of decoherence, and no measurement instrument is assumed.
- Focused EPR tests, the full public/test build, integrity scan, representative axiom audit,
  documentation links, whitespace scan, and `git diff --check` pass.

## Stage Results

- Added reusable low-level lemmas:
  - `Register.basisKet_expectation`;
  - `Information.pureDensity_basisState`, `basisDensity_expectation`,
    `referenceDensity_expectation`, and `pureDensity_evolve`;
  - `Information.Effect.embedAlong` with exact operator semantics; and
  - `Information.referenceDensity_expectation_embedAlong`.
- Added `Deutsch/EPR/RecordStatistics.lean` and re-exported it from `Deutsch.EPR`. Its principal
  compiled results include:
  - the exact identity
    `timeTwoUnitary theta phi = embedAlong pairPlacement (pairCircuit theta phi)`;
  - explicit lifted and recorded four-wire kets derived by applying the named circuit gates;
  - time-three and time-four pure densities, each proved equal to evolution of
    `referenceDensity EPRQubit` through the corresponding named unitary;
  - record effects placed along the ordered injection `q1,q4`, together with the left/right
    marginal and final comparison effects expressed by the canonical paper-one projector;
  - an arbitrary-outcome probability bridge from the time-three record state to the two-wire pair
    density;
  - direct time-three marginal and joint probabilities for Equations (40) and (41);
  - a direct time-four comparison probability for Equation (28); and
  - equal-setting and arbitrary relative-`pi` boundary theorems.
- The bridge intentionally proves equality of the relevant computational-record probabilities.
  It does not assert equality between the reduced record density and `pairDensity`: tracing out the
  source wires removes the pair state's record-basis coherences.
- A second compiled Heisenberg-route experiment recovered the same placed-pair circuit and a
  generic fixed-reference product factorization. Completing the three record statistics by that
  route required substantially more projector normal-form bookkeeping without strengthening the
  result, so the exact ket route was retained.
- `DeutschTests/EPR.lean` now checks the literal four-wire statements of Equations (28), (40), and
  (41), all pair/four-wire probability bridges, raw-zero/paper-one effect semantics, equal settings,
  and arbitrary settings separated by `pi`.
- Verification:
  - `lake env lean Deutsch/EPR/RecordStatistics.lean`: pass.
  - `lake build Deutsch.EPR`: 2722 jobs, pass.
  - `lake build DeutschTests.EPR`: 2723 jobs, pass.
  - `lake build DeutschTests.Audit DeutschTests.EPR`: 3299 jobs, pass.
  - `lake build Deutsch DeutschTests`: 3310 jobs, pass.
  - `python3 goal-1/check_lean_integrity.py`: 67 Lean sources and 429 representative axiom
    reports, pass; observed foundations only `Classical.choice`, `Quot.sound`, and `propext`.
  - `python3 goal-1/check_source_audit.py`: 46 tagged equations, 47 displays, source/provenance
    guards pass.
  - `python3 goal-1/check_doc_links.py`: 14 public Markdown files and 119 local links, pass.
  - `git diff --check` and the focused forbidden-token scan: pass.
- No EPR module imports `Deutsch.Decoherence`, and no measurement, collapse, source formula, or
  trigonometric conclusion is assumed in the circuit bridge.
