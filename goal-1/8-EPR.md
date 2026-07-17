# 8-EPR

## Status

- Complete with evidence on 2026-07-16.

## Current Facts

- Fig. 2 has four upward-running wires. With `q1 = 0`, `q2 = 1`, `q3 = 2`, and `q4 = 3`, its
  chronology is inverse Bell on `(q2,q3)`, separate `x` rotations on `q2,q3`, coherent recording
  CNOTs into `q1,q4`, transport of `q4`, and a final comparison CNOT with target `q1` and control
  `q4`.
- `Deutsch.Gates` already proves exact inverse-Bell amplitudes and descriptors, arbitrary-register
  rotations and CNOTs, unitarity, support, chronology, and all Pauli conjugations needed here.
- `Deutsch.Information` already proves density/effect Born semantics, partial-trace tomography,
  exact disjoint-channel no-signalling, dependence/detectability predicates, recovery, and explicit
  provenance. Stage 8 instantiates these results on the EPR circuit rather than re-encoding them.
- The conventional library Hadamard differs by global phase from the paper's diagonal `pi`
  rotation. Thus Equation (22)'s printed ket is `-i` times the exact library inverse-Bell output;
  the relative sign, density, descriptors, and predictions agree.
- Equations (25) and (27) inherit the sine-sign error already proved for Equation (18). The Stage 8
  descriptor results use the compiled `rotationX` signs and include special-angle
  non-equality regressions against the printed formulas.
- Equations (28) and (41) are mutually inconsistent with the correlated Bell pair in Equations
  (22) and (23). At equal settings the circuit has equal computational-basis outcomes with
  certainty, whereas Equation (28) prints probability one for different outcomes.

## Updated Assumptions and Corrections

- Paper logical bit `0` is raw basis index `1`; paper bit `1` is raw index `0`. The comparison CNOT
  followed by the target bit-one effect therefore selects unequal recorded bits.
- With `rotationX a = exp (-i a X / 2)` and `U† A U`, the correct component rules are
  `Y ↦ cos(a)Y - sin(a)Z` and `Z ↦ sin(a)Y + cos(a)Z`.
- The correct EPR probabilities are
  `P(different) = sin²((theta - phi)/2)` and
  `P(a = 1, b = 1) = (1/2) cos²((theta - phi)/2)`. The source's cosine/sine pair is the
  complementary convention obtained only after explicitly relabelling Bob's result.
- Equation (40)'s singleton marginals remain `1/2`. Equations (42) onward belong to Stage 11 and
  must be rebuilt from the corrected raw outcomes or an explicit Bob-outcome relabelling.
- Recording CNOTs are coherent copies, not measurements or decoherence. Outcome conditioning,
  repeated records, and basis-selective environmental channels remain Stage 10.
- “Information is in `Q2`” is split into descriptor nonconstancy, singleton statistical
  independence, joint detectability, and supplied preparation provenance. No one of these is
  silently substituted for the others.

## Big Picture Objective

- Reconstruct the finite EPR circuit in both pictures, prove its local and joint statistics, and
  separate circuit algebra, descriptor dependence, operational accessibility, and history while
  compiling exact corrections to the inconsistent source formulas.

## Detailed Implementation Plan

1. Add `Deutsch.EPR.Pair`, `Deutsch.EPR.Circuit`, `Deutsch.EPR.Statistics`, and
   `Deutsch.EPR.Provenance`, re-export them from `Deutsch.EPR`, and import the umbrella from the
   project root.
2. On the two-qubit pair, define inverse-Bell preparation, separate local rotations, the total
   circuit, normalized pure state/density, and an exact four-coordinate ket formula depending on
   `theta - phi`.
3. Prove the exact unphased inverse-Bell ket and the explicit `-i` relation to Equation (22), while
   keeping that ket-phase statement separate from downstream density and prediction calculations.
4. On `Fin 4`, define named qubits and the unitaries at times 1–4. Prove unitarity, support,
   cross-region commutation, and the untouched `q1,q4` Equation (24) instances.
5. Export the exact Equation (23) inverse-Bell descriptor triples. Derive corrected Equation (25)
   triples from the public rotation identities and corrected Equation (27) triples from the two
   recording CNOTs, without brute-force matrix expansion.
6. Prove both singleton reductions at time 2 are maximally mixed. Use the all-effect bridge to
   conclude every singleton-local effect probability is independent of both settings, not merely
   the three displayed expectations.
7. Define the unequal-record and joint-paper-one effects. Derive the corrected general
   probabilities, both `1/2` marginals, and explicit equal-angle/difference-`pi` boundary tests that
   refute the printed Equations (28) and (41).
8. Package local statistical independence and joint detectability for a finite parameter family,
   including a concrete `phi = 0` locally-inaccessible example under the Stage 7 semantic APIs.
9. Prove Equation (38) with its phase scope and Equation (39) as equal ket/density output from two
   distinct explicit rotation routes; preserve route history as supplied provenance rather than a
   final-state property.
10. Add focused tests, documentation, source-ledger lifecycle corrections, integrity/axiom targets,
    full build and hygiene evidence, then fold stable findings into `0-plan.md`.

## Paper Mapping

- E22: correct relative sign and explicit global-phase relation.
- E23–E24: exact named-register descriptors and finite support/locality instances.
- E25/E27: corrected sine signs, with executable disagreement tests at `pi/2`.
- E26/C28: maximally mixed singleton reductions and extensional all-effect independence.
- E28/C32: corrected unequal-record probability `sin²((theta-phi)/2)` and a compiled equal-angle
  counterexample to the printed `cos²` formula.
- E38: exact rotated ket with explicit phase convention.
- E39/C50–C52: same output from left/right rotations plus distinct supplied histories; no intrinsic
  final-state carrier claim.
- E40: exact `1/2` singleton pair probabilities; no four-wire record instrument is assumed.
- E41: corrected joint-one probability `(1/2) cos²((theta-phi)/2)`; E42–E46 remain Stage 11.
- F02/C26/C31/C33: finite circuit partition, fixed-channel locality, and explicit transport/history
  data only. Spatial continuum isolation and decoherence claims remain excluded/downstream.

## No-Cheating Checks

- Do not change the prepared Bell ray or silently relabel an outcome to recover the source's
  Equations (28)/(41). State any relabelling as a separate theorem.
- Cross-check every general probability with `theta = phi = 0` and angle difference `pi`.
- Prove local independence at the reduced-density/all-effect level; zero displayed Bloch moments
  alone are not the final theorem.
- Keep ket equality, equality up to global phase, density equality, descriptor equality, and
  equality of effect statistics distinct.
- Do not call coherent CNOT recording a measurement, conditioning, collapse, or decoherence.
- Do not infer route provenance from equal final kets/densities.
- Completed modules contain no proof holes, unsafe declarations, project axioms, or public umbrella
  tactic imports; principal theorems enter `DeutschTests.Audit`.

## Completion Requirements

- [x] The two-qubit state and four-qubit named circuit compile with exact unitarity, chronology,
      support, and basis/order conventions.
- [x] Equations (22)–(24) have exact phase-aware state and descriptor theorems.
- [x] Corrected Equations (25) and (27) compile componentwise, with explicit source-disagreement
      regressions.
- [x] Both singleton reductions are maximally mixed and every singleton effect statistic is setting
      independent.
- [x] Corrected Equations (28), (40), and (41) compile, including equal-angle and difference-`pi`
      boundary cases that expose the source contradiction.
- [x] Equations (38)–(39) compile with distinct-route provenance separated from final-state equality.
- [x] Local independence, joint detection, and finite circuit transport/history are stated through
      the Stage 7 semantic APIs, with interpretation/decoherence boundaries explicit.
- [x] Focused tests, full build, source/doc/integrity/axiom audits, and hygiene checks pass and are
      recorded; Stage 9 is then the first incomplete stage.

## Stage Results

- The source and API audits are complete. They establish the register order, circuit chronology,
  reusable proof routes, Equation (22)'s global phase, corrected sine signs for Equations (25)/(27),
  and the direct equal-angle contradiction correcting Equations (28)/(41).
- `Deutsch.EPR.Pair` compiles the two-qubit preparation/rotation circuits and unitarity, the exact
  Equation (22) relative sign and `-i` phase relation, a general four-coordinate ket expansion, and
  the state-specific Equation (39) equality between the left- and right-rotation routes.
- `Deutsch.EPR.Circuit` compiles all four named wires and time-one through time-four unitaries,
  finite support facts, Equations (23)/(24), all six corrected Equation (25) components, and all
  twelve corrected Equation (27) components with bundled descriptor triples.
- `Deutsch.EPR.Statistics` independently derives the general four-coordinate pure state, both
  maximally mixed singleton reductions, setting independence for every singleton effect, both
  `1/2` marginals, and the corrected unequal/joint-one probabilities. Equal-setting and
  difference-`pi` theorems make the source's complementary Equations (28)/(41) executable
  counterexamples rather than informal errata.
- `equation38Ket_eq_globalPhase_pairPureState` proves the displayed Equation (38) ket is exactly
  `-i` times the conventional-Hadamard circuit state. `Deutsch.EPR.Provenance` proves Equation
  (39) at ket and density level, then exhibits pointwise-distinct supplied route histories with
  the same final density without inferring history from the state.
- `Deutsch.EPR` re-exports the four production modules, and the project/test roots import the EPR
  umbrellas. `DeutschTests.EPR` supplies 24 named state, circuit, descriptor, statistics,
  correction, independence/detectability, and provenance oracles.
- `goal-1/check_lean_integrity.py` scans 44 Lean sources, requires 39 Stage 8 public declarations,
  and accepts all 249 representative axiom reports with only `Classical.choice`, `Quot.sound`,
  and `propext`. The focused EPR suite, exact source audit, 9-file/80-link documentation audit,
  and diff/trailing-whitespace checks pass; the full `lake build` succeeds with 3288 jobs.

## Resume Point

- Stage 8 is complete. Stage 9 (`9-TELEPORTATION`) is the first incomplete stage; begin by auditing
  Fig. 3 and Equations (29)–(37) against the compiled gate, density/channel, recovery, and
  provenance APIs before fixing the five-wire circuit boundary.
