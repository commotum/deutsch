# 9-TELEPORTATION

## Status

- Complete with evidence (2026-07-16). Stage 10 is the first incomplete stage.

## Current Facts

- Fig. 3 has five upward-running wires. At `t=0`, `q1` is prepared while inverse Bell prepares
  `q4,q5`. Between `t=1` and `t=2`, `bellAt q1 q4` acts after `q4` is transported to A. Between
  `t=2` and `t=3`, CNOTs coherently copy the `q1` and `q4` paper bits into `q2` and `q3`; those
  record wires are transported to B before the three-qubit correction `T` acts on `q2,q3,q5`.
- The record CNOTs are coherent copies. Measurement, conditioning, dephasing, redundant classical
  records, and error robustness are Stage 10 obligations and are not assumptions of this stage.
- Existing gate APIs already provide arbitrary-register rotations, Bell/inverse-Bell operations,
  CNOT basis action, all Pauli conjugations, unitarity, support, and chronology. Existing
  information APIs provide pure/density states, reduction, all-effect tomography, channels,
  recovery, dependence predicates, and explicit provenance.
- Equation (29) repeats Equation (18)'s two wrong sine signs under the fixed definitions
  `rotationX theta = cos(theta/2) I - i sin(theta/2) X` and `U† A U`. This error propagates into
  the `theta`-dependent components of Equations (31), (32), and (34)–(37).
- Equation (30) agrees with the compiled inverse-Bell descriptor map. Its paper ket still differs
  from the conventional-Hadamard library ket by the already documented global phase `-i`.
- Equation (33)'s nine generator images are algebraically consistent. One explicit candidate is a
  controlled-`Z`, a controlled-`X`, and local phase representatives on the two record wires. Lean
  must prove unitarity, all nine images, and all four record branches rather than assuming the
  displayed transformation exists.
- The arbitrary-input prediction is now compiled: the final coherent ket is a fixed normalized
  four-wire junk ket tensor the exact input on `q5`, with exact receiver reduction as a separate
  theorem.
- The operational uniform-branch encoder/decoder is a separately constructed semantic model.
  Its branch corrections are derived from the explicit Equation (33) gate, but no theorem equates
  the whole encoder with dephasing/discard of the five-wire circuit. That bridge is Stage 10 work.

## Updated Corrections

- Corrected Equation (29):
  `q1 = (X, cos(theta) Y - sin(theta) Z, sin(theta) Y + cos(theta) Z)`.
- Corrected Equation (31)'s `q1` triple replaces its two rotated combinations by
  `cos(theta)Y1 - sin(theta)Z1` and `sin(theta)Y1 + cos(theta)Z1`; the displayed `q4` triple is
  retained.
- Corrected Equation (32)'s `q2` `y,z` components use
  `-(sin(theta)Y1 + cos(theta)Z1)`; the displayed `q3` triple is retained.
- Corrected Equation (34): the receiver triple uses
  `(cos(theta)Y1 - sin(theta)Z1)` and `(sin(theta)Y1 + cos(theta)Z1)` in its `y,z` components.
- Corrected Equation (35) uses the nontrivial rank-one effect
  `(I + sin(theta) q5y - cos(theta) q5z)/2`. The printed minus-sine effect has probability
  `cos²(theta)` under the corrected circuit and fails at `theta=pi/2`.
- Corrected Equation (36) has both Bloch vectors `(0, sin(theta), -cos(theta))`. Pauli tomography
  can turn this into one-qubit reduced-density/all-effect equality, but that one-parameter result
  is not the arbitrary-input teleportation theorem.
- Corrected Equation (37) reverses the displayed middle term. The printed operator is unequal to
  the circuit observable, although its fixed-reference probability can still be one because the
  erroneous `Y` term has zero reference expectation. Operator equality and one-state prediction
  remain separate.

## Big Picture Objective

- Verify the exact coherent teleportation circuit for arbitrary inputs, prove all correction
  branches and descriptor identities under the fixed convention, establish receiver correctness
  at ket/density/channel level with reference scope explicit, and keep local inaccessibility,
  recovery, record provenance, measurement, and decoherence distinct.

## Detailed Implementation Plan

1. Add `Deutsch.Teleportation.Correction` with an explicit Equation (33) unitary, unitarity, all
   nine Pauli images, and all four paper-record branches.
2. Add `Deutsch.Teleportation.Circuit` with named `Fin 5` wires, the input/resource, Bell, coherent
   record, correction, and verification boundaries, including unitarity and finite support.
3. Add a descriptor module compiling corrected Equations (29)–(32), (34), and (37), with
   special-angle non-equality regressions for every propagated source-sign family.
4. Define an initialized arbitrary input ket and the fixed four-wire junk ket. Prove exact final
   ket factorization, receiver reduction equality, and the corrected Equations (35)/(36) as
   consequences rather than substitutes for end-to-end correctness.
5. Derive the corrected protocol channel from the circuit/branch maps and prove it is the identity
   on every one-qubit operator/density. Extend by an arbitrary finite reference identity, or record
   the exact missing generic tensor theorem if that extension cannot be compiled.
6. Package pre-correction local independence, joint dependence, all-branch recovery, and supplied
   record transport/history through the Stage 7 semantic APIs. Add scoped omission failures for
   the two correction bits rather than an informal generic-necessity claim.
7. Recompute Equation (37) and the unnumbered final verification probability independently; retain
   the source probability only if proved from the corrected observable.
8. Add the public umbrella, focused tests, documentation, source-ledger lifecycle updates,
   integrity/axiom targets, full build, and hygiene evidence.

## Paper Mapping

- E29: corrected input descriptor signs with a `pi/2` disagreement regression.
- E30: exact resource-pair descriptors, reusing inverse Bell.
- E31–E32: corrected Bell/record descriptors; coherent copies only.
- E33/C38: explicit unitary, nine generator images, and four correction branches.
- E34: corrected receiver descriptor triple from the full circuit.
- E35/C39: corrected rank-one guaranteed effect plus exact factorization/reduction purity evidence.
- E36/C40–C41: corrected Bloch vectors and all-effect equality, strengthened by arbitrary-input
  circuit/channel correctness.
- E37/U02: corrected final observable and separately proved probability-one verification.
- F03/C35–C37: fixed five-wire chronology, arbitrary input scope, and branch completeness.
- C42/C44/C46: operational recovery and supplied transport history only; classical-channel and
  decoherence robustness remain Stage 10.

## No-Cheating Checks

- Do not encode the correction output or identity channel as an assumption. Derive branch maps
  from the explicit unitary and connect any channel theorem to those maps.
- Check all four record branches and at least two nontrivial superposition/phase inputs. A
  one-parameter `R_x(theta)|0>` calculation is not arbitrary-input correctness.
- Keep exact ket equality, equality up to phase, reduced-density equality, all-effect equality,
  channel equality, and reference-preserving equality distinct.
- Do not infer factorization or purity merely from expectation one of the identity. Use a
  nontrivial rank-one effect, reduced density, or exact ket factorization.
- Do not call coherent records classical, measured, decohered, or robust. Those words require the
  explicit Stage 10 channel/instrument hypotheses.
- Keep descriptor dependence, local statistical independence, joint detectability, recovery, and
  supplied provenance separate.
- Completed modules contain no proof holes, unsafe declarations, project axioms, or public
  umbrella tactic imports; principal theorems enter `DeutschTests.Audit`.

## Completion Requirements

- [x] The five-wire chronology, named boundaries, unitarity, support, and wire/order conventions
      compile.
- [x] Corrected Equations (29)–(32), (34), and (37) compile componentwise with explicit source
      disagreement regressions.
- [x] Equation (33) has an explicit unitary realization with all nine generator images and all
      four correction branches checked.
- [x] Exact arbitrary-input coherent teleportation correctness compiles at ket and receiver-density
      level; channel and reference-system scope is stated precisely.
- [x] Corrected Equations (35)/(36) and U02 follow from the full circuit, with local purity and
      all-effect prediction equality explicit.
- [x] Intermediate local independence, joint dependence, recovery, branch omission boundaries,
      and supplied transport history use the Stage 7 semantic APIs without semantic substitution.
- [x] Measurement/decoherence claims are deferred to explicit Stage 10 models.
- [x] Focused tests, full build, source/doc/integrity/axiom audits, and hygiene checks pass and are
      recorded; Stage 10 is then the first incomplete stage.

## Stage Results

- `Deutsch.Teleportation` exports the five-wire circuit, exact three-wire correction, corrected
  descriptors, arbitrary-input factorization/reduction, a separately scoped operational
  encoder/decoder, and source-family statistics. Every named boundary has compiled unitarity and
  finite-support evidence.
- Equation (33) has an explicit unitary, all nine Pauli-generator images, all four basis branches,
  and exact branch-to-semantic-correction links. Equations (29), (31), (32), (34), and (37) each
  have source-sign non-equality regressions.
- `coherentProtocol_factorizes` holds for every complex amplitude pair; normalized inputs have
  exact receiver-density equality. Equation (35) has a corrected rank-one effect, certainty,
  explicit receiver purity `1`, and a compiled `pi/2` counterexample to the printed sign.
  Equation (36) has exact Bloch-operator, moment, reduced-density, and all-effect forms.
- U02 is proved on both the evolved five-wire density and the literal `timeFiveUnitary` reference
  output. U03 is discharged by the EPR pair's joint-`ZZ` expectation one and zero marginals.
- The semantic three-wire family has maximally mixed singleton reductions, exact joint
  detectability, an identity decoder, branch-specific observable omission witnesses, and
  explicitly supplied Alice-to-Bob metadata. It is not claimed to be a dephased circuit output.
- Focused EPR and teleportation modules compile. The full `lake build` succeeds with 3296 jobs.
  `goal-1/check_lean_integrity.py` scans 52 Lean sources, requires 38 Stage 9 verification oracles
  and 82 Stage 9 public declarations, and accepts all 335 representative axiom reports using only
  `Classical.choice`, `Quot.sound`, and `propext`. Source coverage and the 10-file/93-link
  documentation audit pass.

## Resume Point

- Stage 9 is complete. Begin Stage 10 by auditing the source's exact measurement/decoherence
  claims, then add a basis-named dephasing or environment channel, its coherent-circuit bridge (or
  an exact obstruction), wrong-basis and bit-error regressions, and explicitly scoped robustness
  results.
