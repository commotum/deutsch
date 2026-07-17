# 10-DECOHERENCE

## Status

- Complete with focused, full-build, source, documentation, integrity, axiom, and hygiene evidence.

## Current Facts

- The source uses “measurement,” “decoherence,” “classical channel,” “environment,” “stable
  observable,” and “invulnerable” in several different claims. All three source figures are
  coherent unitary circuits: none depicts a meter, an outcome register exposed to an observer, an
  environment wire, a discard, or a classical channel primitive. Those words therefore add
  physical claims not contained in the figures themselves.
- Stage 7 supplies finite Kraus channels, density/effect duality, channel composition,
  selected-subsystem channels, exact disjoint no-signalling, recovery, and statistical-independence
  preservation. Stage 10 now adds named nonselective coordinate dephasing; an outcome-conditioned
  instrument remains deliberately outside scope.
- Stage 8 proves coherent record copying and exact local/joint EPR statistics. Stage 9 proves exact
  coherent teleportation and also provides a separately constructed uniform-branch semantic
  encoder/decoder. Stage 10 proves that record dephasing fixes that semantic encoder and preserves
  recovery. No theorem identifies it with dephasing/discard of the coherent five-wire circuit.
- Nonselective computational dephasing is the channel that sums the basis branches and forgets the
  outcome. It is not an outcome-conditioned measurement instrument: D05 supplies effects and Born
  probabilities, but neither D05 nor a dephasing channel supplies a selected outcome and posterior
  state.
- A computational-basis dephasing channel should preserve diagonal classical records but destroy
  off-diagonal coherence. Consequently, “robust to decoherence” can only be true relative to a
  named basis, channel, and encoded family; it is false for arbitrary channels and false in the
  presence of uncorrected classical bit errors. The source's stronger C65 sentence that a pure
  one-qubit encoding is *maximally* vulnerable is not universally true even for this channel:
  computational-basis pure states are fixed by computational dephasing.
- C31 survives only for a fixed, parameter-independent channel. An environment version also needs
  a fixed environment state initially uncorrelated with the parameterized input and one fixed
  system/environment interaction followed by discard. Parameter-dependent noise, initially
  correlated environments, outcome conditioning, and postselection are outside that preservation
  theorem.

## Big Picture Objective

- Replace every Stage 10 use of measurement/decoherence language by an explicit finite channel or
  environment model, prove the exact stability and recovery statements that survive, and compile
  counterexamples to wrong-basis and bit-error overgeneralizations.

## Detailed Implementation Plan

1. Use the completed audit of C03, C22, C30, C31, C34, C36, C44–C46, C50, C65, C66, D05,
   F02, F03, and U03 as the source contract; keep every result below bounded by that contract.
2. Add the reusable `coordinateDephasing` Kraus channel for a named register coordinate, with exact
   matrix action, trace-preserving construction, idempotence, and fixed-diagonal/basis-state
   theorems.
3. Give a CNOT environment realization with a paper-zero environment state, an explicitly unitary
   system/environment copying interaction in the selected computational basis, and Kraus matrices
   obtained by summing over final environment basis labels. This is one dilation, not a theorem
   that every decoherence process is literally a measurement; no joint-density partial-trace
   identity is claimed.
4. Compile a wrong-basis coherence-loss witness and a classical bit-error witness. Do not call the
   channel generically harmless.
5. Define `protocolRecordDephasing` on the two record coordinates of the semantic teleportation
   register and prove the strongest exact bridge available: ideally that it fixes every
   `protocolEncoder` output and preserves `protocolDecoder` recovery. Keep this record-channel
   bridge distinct from the still-missing theorem identifying the semantic encoder with a
   dephased/reduced coherent five-wire circuit.
6. State the EPR repeated-record consequence only for a named computational dephasing/copy channel
   and exact statistic; do not infer interchangeable physical carriers or spacetime transport.
7. Add the public umbrella, focused tests, documentation, lifecycle updates, axiom targets, full
   build, and hygiene evidence.

## Paper Mapping

- C03: require an explicit encoder, fixed channel, shared resource/correlations, and decoder before
  saying that a qubit is transmitted through a classical/decoherent channel. Stage 9's semantic
  encoder/decoder establishes recovery in a separate model; Stage 10's named record-dephasing
  bridge fixes every encoded operator and preserves that decoder recovery.
- D05: retain the computation-basis effects and normalized Born probabilities, but do not infer an
  outcome-conditioned state update. A nonselective dephasing channel forgets its branch label and
  is weaker than a selective measurement instrument.
- C22 and C36: CNOT, including the record gates in F02/F03, is coherent copying. Calling it a
  “perfect measurement” additionally requires a blank record/environment state plus a specified
  dephasing/discard or selective instrument.
- C30: replace generic “spreading” by explicit coupling/channel examples; fixed channels preserve
  an already operationally independent family rather than creating parameter dependence from
  nowhere. Descriptor occurrence and supplied history remain different predicates.
- C31: retain fixed-channel statistical-independence preservation and disjoint no-signalling;
  instantiate named local/environment channels only under fixed parameter-independent dynamics, a
  fixed initially uncorrelated environment state, and no conditioning or postselection.
- C34 and F02: formalize repeated nonselective computational dephasing/idempotence and preservation
  of one named corrected comparison statistic only. Do not identify that with repeated selective
  measurements or infer that arbitrary copied records are physically interchangeable carriers.
- F02 and F03: their implemented gate chronologies remain entirely coherent. The intended Stage 10
  channels are additions to those models, not facts read off the circuit drawings.
- C44: connect record-basis dephasing to the separately scoped teleportation branch model, without
  claiming the still-unproved dephased-coherent-circuit/semantic-encoder identification or a
  generic channel-capacity theorem.
- C45: correct “invulnerable” to exact record-basis dephasing stability with error-free records;
  compile wrong-basis and bit-error failures.
- C46 and U03: keep “entanglement as key” as analogy. U03's non-product `ZZ` moment is a correlation
  witness, not by itself an entanglement witness; a separable classically correlated state can have
  the same named moments. Prove only the explicit resource correlation and decoder/recovery facts
  actually represented by the model.
- C50: preserve the established split between descriptor occurrence, local all-effect
  independence, joint detectability, recovery, and provenance. Calling `Q₃` a “key” does not identify
  a physical key subsystem or prove entanglement is necessary.
- C65: reject the universal accessibility/robustness tradeoff and “maximally vulnerable pure
  qubit” wording. State only channel- and encoding-specific positive results plus computational
  basis-state, wrong-basis, and bit-error boundary cases.
- C66: realize `coordinateDephasing` through one named paper-zero-environment CNOT coupling and
  discard calculation. This supplies an explicit environment model without equating every
  decoherence process, nonselective channel, and selective measurement.

## No-Cheating Checks

- Every dephasing theorem names its channel and selected basis. Every environment theorem names
  the environment state, interaction, and discarded subsystem.
- Do not use a diagonal state definition as evidence that a coherent circuit has physically
  decohered. Supply a channel application or label it a separate semantic model.
- Do not call a coherent CNOT a measurement unless a nonselective or selective measurement model
  is separately defined.
- Do not call nonselective dephasing an observed measurement: it exposes no outcome. Conversely,
  do not infer a dephasing channel merely from the availability of D05's POVM effects.
- Idempotence is stability under repetition, not robustness to arbitrary noise. A bit-flip channel
  is a mandatory negative test.
- A computational-basis channel preserving classical records must still fail on a suitable
  complementary-basis coherent state.
- Keep recovery, local statistical independence, provenance, redundant records, and environment
  correlations as separate predicates.
- A non-product correlation such as U03 is not automatically an entanglement witness, and neither
  correlation nor successful recovery alone identifies a subsystem as a physical “key.”
- Completed modules contain no proof holes, unsafe declarations, project axioms, or hidden
  classicality assumptions; principal theorems enter `DeutschTests.Audit`.

## Completion Requirements

- [x] A named computational-basis dephasing Kraus channel compiles with exact matrix action,
      idempotence, and fixed diagonal/basis-state results.
- [x] At least one explicit environment-state/coupling/discard calculation realizes a dephasing
      consequence or the exact obstruction is documented with a useful substitute.
- [x] Wrong-basis disturbance and classical bit-error failures compile.
- [x] A channel-level theorem connects record-basis dephasing to teleportation or EPR recovery,
      with the coherent-circuit versus separate-model scope explicit.
- [x] Source items C03, C22, C30, C31, C34, C36, C44–C46, C50, C65, C66, D05, F02, F03, and
      U03 have final bounded statuses.
- [x] Documentation never uses generic “decoherence occurs” or “invulnerable” without hypotheses.
- [x] Focused tests, full build, source/doc/integrity/axiom audits, and hygiene checks pass and are
      recorded; Stage 11 is then the first incomplete stage.

## Stage Results

- `Deutsch.Information.Dephasing` exports arbitrary-register coordinate dephasing with exact entry
  action, trace preservation, a fixed-point iff, basis-density stability, operator/density
  idempotence, fixed Z statistics under every finite repetition, and an X-effect disturbance
  witness. The reversed paper/raw-bit convention is explicit throughout.
- `cnotEnvironmentState` is the named paper-zero environment and
  `cnotEnvironmentCoupling` is unitary. Summing its CNOT matrix elements over the final environment
  basis produces Kraus operators exactly equal to the coordinate projectors, hence the same map on
  every one-qubit density. This is the compiled discard representation; a separate theorem about
  partial trace of a constructed joint density is not claimed.
- `protocolRecordDephasing` dephases only the two semantic record coordinates. Its exact block
  formula proves that it fixes every `protocolEncoder.mapOperator A`, so
  `protocolDecoder_after_recordDephasing` recovers every density. The genuine unitary/Kraus
  `protocolRecordKBitFlip` instead maps the encoded basis family to the opposite input and makes
  the unchanged decoder return the wrong bit.
- `epr_c34_q4_dephasing_before_comparison_iterate` proves the bounded source-C34 result: for every
  pre-comparison four-wire density and every finite repetition count, dephasing transported record
  `q4` preserves the final `q1` paper-one probability. It does not assert global-state equality or
  identify this statistic with all of the source's information language.
- `classicallyCorrelatedDensity` is definitionally an equal convex mixture of two product basis
  densities. It has the same two zero single-Z moments, unit joint-ZZ moment, and nonfactorizing
  U03 correlation as `pairDensity 0 0`, while an off-diagonal entry proves the densities unequal.
  This constructively refutes treating those moments as an entanglement witness without adding an
  unavailable abstract separability predicate.
- `lake build Deutsch.Decoherence DeutschTests.Decoherence` built 2727 jobs. The clean full
  `lake build` built 3302 jobs. `python3 -B goal-1/check_lean_integrity.py` scanned 58 Lean sources,
  required 18 Stage 10 oracles and 33 Stage 10 public declarations, and accepted 368 representative
  axiom reports containing only `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_source_audit.py` passed all 46 numbered equations, three unnumbered
  displays, three figures, 11 definitions, 66 claims, and ten interpretation groups.
  `python3 -B goal-1/check_doc_links.py` passed 11 Markdown files and 97 repository-local links.
  The forbidden-token scan, trailing-whitespace scan, `git diff --check`, and adversarial
  statement/scope review all passed.

## Resume Point

- Stage 11 (`11-BELL-AUDIT`) is the first incomplete stage. Build the corrected finite
  three-setting Bell/pigeonhole theorem on one explicit common assignment space, importing the
  corrected Stage 8 probabilities rather than the false printed Equations (41) and (45).
