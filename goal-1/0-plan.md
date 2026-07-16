# Goal 1: Formalize Information Flow in Entangled Quantum Systems

Shorthand: `LEAN-INFOFLOW`

## Big-Picture Objective

Build a reusable, pinned Lean 4/mathlib library that independently reconstructs the mathematically precise content of David Deutsch and Patrick Hayden's *Information Flow in Entangled Quantum Systems*. The library must formalize finite quantum systems in the Heisenberg picture, subsystem observables and locality, representative gate and circuit calculations, EPR and teleportation, and operationally meaningful notions of information dependence. It must distinguish verified mathematics from interpretation, correct the source where necessary, and finish with documentation, executable examples, a clean build, and an axiom audit.

The paper is evidence and a source of conjectures, not a formal specification. The project succeeds only by proving explicit corrected statements under explicit assumptions or by documenting exact obstructions and nearby useful results.

## Non-Negotiable Constraints and No-Cheating Rules

- Keep Lean and mathlib versions pinned and keep the project compiling incrementally.
- Use mathlib definitions where they fit, but verify their multiplication, tensor, adjoint, basis-order, and finite-dimensional conventions before relying on them.
- Do not use `sorry`, `admit`, `by_contra!`-style concealment of missing mathematics, unsafe declarations, or unexplained project-specific axioms in completed modules.
- Do not weaken theorem statements merely to make proofs easy. Any correction, extra hypothesis, or reduced scope must be documented against the corresponding paper claim.
- Verify displayed identities algebraically; do not encode the paper's formulas as assumptions.
- Keep operator equality distinct from equality of expectations or measurement distributions.
- Keep Schrödinger states, Heisenberg observables, descriptor triples, and subsystem embeddings distinct in types and documentation.
- Define tensor order, qubit order, control/target order, multiplication direction, circuit chronology, adjoint convention, and rotation sign convention once and test them.
- State whether results apply to pure states, density operators, or both.
- Treat decoherence only under explicit channel/environment assumptions.
- Do not promote philosophical claims about ontology, locality, many worlds, or Bell's theorem into Lean theorems without explicit mathematical definitions and assumptions.
- Do not identify “information is in subsystem A” with mere syntactic parameter occurrence. Distinguish descriptor dependence, local statistical dependence, joint statistical dependence, operational distinguishability, recoverability, and any historical provenance notion actually used.
- If a claim is false or cannot be established, record the exact obstruction, prove the strongest nearby useful statement, and never fabricate a proof.
- Preserve unrelated user changes. In particular, inspect repository state before every stage and do not assume currently untracked source material is disposable.

## Current Facts

- The working directory is `/Users/jake/Developer/deutsch`.
- The paper is available as `deutsch-2000/deutsch-2000.md`, with three referenced circuit images in `deutsch-2000/images/`.
- The source has sections on Heisenberg computation, gates, EPR, teleportation, locally inaccessible information, Bell's theorem, and the Schrödinger picture.
- The repository currently exposes a Python scaffold (`pyproject.toml`, `main.py`, `uv.lock`) and an empty `README.md`.
- No `lean-toolchain`, `lakefile.lean`, `lakefile.toml`, `lake-manifest.json`, or PDF was detected at scaffold time.
- `deutsch-2000/` is currently untracked according to `git status --short`; it must be preserved.
- No Lean representation or theorem has yet been selected or verified.

## Initial Assumptions to Test

- A concrete finite-dimensional matrix model over `ℂ` may be the lowest-risk first representation for explicit qubit calculations, while a finite-dimensional Hilbert-space abstraction may better support reusable locality and measurement theorems. Stage 2 must compare them rather than commit prematurely.
- Tensor-factor embeddings should make the main disjoint-support commutation and Heisenberg locality theorem direct. The exact mathlib API and factor-order convention remain to be established.
- Descriptor completeness may be best stated as generation/reconstruction of the global operator algebra, not as an ontological claim about subsystem states.
- Local statistical independence and joint recoverability can likely be expressed using equality/inequality of restricted Born distributions or reduced states/channels over an explicit parameter family.
- Most gate identities can be proved first for concrete matrices, then lifted through subsystem embeddings and conjugation.
- The paper may contain convention-sensitive or incorrect signs in controlled-NOT and later descriptor formulas; every identity needs independent checking.
- The Bell section may yield a finite contradiction theorem about explicitly stated single-valued stochastic assignments, while the paper's interpretation of that contradiction will remain documentation.

## Project-Wide Success Metrics and Verification

- A pinned Lean 4/mathlib project builds from a clean checkout using documented commands.
- Public modules expose reusable definitions and theorems for finite registers, local embeddings/support, Heisenberg conjugation, descriptors, gates, states/measurements, and information dependence.
- The central locality result proves that conjugation by an operation supported on one subsystem fixes observables supported on a disjoint subsystem, with all required finiteness/unitarity/disjointness assumptions explicit.
- Pauli relations are established initially and shown preserved under unitary conjugation.
- Pauli/NOT, rotations, Hadamard, CNOT, Bell, EPR, and teleportation identities are verified under documented ordering conventions.
- EPR and teleportation results separately cover circuit correctness, descriptor evolution, local statistical independence, and recovery of correlations or the teleported state after the required later interaction/classical control.
- Information notions are semantic and operational, not syntax inspection, and theorems state which notion they use.
- Every significant paper equation or claim is mapped to a Lean declaration or classified as corrected, partial, interpretative/excluded, or unresolved.
- Representative examples execute or reduce in Lean and pin the library's conventions.
- Repository-wide searches find no `sorry`, `admit`, unsafe escape hatch, or unexplained project axiom in completed project modules.
- The main exported theorems receive a recorded `#print axioms` audit; only understood foundational/mathlib axioms are accepted and documented.
- Focused tests, the full build, formatting/whitespace checks, documentation link checks, and the equation/claim coverage audit all pass.

## Stage Index

1. `1-SOURCE-AUDIT`
2. `2-FOUNDATIONS`
3. `3-REGISTERS`
4. `4-LOCALITY`
5. `5-DESCRIPTORS`
6. `6-GATES`
7. `7-INFORMATION`
8. `8-EPR`
9. `9-TELEPORTATION`
10. `10-DECOHERENCE`
11. `11-BELL-AUDIT`
12. `12-LIBRARY-AUDIT`

## 1-SOURCE-AUDIT

### Big Picture Objective

Turn the paper into a traceable set of mathematical obligations without treating its prose or displayed equations as trusted facts.

### Detailed Implementation Plan

- Inventory all numbered equations, circuit figures, definitions, and substantive claims in `deutsch-2000/deutsch-2000.md`.
- Classify each item as algebraic identity, circuit claim, locality claim, statistical claim, completeness claim, decoherence-dependent claim, Bell-assumption claim, or interpretation.
- Record hidden assumptions and convention dependencies, especially qubit order, CNOT control/target, operator-product order, pure/mixed state scope, and observable versus prediction equality.
- Create the declaration-mapping document that later stages will update with statuses: planned, proved, corrected, partial, excluded, or unresolved.
- Identify the smallest representative examples needed to prevent convention drift.

### Completion Requirements

- Every numbered paper equation and each major prose claim has a unique audit entry and provisional disposition.
- Each mathematical entry names the Lean module/stage expected to handle it and lists unresolved assumptions.
- Interpretative claims are explicitly separated from formal proof obligations.
- The three figures are cross-referenced to the relevant circuit obligations.
- The audit contains no claim that an equation is correct merely because it appears in the paper.

## 2-FOUNDATIONS

### Big Picture Objective

Establish the pinned Lean project, test mathlib's relevant APIs and conventions, and choose representations that support both reusable theorems and concrete calculations.

### Detailed Implementation Plan

- Create and pin the Lean 4/mathlib project without disturbing the existing source files.
- Probe mathlib support for complex matrices, finite-dimensional inner-product spaces, linear maps, continuous linear maps if needed, tensor products/Kronecker products, adjoints, unitaries, density operators, traces, and finite probability distributions.
- Compare at least a concrete `Matrix` model and an abstract finite Hilbert-space/operator model against the required locality, embedding, and computation proofs.
- Write a conventions document and executable smoke tests for basis order, tensor order, multiplication direction, adjoint, Pauli matrices, and a two-qubit basis.
- Establish module boundaries, namespace policy, public API rules, build/test commands, and automated checks for forbidden proof holes and axioms.

### Completion Requirements

- Pinned toolchain and dependency files exist, and a minimal project builds with the documented command.
- Representation decisions are justified by compiled probes, with rejected alternatives and migration risks recorded.
- All global algebraic and circuit conventions are documented and covered by executable Lean examples.
- The source audit points to intended module/declaration locations.
- A baseline forbidden-token scan and axiom-audit mechanism are present and run successfully.

## 3-REGISTERS

### Big Picture Objective

Formalize finite quantum registers, subsystem observables, states, and Heisenberg evolution in a reusable way.

### Detailed Implementation Plan

- Define finite qubit and, where useful, finite-qudit register spaces with explicit basis indexing.
- Define global operators, adjoint, Hermitian and unitary predicates/types, expectation, and Heisenberg conjugation with a documented convention.
- Define embedding of operators on selected tensor factors, including single-qubit Pauli embeddings and identities on complementary factors.
- Give a semantic notion of operator support or locality sufficient for arbitrary selected subsystems, not only adjacent qubits.
- Prove the core algebraic properties of embeddings and conjugation needed downstream.
- Add small executable examples for one-, two-, and three-qubit registers.

### Completion Requirements

- Public definitions compile and do not rely on project axioms.
- Identity, composition, adjoint, Hermiticity, and unitarity laws required later are proved for the chosen embeddings/conjugation.
- Selected-factor behavior and qubit-order convention are verified on explicit basis vectors or matrices.
- Examples catch swapped tensor factors and reversed conjugation order.
- Focused register tests and the full build pass.

## 4-LOCALITY

### Big Picture Objective

Prove the paper's locality core as precise support, commutation, and conjugation theorems.

### Detailed Implementation Plan

- Prove that observables and operations embedded on disjoint subsystems commute.
- Prove that conjugation by an operator supported on subsystem `A` fixes an observable supported on disjoint subsystem `B`; state a unitary specialization as the Heisenberg locality theorem.
- Generalize from individual qubits to arbitrary disjoint finite subsystem sets where the representation permits it.
- Prove compatible expectation/statistics corollaries for arbitrary states, clearly separating operator equality from prediction equality.
- State the exact scope: a supported gate/dynamics theorem, not an automatic theorem about approximate simulation of arbitrary spatial dynamics.

### Completion Requirements

- The central disjoint-support commutation and locality theorems compile without proof holes or project axioms.
- The assumptions on support, disjointness, and unitarity are explicit and no stronger than needed for each result.
- At least one entangled-state example demonstrates that the operator result does not require a product state.
- Counterexamples or tests show why disjointness/support hypotheses cannot simply be omitted.
- The paper audit marks the discrete-gate locality claim precisely and records the separate unresolved burden for any continuum/general-dynamics extrapolation.

## 5-DESCRIPTORS

### Big Picture Objective

Represent qubits by global Heisenberg Pauli descriptors and prove their algebraic invariants and a precise completeness result.

### Detailed Implementation Plan

- Define Pauli matrices and a descriptor triple associated with a register factor.
- Formalize the same-factor Pauli multiplication/anticommutation relations and cross-factor commutation relations.
- Prove unitary conjugation preserves Hermiticity, squares, products, commutators, and the Pauli relations.
- Relate descriptor evolution to global circuit conjugation.
- Replace vague “complete description” language with an explicit algebra-generation, basis-expansion, or reconstruction theorem strong enough to recover global observables/predictions from the complete descriptor family.
- Document gauge/equivalence issues if different descriptor families yield the same predictions in a fixed reference state.

### Completion Requirements

- Initial embedded descriptors satisfy the full documented Pauli and cross-factor relations.
- Preservation under arbitrary unitary conjugation is proved.
- A compiled, mathematically explicit completeness/reconstruction statement is exported, or the exact obstruction is recorded with the strongest proved substitute.
- Equality of descriptor operators and equality of predictions remain separate APIs/theorems.
- Paper equations (1)–(8) and their surrounding completeness claims have audited dispositions.

## 6-GATES

### Big Picture Objective

Independently verify the elementary gate and Bell-transform identities under one fixed, tested convention.

### Detailed Implementation Plan

- Define Pauli/NOT gates, square-root-of-NOT if retained, axis rotations, Hadamard, CNOT with named control and target, and the Bell transform.
- Prove unitarity and compute Heisenberg conjugation on Pauli descriptors algebraically.
- Derive rotation formulas from exponentials or a rigorously equivalent closed form, including signs and angle conventions.
- Lift concrete identities into arbitrary registers using embeddings and the locality API.
- Compare every result with paper equations (9)–(20), documenting sign, tensor-order, or control/target corrections.
- Add basis-action and matrix-equality examples that independently cross-check descriptor formulas.

### Completion Requirements

- Each public gate is proved unitary and has verified basis action where applicable.
- Heisenberg transformations for Pauli/NOT, rotations, Hadamard, CNOT, and Bell compile as operator equalities.
- At least two independent checks pin CNOT control/target and circuit composition order.
- Any discrepancy with the paper is reproduced, explained, and replaced by the strongest correct statement.
- Focused gate tests, full build, and forbidden-token scan pass.

## 7-INFORMATION

### Big Picture Objective

Define precise state, measurement, channel, and parameter-dependence notions adequate for the paper's operational claims.

### Detailed Implementation Plan

- Formalize pure states and/or density operators with Born expectations/probabilities, expanding to mixed states wherever the theorem naturally permits.
- Define local observables/measurements and restriction to a subsystem in the chosen representation.
- For parameterized state or descriptor families, separately define descriptor dependence, local-statistics equivalence/independence, joint-statistics equivalence/independence, operational distinguishability, and recovery by a specified later channel/interaction.
- Prefer extensional equality of distributions, expectations for all allowed effects, reduced states, or existence of a distinguishing measurement over syntactic expression inspection.
- Relate equivalent notions under finite-dimensional hypotheses where useful.
- If historical provenance is needed, represent it as explicit circuit/channel factorization data rather than an intrinsic property of the final state.

### Completion Requirements

- Every “information” predicate has a semantic definition, documented quantifiers, and stated subsystem/measurement class.
- Local and joint statistical dependence are demonstrably distinct via compiled examples.
- At least one theorem connects local reduced-state equality, equality of all local measurement statistics, and failure of local distinguishability under explicit assumptions.
- Pure-state-only restrictions are documented; results valid for density operators are proved at that level.
- No theorem infers information location solely from syntactic parameter occurrence.

## 8-EPR

### Big Picture Objective

Reconstruct the EPR example and separate circuit algebra, descriptor evolution, local statistics, joint correlations, and interpretation.

### Detailed Implementation Plan

- Encode the paper's EPR preparation and measurement-basis choices under the fixed gate/order convention.
- Verify the global state/circuit result and derive the relevant Heisenberg descriptor evolution.
- Prove local measurement statistics are independent of the remote setting/outcome under the appropriate no-signalling hypotheses.
- Prove the stated parameter-dependent joint correlations and operational distinguishability available to joint data.
- Identify which claims concern a specific circuit and which follow from general channel locality/no-signalling.
- Update the paper map with corrected equations and exclude unformalized ontological conclusions.

### Completion Requirements

- The EPR circuit's state and descriptor calculations compile and agree through independent Schrödinger/Heisenberg cross-checks.
- Local marginal independence is proved for the exact allowed parameter family and measurement class.
- Joint correlation dependence is proved with an explicit statistic or measurement.
- The result is tested on an entangled state and does not silently assume separability.
- Interpretative statements about where information “really” travelled are labeled as interpretations unless captured by a defined operational predicate.

## 9-TELEPORTATION

### Big Picture Objective

Verify teleportation while keeping correctness, observable evolution, local inaccessibility, classical outcomes, and later recovery mathematically distinct.

### Detailed Implementation Plan

- Encode the Bell-pair preparation, Bell measurement/unitary equivalent, outcome registers, controlled corrections, and any deferred-measurement/coherent version needed for clean unitary reasoning.
- Prove teleportation correctness for an arbitrary input pure state and extend to density operators or entangled reference systems if the chosen abstraction supports it.
- Compute the relevant Heisenberg descriptors through the circuit and compare with the paper's formulas.
- Prove that designated intermediate local/classical registers have parameter-independent local statistics while suitable joint correlations retain dependence.
- Prove recovery after later access to the classical outcomes/correction interaction using the operational recovery definition.
- State decoherence assumptions separately rather than building them silently into “classical channel.”

### Completion Requirements

- End-to-end teleportation correctness is a compiled theorem with input and reference-system scope stated.
- Descriptor calculations are verified under the same convention as the gate library.
- Intermediate local independence and joint dependence/recoverability are separate theorems.
- All correction branches or their coherent controlled equivalent are checked.
- Paper teleportation equations/claims have proved, corrected, partial, interpretative, or unresolved statuses.

## 10-DECOHERENCE

### Big Picture Objective

Make only the decoherence and “classical channel” statements justified by explicit mathematical models.

### Detailed Implementation Plan

- Identify exactly where the paper relies on decoherence, copying, measurement, discarded environments, or effectively classical records.
- Model the minimal relevant channel/environment interaction, with basis and trace/discard assumptions explicit.
- Prove the resulting diagonalization, local indistinguishability, record stability, or recovery statements actually needed by the EPR/teleportation discussion.
- Separate exact finite-dimensional channel results from approximate physical claims and from broad interpretative prose.

### Completion Requirements

- Every formal decoherence theorem names its channel, environment state, basis, and exact/approximate status.
- No generic claim that “decoherence occurs” appears without hypotheses.
- At least one channel-level calculation connects the model to the teleportation/classical-record results, or an exact obstruction and useful substitute are documented.
- Pure and mixed state scope is explicit.
- Full build and axiom audit for the new results pass.

## 11-BELL-AUDIT

### Big Picture Objective

Formalize the mathematical contradiction in the paper's Bell discussion only under its explicit assumptions, while separating philosophical conclusions.

### Detailed Implementation Plan

- Extract the exact finite or probabilistic assumptions used for single-valued stochastic outcomes and parameter choices.
- Compare them with a standard Bell/CHSH-style formulation only as needed to avoid misstating the theorem.
- Formalize the contradiction or inequality under explicit locality, independence, value-assignment, and probability assumptions.
- Test whether the paper's claimed conclusion follows; if not, state the strongest valid theorem and record the logical gap.
- Keep many-worlds, ontology, and “irrelevance” claims in the documentation classification unless separately defined.

### Completion Requirements

- A compiled theorem derives the intended contradiction/inequality from a complete, reviewable list of assumptions, or the exact formal obstruction is documented with a nearby correct theorem.
- No philosophical interpretation is smuggled into a theorem conclusion.
- The relationship between this theorem and the library's locality/no-signalling theorem is explicitly documented; distinct notions of locality are not conflated.
- The source audit covers every substantive Bell-section claim.
- Focused proof checks, full build, and axiom audit pass.

## 12-LIBRARY-AUDIT

### Big Picture Objective

Turn the accumulated formalization into a documented, reusable library and verify the original objective end to end.

### Detailed Implementation Plan

- Stabilize namespaces, imports, theorem names, generality, and public/private boundaries.
- Complete the equation/example/claim-to-declaration map with statuses and explanations for corrections, exclusions, and unresolved items.
- Add representative executable examples and reuse guidance for later quantum-information/locality projects.
- Document all conventions, state/measurement scope, support semantics, information notions, and known limits.
- Run focused tests, the clean full build, forbidden-token and custom-axiom scans, `#print axioms` on main exports, whitespace/diff checks, and documentation/link checks.
- Produce the final project report requested by the user: formalized content, exports, corrections, EPR/teleportation verification, locality/information definitions, unresolved interpretations, build/axiom results, and reuse path.

### Completion Requirements

- The pinned project builds from the documented clean-start procedure.
- No completed project module contains `sorry`, `admit`, an unsafe proof escape, or an unexplained project-specific axiom.
- A recorded axiom audit exists for every principal exported theorem, with all dependencies understood.
- The paper map has no silently omitted equation or major claim; every item has a final status.
- Public documentation and examples are sufficient for another Lean user to embed gates, evolve observables, apply locality results, and state operational information-dependence claims.
- The final report answers every requested end-of-project bullet and distinguishes completed work from open work.
- Any remaining issue is explicit next work with evidence and an unblock path; the goal is not declared complete unless the original objective is genuinely achieved.
