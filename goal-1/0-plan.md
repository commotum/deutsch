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

- The working directory is `/home/jake/Developer/deutsch` in the current environment (the original brief used `/Users/jake/Developer/deutsch`).
- The paper is available as `deutsch-2000/deutsch-2000.md`, with three referenced circuit images in `deutsch-2000/images/`.
- The Markdown source has 760 lines, eight numbered sections, 49 display-math blocks (46 tagged equations numbered (1)–(46) and three unnumbered displays), and three figures.
- The source has sections on Heisenberg computation, gates, EPR, teleportation, locally inaccessible information, Bell's theorem, and the Schrödinger picture.
- The original Python scaffold (`pyproject.toml`, `main.py`, `uv.lock`) remains intact. `README.md` now documents the Lean build and audit commands.
- Stage 2 added a Lake project pinned to Lean/mathlib `v4.32.0`; the resolved mathlib commit is `81a5d257c8e410db227a6665ed08f64fea08e997`.
- The Stage 1 baseline was a clean `master` branch tracking `origin/master`; `deutsch-2000/`, the Python scaffold, and the original goal files remain preserved. Stage 1 and Stage 2 changes are intentionally unstaged in the shared worktree.
- `1-SOURCE-AUDIT` through `12-LIBRARY-AUDIT` are complete with evidence. The original finite,
  corrected library objective is complete; documented extensions remain optional next work.
- The final paper map contains E01–E46, U01–U03, D01–D11, F01–F03, C01–C66, and ten interpretation-boundary groups, each routed in `goal-1/1-SOURCE-AUDIT.md`.
- Stage 2 selected a hybrid representation. Stage 3 now publicly bridges concrete register matrices to finite-Hilbert endomorphisms with `Deutsch.Register.matrixEndEquiv`; abstract tensor-factor probes remain verification-only until a later semantic layer needs them.
- Stage 3 exports arbitrary finite named register bases, selected-`Finset` and ordered-injection embeddings, exact support witnesses, embedded Pauli/projector algebra, normalized pure states, fixed-reference expectation equivalence, and eigenvector transport. It does not claim density/POVM semantics or the arbitrary-disjoint locality theorem prematurely.
- Stage 4 exports arbitrary disjoint-support commutation, the exact nonunitary Gram-factor residue, minimal isometry and physical-unitary Heisenberg locality, and arbitrary-ket expectation invariance. A normalized, formally non-product Bell ket and overlap/support/nonunitary counterexamples verify the theorem boundaries.
- Stage 5 exports typed global descriptor triples/families, minimal Pauli validity with derived reverse laws, exact initial support and arbitrary cross-axis commutation, shared-unitary preservation, constructive generation of every global matrix unit/full operator algebra, explicit initial/evolved Pauli-word bases and reconstruction, and separate equality/conjugacy/fixed-reference comparison relations. Invalid triples/families and a valid reference-equivalent but operator-unequal conjugate regression verify the boundaries.
- Stage 6 exports exact one-qubit, arbitrary-register CNOT, current-descriptor NOT/CNOT, Bell,
  and inverse Bell gates with unitarity, basis amplitudes, explicit at-most support witnesses, all
  Pauli/descriptor maps, and fixed chronology. Equation (18) is contradicted as printed and
  replaced by the compiled signs forced by Equation (17); arbitrary-axis exponentials,
  universality, measurement semantics, and continuum extrapolation remain outside that result.

## Initial Assumptions to Test

- A concrete finite-dimensional matrix model over `ℂ` may be the lowest-risk first representation for explicit qubit calculations, while a finite-dimensional Hilbert-space abstraction may better support reusable locality and measurement theorems. Stage 2 must compare them rather than commit prematurely.
- Tensor-factor embeddings should make the main disjoint-support commutation and Heisenberg locality theorem direct. The exact mathlib API and factor-order convention remain to be established.
- Descriptor completeness may be best stated as generation/reconstruction of the global operator algebra, not as an ontological claim about subsystem states.
- Local statistical independence and joint recoverability can likely be expressed using equality/inequality of restricted Born distributions or reduced states/channels over an explicit parameter family.
- Most gate identities can be proved first for concrete matrices, then lifted through subsystem embeddings and conjugation.
- The paper may contain convention-sensitive or incorrect signs in controlled-NOT and later descriptor formulas; every identity needs independent checking.
- The Bell section should yield a finite contradiction theorem about explicitly stated single-valued stochastic assignments, while the paper's interpretation remains documentation. Equation (45) cannot be reused: it is false as printed, with an executable Boolean counterexample and a truth-table-checked corrected partition recorded in Stage 1.

## Stage 1 Findings and Routed Obligations

- Equation (4) makes `q_z=+1` the bit value 1 and `q_z=-1` the bit value 0, opposite the common quantum-computing labels. This must be tested before interpreting the CNOT projectors and minus signs in (15)–(16).
- The paper moves between local tensor operands and descriptors already defined as global `2^n × 2^n` matrices. In particular, (15) needs a typed correction using local operators or global embedded products.
- Exact operator equality must remain separate from physical equivalence up to global phase. Equations (9)–(11) specify exact ket/matrix elements, while a bare basis-label permutation would leave independent basis phases.
- A pure state can be moved to a fixed reference vector by conjugating observables. A genuinely mixed density operator cannot be unitarily changed into a pure fixed state because rank and spectrum are invariant; any mixed-state analogue needs purification, enlargement, or a corrected representation theorem.
- Descriptor completeness is provisionally routed to algebra generation/reconstruction. Gauge-equivalent descriptor families and equality of fixed-state predictions must not be confused with operator equality or subsystem ontology.
- The discrete disjoint-support gate result does not become an exact locality theorem for arbitrary spatial dynamics merely from arbitrarily accurate circuit simulation. Exact supported Hamiltonian/channel theorems and approximate extrapolations require separate hypotheses.
- The source's information definitions are asymmetric and representation-sensitive. Stage 7 therefore separately formalizes descriptor dependence, local and joint statistical dependence, operational distinguishability, recovery, and explicit circuit/channel provenance.
- Local Bloch-vector claims such as (26) require a proved bridge to all local effects/measurements. Parameter independence is preserved only by parameter-independent local processing with fixed independent ancillas.
- “Decoherence” and “classical channel” claims require named basis-dependent channels or environment dilations. Wrong-basis dephasing and bit errors are required negative tests; no generic robustness claim is accepted.
- Equations (35)–(37) establish at most a one-parameter local-output calculation until Stage 9 proves arbitrary-input, branch-complete, preferably reference-preserving channel correctness.
- The Bell argument needs a finite common probability space/counterfactual assignment,
  setting-independent weights and setting-local responses, plus positive-support handling of (43).
  Equation (45) is false at `(a_0,a_1,a_2)=(1,0,1)` and the corrected complementary partition
  passes all eight Boolean cases. Stage 11 independently proves the corrected three-setting
  contradiction without using either form of Equation (45).
- No PDF/facsimile is present, so the Markdown transcription itself remains an external-fidelity assumption to document in the final audit.

## Stage 2 Findings and Representation Commitments

- Lean and mathlib are pinned to `v4.32.0`; the default `Deutsch` and `DeutschTests` targets build together. Public modules do not import `Mathlib.Tactic`.
- The paper's logical bit `1` is raw matrix index `0` and the `+1` eigenspace of `Z`; logical bit `0` is raw index `1` and the `-1` eigenspace. Raw product pairs flatten as `00,01,10,11`, hence paper-labelled pairs flatten as `11,10,01,00`.
- `A ⊗ₖ B` acts on the first/left and second/right product coordinates respectively. All eight left/right `X` actions on the two-qubit paper-labelled basis are executable regression tests.
- Heisenberg evolution is `U† A U`. A phase-sensitive gate and both transformed `X` eigenvectors independently distinguish it from `U A U†`.
- CNOT uses left target, right control, and activates on paper bit `1`. Its four-case truth table, independent permutation matrix, involution, and all six Pauli conjugations compile.
- With `R_x(π/2)=(I-iX)/√2`, the verified Heisenberg signs are `Y ↦ -Z` and `Z ↦ Y`. Lean rejected the initially expected opposite mnemonic signs, preventing convention drift.
- Fig. 1 chronology is represented by `(I ⊗ H) * CNOT`, with inverse `CNOT * (I ⊗ H)`; both product orders reduce to the identity.
- Concrete probes compile positive trace-one matrices, effects, finite measurements, and an explicit maximally mixed `1/2,1/2` distribution. Abstract probes compile rank-one densities, effects, finite-measurement normalization, adjoints, disjoint tensor commutation, and binary Heisenberg locality.
- The Stage 2 probes did not prove general Born weights real and in `[0,1]`. Stage 7 now supplies
  the required cyclic-trace/factorization proof without incorrectly assuming that `ρE` is positive
  semidefinite.
- Mixed states remain positive trace-one operators. No theorem may unitary-conjugate an arbitrary mixed state to a fixed pure state; the rank/spectrum obstruction remains a later formal obligation.
- `docs/conventions.md` and `docs/representation.md` are authoritative for module boundaries, rejected alternatives, and migration risks. Stage 3 has since discharged the matrix/endomorphism bridge and arbitrary selected-factor obligations; abstract tensor reassociation remains a documented migration concern rather than an unproved identification.

## Stage 3 Findings and Register Commitments

- A finite register is named by any finite decidable type `Q`; its computational labels are `Q → Fin 2`, its Hilbert carrier is `EuclideanSpace ℂ (Q → Fin 2)`, and its concrete operators are square matrices on that basis. `Fin n` is a specialization rather than a baked-in indexing policy.
- `matrixEndEquiv` is the public algebra equivalence from register matrices to Hilbert endomorphisms. Its action and conjugate-transpose/adjoint compatibility are compiled theorems, so state proofs do not silently identify unrelated coordinate representations.
- For `s : Finset Q`, `embedSubsystemAlgHom s` is reindexed `A ⊗ I` along an explicit selected/complement basis split. It is injective and preserves the full algebraic, adjoint, Hermitian, unitary, and Heisenberg structure needed downstream.
- A `Finset` records selected labels but not the order of an input register. `embedAlong (p : K ↪ Q)` is therefore a separate ordered placement; equal ranges with opposite injections are proved to yield different placements for a nonsymmetric operator.
- `IsSupportedOn s A` is an explicit local-operator image witness. It is closed under same-support algebra and adjoint/Heisenberg operations. A compile-clean general proof probe derives commutation for arbitrary disjoint selected subsystems, confirming this support representation is sufficient for Stage 4.
- Public embedded Pauli operators satisfy the complete signed same-coordinate Pauli algebra and are Hermitian/unitary. Arbitrary one-qubit operators at distinct coordinates commute. Paper-bit projectors satisfy their exact `(I±Z)/2` formulas, idempotence, complementarity, orthogonality, and `Z=±1` sector laws under the reversed source convention.
- Every normalized finite-register pure ket is exactly a unitary image of the all-paper-zero reference ket. `PureState.exists_fixed_reference_representation` then proves the fixed-reference Heisenberg expectation equality for every matrix operator. This is explicitly a pure-state theorem and does not repair the source's mixed-state sentence by rank-changing conjugation.
- Unitary hypotheses are explicit in norm preservation, algebra-homomorphic Heisenberg results, and eigenvector transport. Tests prove zero/nonunitary matrices fail the corresponding norm and identity claims.
- `docs/registers.md` distinguishes coordinate equality, operator equality, one-state expectation
  equality, all-state equality, and joint-distribution equality. Stage 7 adds density matrices,
  effects, POVMs, channels, and operational information notions in a separate public layer.

## Stage 4 Findings and Locality Commitments

- `embedSubsystem_commute_of_disjoint` proves full operator commutation for arbitrary matrices embedded on arbitrary disjoint finite selected subsystems. `supportedOperators_commute_of_disjoint` lifts the result through semantic `IsSupportedOn` witnesses; no unitary or state hypothesis is involved.
- Commutation alone gives `heisenberg U A = (Uᴴ * U) * A`. Exact fixing requires only the minimal isometry identity `Uᴴ * U = 1`; the physical public specialization takes matrix-unitary membership, and a bundled `UnitaryOperator` form is also exported.
- The locality theorem is operator-first and state-independent. Its Heisenberg- and Schrödinger-form expectation corollaries quantify over every register ket without assuming a tensor-product state.
- The entangled regression is formal: a normalized two-qubit Bell ket is proved not to satisfy an explicit coordinate product-vector predicate before remote expectation invariance is instantiated on it.
- Multi-label nonadjacent sets and empty support compile. Overlap is necessary (`X†ZX=-Z` on one coordinate), exact remote support cannot be fabricated, and a disjoint but nonunitary zero action fails to fix a nonzero remote observable.
- The result is exact finite supported-operation locality. Stage 7 separately supplies finite Kraus
  channel no-signalling and density/POVM semantics; neither result is a continuum/spatial-dynamics
  limit or an ontological criterion. C19's approximation extrapolation remains unresolved.
- `docs/locality.md` is authoritative for this boundary and for the hierarchy from commutation to cancellation to expectations.

## Stage 6 Findings and Gate Commitments

- `Deutsch.Gates.OneQubit` separates exact matrices, exact basis action, equality up to an explicit
  phase, and equality of Heisenberg action. The paper's Equation (14) square-root branch is valid
  and squares exactly to NOT, but it is not `rotationX (π/2)`.
- With `rotationX θ = cos(θ/2)I - i sin(θ/2)X` and `U† A U`, symbolic proofs give
  `Y ↦ cos θ Y - sin θ Z` and `Z ↦ sin θ Y + cos θ Z`. Checks at `0`, `±π/2`, and `π`
  reproduce the conflict: both sine signs in Equation (18) are wrong under Equation (17).
  The full arbitrary-axis/matrix-exponential schema remains conservatively partial.
- `cnotAt target control h` is an ordered arbitrary-register coherent permutation, activated by
  paper bit `1`/raw index `0`. It has exact entries and basis action, a typed global-projector
  Equation (15), and all six Equation (16) maps. `cnotFromDescriptors` proves the same polynomial
  unitary and transformations for every valid current descriptor family.
- Fig. 1 chronology is fixed definitionally by
  `bellAt = hadamardAt control * cnotAt target control h`; the inverse reverses those factors.
  Both inverse products, all twelve Equations (20)–(21) generator maps, exact arbitrary-register
  amplitudes, and pair-support witnesses compile.
- `IsSupportedOn s A` is used as an at-most support witness; gate documentation makes no
  minimal-support claim. CNOT remains a coherent gate, not a measurement or discarded record.
  Universality after Equation (19), channel semantics, and the finite-to-continuum leap remain
  unresolved or downstream rather than imported assumptions.
- The focused gate suite includes target/control, chronology, phase, sign, amplitude, current-frame,
  and remote-locality regressions. The final Stage 6 integrity audit scans 29 Lean sources,
  requires 29 gate oracles and 55 public gate declarations, and accepts 132 axiom reports using
  only `Classical.choice`, `Quot.sound`, and `propext`; the full build passes 3273 jobs.

## Stage 7 Findings and Information-Semantics Commitments

- Density states are positive semidefinite trace-one matrices; effects are positive semidefinite
  matrices with positive complements; finite POVMs sum to identity. Born reality, nonnegativity,
  upper bounds, and normalization are proved from these hypotheses rather than assumed.
- Selected-subsystem reduction is an explicit partial trace compatible with the register basis
  split. It is positive, trace-preserving, and trace-dual to embedded effects. Equality of reduced
  densities is exactly equality of all local-effect probabilities; three Pauli probabilities are
  complete for a one-qubit reduction.
- Finite physical processing uses typed Kraus families with a compiled completeness equation.
  Identity, unitary, composition, density action, dual-effect action, and Born duality are public.
  A channel acting on one selected subsystem preserves every disjoint reduced density, even for an
  entangled input; fixed-channel data processing does not license parameter-dependent processing.
- Statistical equivalence, weak detectability, local/joint independence, recovery by a specified
  decoder, descriptor nonconstancy, and supplied preparation/process provenance are distinct APIs.
  No final density matrix is claimed to determine its construction history.
- The same-register pure fixed-reference representation does not extend to arbitrary mixed states:
  a compiled purity argument rules out unitarily evolving the maximally mixed qubit to the pure
  reference. Density Schrödinger/Heisenberg expectation duality is the valid general substitute.
- A two-qubit classical one-time-pad family provides a boundary example: both singleton marginals
  are constant, joint parity detects the parameter, an explicit Kraus decoder recovers it, and two
  pointwise-distinct preparation histories realize the same final density family. The paper's EPR
  instantiation is supplied separately by Stage 8.

## Stage 8 Findings and EPR Commitments

- Fig. 2 is fixed as a four-wire finite circuit with inverse Bell on `q2,q3`, independent local
  `x` rotations, coherent recording CNOTs into `q1,q4`, explicit transport metadata for `q4`, and
  a final comparison CNOT. Unitarity, finite support, and Equations (23)/(24) compile at named
  boundaries; coherent recording is not called measurement or decoherence.
- The conventional library Hadamard prepares the same Equation (22) ray with a global phase:
  the displayed source ket is exactly `-i` times the compiled inverse-Bell ket. Equation (38) now
  has the corresponding named phase-aware ket theorem at `φ=0`.
- Equations (25) and (27) inherit both wrong sine signs from Equation (18). Their corrected
  descriptor triples and a `pi/2` source-disagreement regression compile under the fixed
  `rotationX`/Heisenberg convention.
- Equations (28) and (41) are complementary to the raw outcomes forced by Equations (22)/(23).
  The compiled circuit gives `P(different)=sin²((θ-φ)/2)` and
  `P(a=1,b=1)=(1/2)cos²((θ-φ)/2)`; equal-setting and difference-`pi` theorems expose the printed
  contradiction. Any later Bell argument must use these corrected outcomes or explicitly
  complement Bob's result.
- Both singleton reductions are maximally mixed for arbitrary settings, which is lifted to
  equality of every singleton effect statistic. A finite setting family is nevertheless jointly
  detectable, so descriptor occurrence, local statistical independence, joint accessibility,
  recovery, and supplied history remain distinct notions.
- Equation (39) is proved for the two explicit state-preparation routes at ket and density level.
  Pointwise-distinct route histories can produce the same final density, so provenance remains
  supplied circuit data rather than a property recovered from the final state.

## Final Paper Claim Map

- The authoritative Stage 1 ledger is `goal-1/1-SOURCE-AUDIT.md`; later stages must update its lifecycle dispositions and declaration names rather than creating an unlinked second map.
- Equations (1)–(8) route primarily to registers, descriptors, locality, and information; (9)–(21) and Fig. 1 to gates; (22)–(28) and Fig. 2 to EPR; (29)–(37) and Fig. 3 to teleportation; (38)–(39) to EPR/provenance; and (40)–(46) to EPR statistics plus the Bell audit.
- Decoherence claims have no dedicated numbered equations in the paper; their obligations are preserved as prose-claim entries and must not be omitted for lack of an equation tag.
- Interpretative claims about ontology, actual outcomes, nonlocal influence, and picture choice are explicitly separated from formal obligations in I01–I10.

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

### Status

Complete with evidence on 2026-07-16.

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

### Evidence

- `python3 -B goal-1/check_source_audit.py` reports exact E01–E46/source-tag agreement, all 49 display blocks with U01–U03, exact F01–F03 IDs and resolved image links, contiguous D01–D11/C01–C66/I01–I10 identifiers, complete LC01–LC66 class/status pairs, and a passing equation-(45) counterexample/corrected truth table.
- A manual section-by-section review supplies the semantic evidence for definition and prose-claim completeness; the checker deliberately proves identifier coverage, not the judgment that a prose inventory is exhaustive.
- All three figures were visually inspected: their upward chronology, wires, controls/targets, transports, and stage boundaries are recorded in F01–F03.
- No Lean build, Lean forbidden-token scan, or `#print axioms` audit is applicable yet because there are zero Lean files and no Lake project. Those mechanisms remain mandatory Stage 2 deliverables rather than vacuous Stage 1 passes.
- `git diff --check`, explicit no-index checks for both new files, and a trailing-whitespace scan pass; the final Stage 1 status/diff is recorded in the stage file without deleting or staging user work.

## 2-FOUNDATIONS

### Status

Complete with evidence on 2026-07-16.

### Big Picture Objective

Establish the pinned Lean project, test mathlib's relevant APIs and conventions, and choose representations that support both reusable theorems and concrete calculations.

### Detailed Implementation Plan

- Create and pin the Lean 4/mathlib project without disturbing the existing source files.
- Probe mathlib support for complex matrices, finite-dimensional inner-product spaces, linear maps, continuous linear maps if needed, tensor products/Kronecker products, adjoints, unitaries, density operators, traces, and finite probability distributions.
- Compare at least a concrete `Matrix` model and an abstract finite Hilbert-space/operator model against the required locality, embedding, and computation proofs.
- Write a conventions document and executable smoke tests for basis order, tensor order, multiplication direction, adjoint, Pauli matrices, and a two-qubit basis.
- Make the first compiled oracle check `Z`/bit labels, both Pauli multiplication orders, factor embeddings on every two-qubit basis vector, `U† A U` chronology, all four CNOT cases and six Pauli conjugations, `R_x(π/2)` signs, and Bell/inverse composition.
- Compare concrete `Matrix` and abstract endomorphism/finite-Hilbert representations with compiled probes for locality, adjoint, trace/density matrices, tensor embeddings, and finite measurement semantics before selecting the public layer.
- Record how mixed states are represented without assuming that unitary conjugation turns a mixed density operator into the fixed pure reference state.
- Establish module boundaries, namespace policy, public API rules, build/test commands, and automated checks for forbidden proof holes and axioms.

### Completion Requirements

- Pinned toolchain and dependency files exist, and a minimal project builds with the documented command.
- Representation decisions are justified by compiled probes, with rejected alternatives and migration risks recorded.
- All global algebraic and circuit conventions are documented and covered by executable Lean examples.
- The source audit points to intended module/declaration locations.
- A baseline forbidden-token scan and axiom-audit mechanism are present and run successfully.

### Evidence

- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin Lean/mathlib `v4.32.0` and resolved mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Focused compilation of `DeutschTests/Foundations/Concrete.lean`, `Abstract.lean`, and `MatrixSemantics.lean` exits 0 without warnings; `lake build` succeeds for both default targets with 3249 jobs.
- `goal-1/check_lean_integrity.py` scans 8 Lean source files, rejects proof holes/unsafe/project axioms, checks 37 required convention/API oracles and exact pins, compiles 22 representative axiom reports, and accepts only `propext`, `Classical.choice`, and `Quot.sound`.
- `goal-1/check_source_audit.py` preserves exact source/ledger coverage and distinguishes `Oracle verified` finite checks from prohibited premature `Proved` paper-equation status.
- `goal-1/check_doc_links.py` validates all 9 repository-local links in the 3 public Markdown files.
- The representation decision, convention theorem names, known gaps, exact command output, initial smoke failures, and final worktree checks are recorded in `goal-1/2-FOUNDATIONS.md`.

## 3-REGISTERS

### Status

Complete with evidence on 2026-07-16.

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

### Evidence

- Public `Deutsch.Register` re-exports `Basic`, `Embedding`, `Pauli`, and `State`; the project root imports it. The implementation contains no proof holes, unsafe declarations, or project axioms.
- `DeutschTests/Register.lean` verifies dimensions for one through three qubits, the paper-zero raw index, exact left/right two-factor coordinate bridges, exhaustive outer-coordinate three-qubit behavior, nonadjacent commutation, order-sensitive injected placement, support closure, nonunitary counterexamples, and eigenvector transport.
- `lake env lean DeutschTests/Register.lean` exits 0 without output; `lake build Deutsch.Register.Embedding DeutschTests.Register` succeeds with 3092 jobs; the full `lake build` succeeds with 3255 jobs.
- `goal-1/check_lean_integrity.py` scans 14 Lean sources, requires 37 foundation oracles, 18 register verification oracles, and 26 Stage 3 public declarations, compiles 48 `#print axioms` reports, and observes only `Classical.choice`, `Quot.sound`, and `propext`.
- The source audit passes after conservative Stage 3 lifecycle updates; general disjoint-subsystem locality, descriptors, density/measurement semantics, and mixed-state wording remain explicitly downstream.
- The documentation link audit passes 4 Markdown files and 18 local links. `git diff --check` and a targeted trailing-whitespace scan report no findings. Exact declarations, commands, and boundaries are recorded in `goal-1/3-REGISTERS.md`.

## 4-LOCALITY

### Status

Complete with evidence on 2026-07-16.

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

### Evidence

- Public `Deutsch.Locality` re-exports `Basic` and `Heisenberg`; the project root imports it. Arbitrary disjoint selected-subsystem commutation is proved entrywise and then exposed through exact support witnesses.
- The public Heisenberg layer separates the Gram residue, minimal isometry cancellation, unitary/bundled-unitary locality, and arbitrary-ket prediction corollaries. No proof relies on a product-state assumption.
- `DeutschTests/Locality.lean` verifies nonadjacent multi-label and empty supports, a normalized non-product Bell ket, overlap and fabricated-support failures, and a disjoint nonunitary counterexample.
- `lake env lean DeutschTests/Locality.lean` exits 0; `lake build Deutsch.Locality DeutschTests.Locality` succeeds with 3095 jobs; the full `lake build` succeeds with 3259 jobs.
- The integrity checker scans 18 Lean sources, requires 17 locality regression oracles and 9 Stage 4 public declarations, and accepts all 57 representative axiom reports with only `Classical.choice`, `Quot.sound`, and `propext`.
- Source and documentation audits pass after conservative lifecycle updates; the docs audit covers 5 Markdown files and 28 local links. Whitespace/diff/status checks pass as recorded in `goal-1/4-LOCALITY.md`.

## 5-DESCRIPTORS

### Status

Complete with evidence on 2026-07-16.

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

### Evidence

- `Deutsch.Descriptor` re-exports validity, comparison, constructive generation, and Pauli-basis modules. Initial families satisfy every same-label signed Pauli law and every distinct-label/axis commutator; shared unitary conjugation preserves family validity.
- `DescriptorFamily.initial_generates_operator_algebra` constructively builds all standard matrix units and the full algebra for arbitrary finite labels, including `Empty`. `PauliWord.reconstruction` and `evolvedReconstruction` independently give exact initial/evolved coefficient expansions and genuine bases.
- `DescriptorFamily.GeneratesOperatorAlgebra.evolve` proves completeness preservation through the unitary star-algebra automorphism. Comparison APIs and a compiled `-Z` stabilizer example separate exact operator equality, conjugacy, and fixed-reference component expectations.
- `DeutschTests/Descriptor.lean` compiles cleanly and requires 25 named positive/negative/boundary oracles. The focused build succeeds with 3261 jobs; the full `lake build` succeeds with 3268 jobs.
- The integrity audit scans 24 Lean sources, requires 20 Stage 5 public declarations, and accepts all 77 axiom reports with only `Classical.choice`, `Quot.sound`, and `propext`. Source coverage, 6-file/38-link documentation, forbidden-token, diff, and trailing-whitespace checks pass as recorded in `goal-1/5-DESCRIPTORS.md`.

## 6-GATES

### Status

Complete with evidence on 2026-07-16.

### Big Picture Objective

Independently verify the elementary gate and Bell-transform identities under one fixed, tested convention.

### Detailed Implementation Plan

- Define Pauli/NOT gates, square-root-of-NOT if retained, axis rotations, Hadamard, CNOT with named control and target, and the Bell transform.
- Prove unitarity and compute Heisenberg conjugation on Pauli descriptors algebraically.
- Derive rotation formulas from exponentials or a rigorously equivalent closed form, including signs and angle conventions.
- Lift concrete identities into arbitrary registers using embeddings and the locality API.
- Compare every result with paper equations (9)–(21), documenting sign, tensor-order, or control/target corrections.
- Add basis-action and matrix-equality examples that independently cross-check descriptor formulas.

### Completion Requirements

- Each public gate is proved unitary and has verified basis action where applicable.
- Heisenberg transformations for Pauli/NOT, rotations, Hadamard, CNOT, and Bell compile as operator equalities.
- At least two independent checks pin CNOT control/target and circuit composition order.
- Any discrepancy with the paper is reproduced, explained, and replaced by the strongest correct statement.
- Focused gate tests, full build, and forbidden-token scan pass.

### Evidence

- `Deutsch.Gates` re-exports `OneQubit`, `CNOT`, and `Bell`, and the project root imports it.
  Exact local and arbitrary-register basis amplitudes independently cross-check all component
  conjugations; current-descriptor NOT/CNOT theorems carry explicit validity hypotheses.
- `DeutschTests.Gates` provides 29 required positive, negative, order, sign, locality, and
  amplitude regressions. Focused builds and `DeutschTests.Audit` compile without warnings or
  forbidden dependencies.
- `goal-1/check_lean_integrity.py` scans 29 Lean sources, requires 55 Stage 6 public declarations,
  and accepts all 132 representative axiom reports with only `Classical.choice`, `Quot.sound`, and
  `propext`. Source coverage, the 7-file/49-link documentation audit, diff/whitespace hygiene, and
  the final 3273-job `lake build` pass. Exact declarations and boundaries are recorded in
  `goal-1/6-GATES.md` and `docs/gates.md`.

## 7-INFORMATION

### Status

Complete with evidence on 2026-07-16.

### Big Picture Objective

Define precise state, measurement, channel, and parameter-dependence notions adequate for the paper's operational claims.

### Detailed Implementation Plan

- Formalize density operators, effects, finite POVMs, Born expectations/probabilities, and their
  pure-state bridge, expanding to mixed states wherever the theorem naturally permits.
- Define explicit selected-subsystem partial trace and prove positivity, trace preservation,
  embedded-effect duality, all-effect tomography, and the one-qubit Pauli criterion.
- Define typed finite Kraus channels, their density and dual-effect actions, identity/unitary/
  composition constructions, fixed-channel data processing, and exact disjoint-subsystem
  reduced-state invariance.
- For parameterized state or descriptor families, separately define descriptor dependence,
  local/joint statistical equivalence and independence, operational distinguishability, exact
  recovery by a specified channel, and explicit preparation/process provenance.
- Prove an executable mixed-state obstruction to the fixed-pure-reference overreach and provide
  density evolution/expectation duality as the correctly scoped substitute.
- Use a classical diagonal one-time-pad family to separate local independence, joint detection,
  recovery, and construction history without consuming the paper's EPR example.

### Completion Requirements

- Every “information” predicate has a semantic definition, documented quantifiers, and stated subsystem/measurement class.
- Local and joint statistical dependence are demonstrably distinct via compiled examples.
- At least one theorem connects local reduced-state equality, equality of all local measurement statistics, and failure of local distinguishability under explicit assumptions.
- Pure-state-only restrictions are documented; results valid for density operators are proved at that level.
- No theorem infers information location solely from syntactic parameter occurrence.

### Evidence

- `Deutsch.Information` publicly re-exports state, reduction, channel, local-channel, dependence,
  qubit, and one-time-pad modules; the project root imports the umbrella.
- `DeutschTests.Information` supplies 33 required positive, negative, and boundary oracles,
  including general Born bounds, partial-trace duality/tomography, channel duality/data processing,
  entangled-input disjoint-channel invariance, the mixed-state obstruction, and the one-time-pad
  separation/recovery/history results.
- Focused information and axiom-audit modules compile cleanly; the full `lake build` succeeds with
  3282 jobs.
- `goal-1/check_lean_integrity.py` scans 38 Lean sources, requires 78 Stage 7 public declarations,
  and accepts all 210 representative axiom reports with only `Classical.choice`, `Quot.sound`, and
  `propext`.
- The exact source audit and 8-file/68-link documentation audit pass. `git diff --check` and the
  targeted completed-project trailing-whitespace scan report no findings. Exact declarations and
  boundaries are recorded in `goal-1/7-INFORMATION.md` and `docs/information.md`.

## 8-EPR

### Status

Complete with evidence on 2026-07-16.

### Big Picture Objective

Reconstruct the EPR example and separate circuit algebra, descriptor evolution, local statistics, joint correlations, and interpretation.

### Detailed Implementation Plan

- Encode the paper's EPR preparation and measurement-basis choices under the fixed gate/order convention.
- Verify the global state/circuit result and derive the relevant Heisenberg descriptor evolution.
- Preserve Equation (22)'s printed global phase separately from the conventional-Hadamard circuit
  ket and prove exact density/prediction agreement.
- Correct the sine signs inherited from Equation (18) in Equations (25)/(27), with special-angle
  non-equality tests against the printed formulas.
- Prove local measurement statistics are independent of the remote setting/outcome under the appropriate no-signalling hypotheses.
- Prove the corrected joint correlations: unequal-record probability
  `sin²((theta-phi)/2)` and joint-paper-one probability `(1/2) cos²((theta-phi)/2)`, including
  compiled equal-setting counterexamples to the printed complementary formulas.
- Identify which claims concern a specific circuit and which follow from general channel locality/no-signalling.
- Update the paper map with corrected equations and exclude unformalized ontological conclusions.

### Completion Requirements

- The EPR circuit's state and descriptor calculations compile and agree through independent Schrödinger/Heisenberg cross-checks.
- Local marginal independence is proved for the exact allowed parameter family and measurement class.
- Joint correlation dependence is proved with an explicit statistic or measurement.
- The result is tested on an entangled state and does not silently assume separability.
- Interpretative statements about where information “really” travelled are labeled as interpretations unless captured by a defined operational predicate.

### Evidence

- `Deutsch.EPR` re-exports the pair, named four-wire circuit, density/statistics, and provenance
  modules; the project root imports it. The production layer compiles Equations (22)–(24),
  corrected Equations (25)/(27)/(28)/(41), Equation (38)'s explicit global phase, Equation (39)'s
  equal route outputs, Equation (40)'s pair-level marginals, finite support/unitarity, all-effect
  singleton independence, joint detection, and distinct supplied histories.
- `DeutschTests.EPR` supplies 24 required positive, boundary, correction, and semantic-separation
  oracles. The focused module and the representative axiom audit compile cleanly.
- `goal-1/check_lean_integrity.py` scans 44 Lean sources, requires 39 Stage 8 public declarations,
  and accepts all 249 representative axiom reports with only `Classical.choice`, `Quot.sound`, and
  `propext`. The full `lake build` succeeds with 3288 jobs.
- The exact source checker and the 9-file/80-link documentation audit pass. `git diff --check` and
  the targeted completed-project trailing-whitespace scan report no findings. Exact declarations,
  corrections, and interpretation boundaries are recorded in `goal-1/8-EPR.md` and `docs/epr.md`.

## 9-TELEPORTATION

### Status

Complete with evidence (2026-07-16).

### Big Picture Objective

Verify teleportation while keeping correctness, observable evolution, local inaccessibility, classical outcomes, and later recovery mathematically distinct.

### Detailed Implementation Plan

- Encode the Bell-pair preparation, Bell measurement/unitary equivalent, outcome registers, controlled corrections, and any deferred-measurement/coherent version needed for clean unitary reasoning.
- Prove exact coherent-ket factorization for an arbitrary input pure state, derive receiver-density
  equality, and extend to an identity channel and arbitrary entangled reference when the compiled
  tensor/channel APIs support it; state any remaining reference boundary explicitly.
- Compute the relevant Heisenberg descriptors through the circuit and compile the corrected sine
  signs rather than importing the paper's propagated Equation (18) error.
- Exhibit Equation (33)'s unitary, prove all nine generator images, and check all four correction
  branches rather than only the receiver components used later.
- Prove that designated intermediate local/classical registers have parameter-independent local statistics while suitable joint correlations retain dependence.
- Prove recovery after later access to the classical outcomes/correction interaction using the operational recovery definition.
- State decoherence assumptions separately rather than building them silently into “classical channel.”

### Completion Requirements

- End-to-end teleportation correctness is a compiled theorem with input and reference-system scope stated.
- Descriptor calculations are verified under the same convention as the gate library.
- Intermediate local independence and joint dependence/recoverability are separate theorems.
- All correction branches or their coherent controlled equivalent are checked.
- Paper teleportation equations/claims have proved, corrected, partial, interpretative, or unresolved statuses.

### Evidence

- `Deutsch.Teleportation` exports the exact five-wire chronology and support, explicit Equation
  (33) correction with nine generator images and four branches, corrected Equations (29)–(37),
  arbitrary-input coherent factorization, receiver reduction, corrected purity/all-effect
  statistics, and literal full-circuit U02 verification.
- A separately constructed uniform-branch encoder/decoder is the identity on all one-qubit
  operators and densities, with singleton local independence, joint detection, branch-specific
  omission witnesses, and supplied Alice-to-Bob metadata. Its branch corrections are tied to the
  explicit gate; no coherent-circuit-to-dephasing bridge or arbitrary-reference circuit theorem is
  claimed.
- Focused EPR/teleportation checks compile. The full build succeeds with 3296 jobs. The integrity
  audit scans 52 Lean sources, requires 38 Stage 9 oracles and 82 public declarations, and accepts
  335 representative axiom reports with only `Classical.choice`, `Quot.sound`, and `propext`.
  Source coverage and the 10-file/93-link documentation audit pass.

## 10-DECOHERENCE

Complete with evidence (2026-07-16).

### Big Picture Objective

Make only the decoherence and “classical channel” statements justified by explicit mathematical models.

### Detailed Implementation Plan

- Identify exactly where the paper relies on decoherence, copying, measurement, discarded environments, or effectively classical records.
- Model the minimal relevant channel/environment interaction, with basis and trace/discard assumptions explicit.
- Prove the resulting diagonalization, local indistinguishability, record stability, or recovery statements actually needed by the EPR/teleportation discussion.
- Add wrong-basis dephasing and bit-error counterexamples that demonstrate why the selected basis/channel hypotheses are necessary.
- Separate exact finite-dimensional channel results from approximate physical claims and from broad interpretative prose.

### Completion Requirements

- Every formal decoherence theorem names its channel, environment state, basis, and exact/approximate status.
- No generic claim that “decoherence occurs” appears without hypotheses.
- At least one channel-level calculation connects the model to the teleportation/classical-record results, or an exact obstruction and useful substitute are documented.
- Pure and mixed state scope is explicit.
- Full build and axiom audit for the new results pass.

### Evidence

- `coordinateDephasing` is a constructive finite Kraus channel with exact coordinate-block entry
  action, trace preservation, a fixed-point characterization, basis-density stability,
  idempotence, repeated Z-statistic preservation, and complementary-X disturbance.
- A fixed paper-zero environment and unitary system-control/environment-target CNOT produce the
  same Kraus projectors when the final environment basis label is summed out. This is an exact
  output-label discard realization; no unproved joint-density partial-trace identity is claimed.
- `protocolRecordDephasing` fixes every operator produced by the separate semantic teleportation
  encoder, and the existing decoder recovers every input density afterward. A genuine unitary
  first-record bit flip instead maps encoded basis inputs to the opposite family and makes recovery
  fail explicitly. The still-missing coherent-five-wire/dephased-semantic-encoder equality remains
  documented rather than assumed.
- Repeated `q4` dephasing before the final EPR comparison preserves only the named final `q1`
  paper-one probability for every pre-comparison density. A constructive mixture of product basis
  densities has the same U03 Z moments as the Bell resource, proving those moments alone do not
  witness entanglement.
- Focused Stage 10 verification builds 2727 jobs; the full build succeeds with 3302 jobs. The
  integrity audit scans 58 Lean sources, requires 18 Stage 10 oracles and 33 public declarations,
  and accepts 368 representative axiom reports with only `Classical.choice`, `Quot.sound`, and
  `propext`. Source coverage and the 11-file/97-link documentation audit pass, as do forbidden
  token, trailing-whitespace, and diff checks.

## 11-BELL-AUDIT

Complete with evidence (2026-07-16).

### Big Picture Objective

Formalize the mathematical contradiction in the paper's Bell discussion only under its explicit assumptions, while separating philosophical conclusions.

### Detailed Implementation Plan

- Extract the exact finite or probabilistic assumptions used for single-valued stochastic outcomes and parameter choices.
- Compare them with a standard Bell/CHSH-style formulation only as needed to avoid misstating the theorem.
- Formalize the contradiction or inequality under explicit locality, independence, value-assignment, and probability assumptions.
- Do not formalize printed equation (45) as an identity. Use the corrected complementary-event partition or a simpler finite three-setting pigeonhole inequality, and record the exact relation to the invalid printed derivation.
- Formulate only the finitely many counterfactual settings needed for the proof so almost-sure equalities do not require uncountable intersections of null sets.
- Test whether the paper's claimed conclusion follows; if not, state the strongest valid theorem and record the logical gap.
- Keep many-worlds, ontology, and “irrelevance” claims in the documentation classification unless separately defined.

### Completion Requirements

- A compiled theorem derives the intended contradiction/inequality from a complete, reviewable list of assumptions, or the exact formal obstruction is documented with a nearby correct theorem.
- No philosophical interpretation is smuggled into a theorem conclusion.
- The relationship between this theorem and the library's locality/no-signalling theorem is explicitly documented; distinct notions of locality are not conflated.
- The source audit covers every substantive Bell-section claim.
- Focused proof checks, full build, and axiom audit pass.

### Evidence

- `Deutsch.Bell.SourceCorrection` independently compiles the false printed Equation (45)
  counterexample and corrected Boolean partition. `Deutsch.Bell.Finite` proves the common-table
  and explicit two-party inequalities with setting-local response signatures and
  setting-independent nonnegative normalized weights.
- `perfectEqualSettingSupport_of_agreementProbability_one` derives equal responses on every
  positive-weight assignment from equal-setting probability one, leaving zero-weight tables
  unconstrained. The strongest integrated theorem therefore assumes only the finite model's
  weights and reproduction of the complete corrected quantum agreement table.
- `Deutsch.Bell.Quantum` derives `cos²((theta-phi)/2)`, exact `1/4` values for every distinct pair
  among `0,2π/3,4π/3`, and perfect equal-setting agreement from the corrected Stage 8 Born
  result. `corrected_epr_three_settings_refute_normalized_local_model` and its negated wrapper
  compile the contradiction without importing the source's false Equations (41) or (45).
- Focused verification builds 2723 jobs; the full build succeeds with 3308 jobs. The integrity
  checker scans 64 Lean sources, requires 15 Bell oracles and 34 ordered Bell public declarations,
  and accepts 402 representative axiom reports using only `Classical.choice`, `Quot.sound`, and
  `propext`. Source coverage, the 12-file/98-link documentation audit, and hygiene checks pass.

## 12-LIBRARY-AUDIT

Complete with evidence (2026-07-16). All twelve stages and the original finite corrected objective
are complete.

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

### Evidence

- The public root has ten topic umbrellas and the verification root has 15 focused imports. The
  integrity checker locks 49 ordered production import edges, rejects production-to-test imports,
  and requires seven thin examples that compile through the public root alone.
- The finalized source map has no `Planned` entry. Its 66 prose statuses are 22 corrected, 31
  partial, eight excluded, and five unresolved; its 63 equation/display/definition/figure statuses
  are six oracle verified, 25 corrected, 31 partial, and one excluded. Every partial/unresolved
  item names its exact boundary or extension path.
- `docs/reuse.md` and `DeutschTests.Examples` demonstrate named embedding/gate placement,
  Heisenberg evolution, locality, operational information semantics, and corrected Bell reuse.
  `docs/project-report.md` records public exports, corrections, central results, limitations,
  verification, and extension paths.
- After `lake clean deutsch`, the default build completed 3309 jobs. SHA-256 manifests of 110
  non-generated files and full worktree status were unchanged across cleaning/building. The final
  integrity audit scans 65 Lean sources and accepts 402 ordered principal axiom reports using only
  `Classical.choice`, `Quot.sound`, and `propext`.
- Source coverage passes; all 14 expected public Markdown files and 118 local links pass; focused
  examples, forbidden-token/custom-axiom/opaque checks, trailing whitespace, import closure,
  `git diff --check`, and worktree-preservation checks pass.
