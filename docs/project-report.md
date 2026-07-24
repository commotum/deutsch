# Project report

## Result and scope

This repository is a pinned Lean 4/mathlib library that reconstructs the paper's mathematical
development in explicit finite-dimensional matrix models. It proves reusable results about named
finite registers, subsystem embeddings, Heisenberg evolution, support locality, descriptors,
gates, density states and channels, EPR correlations, teleportation, dephasing, and two
independent finite Bell contradictions.

The paper is not proof input. Every result is derived from definitions, finite matrix algebra, and
explicit hypotheses. The library does not infer philosophical conclusions from descriptor
formulas, state-vector identities, or Bell premises.

The scope is deliberately finite. It is not a formalization of continuum quantum field theory,
an arbitrary spatial-dynamics limit, a communication-capacity theorem, or an ontology.

## Public entry points

Import `Deutsch` for the complete production library. Narrower umbrellas are available when a
downstream development wants fewer dependencies:

| Import | Main API |
| --- | --- |
| `Deutsch.Foundations` | Concrete qubit matrices, tensor/bit conventions, Heisenberg conjugation |
| `Deutsch.Register` | Named finite registers, subsystem embeddings, Pauli operators, pure states |
| `Deutsch.Locality` | Disjoint-support commutation and exact Heisenberg invariance |
| `Deutsch.Descriptor` | Valid descriptor families, evolution, generation, Pauli-word reconstruction |
| `Deutsch.Gates` | NOT, square-root NOT, arbitrary-axis rotations, Hadamard, CNOT, Bell and inverse Bell |
| `Deutsch.Information` | Densities, effects, POVMs, reduction, Kraus channels, dependence and recovery |
| `Deutsch.EPR` | Pair and four-wire circuit descriptors, densities, statistics, and provenance |
| `Deutsch.Teleportation` | Coherent circuit, conditional correction, correctness, protocol, and statistics |
| `Deutsch.Decoherence` | Named dephasing consequences, record errors, EPR stability, correlation boundary |
| `Deutsch.Bell` | All-setting moments, finite assignment inequality, quantum bridge, and contradictions |
| `Deutsch.Paper` | Canonical `equation01`–`equation46` façade over the topical APIs |

The [reuse guide](reuse.md) gives examples compiled against the public root, and the
[paper façade guide](paper.md) maps the numbered sequence to reusable APIs. Topic guides describe
the representation and theorem boundaries in more detail:
[conventions](conventions.md), [representation](representation.md),
[registers](registers.md), [locality](locality.md), [descriptors](descriptors.md),
[gates](gates.md), [information](information.md), [EPR](epr.md),
[teleportation](teleportation.md), [decoherence](decoherence.md), and
[Bell](bell.md).

## Formalized mathematical content

- Arbitrary finite named qubit registers have explicit computational bases, selected-subsystem and
  ordered-injection embeddings, support witnesses, a matrix/endomorphism bridge, and embedded
  Pauli/projector algebra. Normalized pure states admit exact unitary preparation from the fixed
  reference ket.
- Operators supported on disjoint finite subsystems commute. Conjugation by a supported isometry,
  and in particular a physical unitary, fixes a disjoint observable exactly. Expectation
  corollaries quantify over arbitrary kets, including entangled kets.
- Descriptor triples and families have explicit Pauli validity laws, cross-coordinate
  commutation, unitary preservation, complete global matrix-unit generation, and exact
  initial/evolved Pauli-word bases with reconstruction.
- Named and current-descriptor gates have exact unitarity, basis action, chronology, support, and
  Pauli conjugation results. The arbitrary-axis API identifies the actual matrix exponential
  `exp(-i θ n·σ/2)`, proves unitarity, derives the Rodrigues action, and transports the gate and
  axis observable into an arbitrary current Heisenberg frame.
- Density states, effects, finite POVMs, Born bounds and normalization, partial trace, finite
  Kraus channels, channel/effect duality, and selected-subsystem no-signalling are constructive
  public APIs. Local statistics, joint detectability, recovery, descriptor dependence, and
  supplied provenance are separate definitions.
- The EPR layer proves the named four-wire circuit, phase-aware state identities, descriptor
  evolution, maximally mixed singleton reductions, all-effect local independence, exact joint
  probabilities, joint detectability, and equal-final-state/distinct-history examples. Structural
  circuit-to-pair bridges connect the record and final comparison effects to the pair-density
  calculation before the trigonometric evaluation.
- The teleportation layer proves the five-wire coherent chronology, all conditional-correction
  branches, arbitrary-pure-input factorization, receiver-density equality, and the numbered
  observable calculations. A separate uniform-branch encoder/decoder recovers every one-qubit
  density and exposes local inaccessibility, joint detection, necessity examples for the named
  correction operations, and supplied transport metadata.
- Named coordinate dephasing has exact entry action, fixed points, idempotence, basis-state
  stability, complementary-basis disturbance, and a paper-zero CNOT environment realization.
  Record dephasing fixes the semantic teleportation encoder and preserves recovery, while a record
  bit flip makes the unchanged decoder fail.
- `Deutsch.Paper` exposes exactly one source-shaped declaration for each numbered equation. Its
  Equation (40)–(46) route starts with the literal EPR record statistics, derives the Boolean
  moment identities for arbitrary real settings, restricts one model to the three special
  settings, and obtains the final contradiction.
- The independent Bell route proves the three-Boolean pigeonhole inequality for normalized
  nonnegative distributions over deterministic setting-local response tables. The EPR agreement
  probabilities at `0`, `2π/3`, and `4π/3` contradict that finite model; equality on
  positive-weight equal-setting responses is derived from probability one rather than assumed.

## Conventions and proof boundaries

The implementation makes several distinctions explicit:

- The paper labels the `+1` eigenspace of `Z` as logical bit `1`; gate truth tables and outcome
  statements consistently translate between that label and the raw matrix index.
- Heisenberg evolution is `Uᴴ * A * U`. Rotations use
  `R(n,θ)=exp(-i θ n·σ/2)`, so every component identity follows from one convention and the
  arbitrary-axis exponential theorem.
- The conventional Hadamard Bell preparation and source-shaped ket are related by an explicit
  global phase; prediction invariance is proved separately.
- A same-register unitary cannot move an arbitrary mixed density to a fixed pure reference because
  unitary conjugation preserves rank and spectrum. Density Schrödinger/Heisenberg duality is the
  general finite substitute.
- The three named `Z` moments alone do not establish entanglement: an explicit mixture of product
  basis densities has the same moments and nonfactorizing correlation while differing from the
  Bell density.

The library also keeps apart:

- exact operator equality, equality after conjugation, and equality of one-state expectations;
- equality of all local effect statistics, equality of one joint statistic, and equality of
  global densities;
- descriptor nonconstancy, local statistical dependence, joint detectability, decoder recovery,
  and supplied preparation/process history;
- disjoint-support dynamical locality, channel no-signalling, and Bell's counterfactual
  setting-local response assumption;
- coherent record copying, nonselective dephasing, an outcome-conditioned instrument, and an
  observer learning an outcome.

These distinctions appear in theorem statements and hypotheses, not only in prose.

## Explicit limitations and extension paths

- A continuum or general-dynamics extrapolation needs a topology, approximation theorem, error
  bounds, and supported Hamiltonian or channel hypotheses.
- Outcome-conditioned instruments and posterior-state rules require an additional instrument API;
  the present dephasing channels are nonselective.
- The coherent teleportation circuit is proved for arbitrary pure input, but no packaged theorem
  yet treats a circuit input entangled with an arbitrary reference. The separate semantic channel
  is the identity on every one-qubit density, and no theorem equates it with dephasing and
  reduction of the five-wire circuit.
- The Bell assignment theorem is stated for finite deterministic response tables with a
  setting-independent distribution. A fully packaged equivalence with every stochastic
  factorizable presentation is a separate theorem obligation.
- Communication capacities, entanglement necessity, the cited “nonlocality without entanglement”
  task, and philosophical claims about actual outcomes or many worlds are not conclusions of the
  proved finite models.

The original PDF, the canonical Markdown, and all three figures are retained with stable
provenance. For the small historical formula comparison, see
[Printed-form comparison](errata.md).

## Verification and reproducibility

The repository pins Lean and mathlib in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The full verification sequence is:

```bash
lake clean deutsch
lake build
python3 -B goal-1/check_source_audit.py
python3 -B goal-1/check_lean_integrity.py
python3 -B goal-1/check_doc_links.py
```

The checkers verify source-map coverage, the production/test import boundary, the public
declaration registry, exact equation-façade cardinality, principal axiom reports, repository-local
documentation links, and forbidden implementation shortcuts. The accepted foundational axioms
are the standard mathlib set used by this development: `Classical.choice`, `Quot.sound`, and
`propext`.
