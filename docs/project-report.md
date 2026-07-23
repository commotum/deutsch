# Final project report

## Result and scope

The project is a pinned Lean 4/mathlib library that reconstructs the paper's mathematically precise
content in finite-dimensional matrix models. It proves reusable results about named finite
registers, subsystem embeddings, Heisenberg evolution, support locality, descriptors, gates,
density states and channels, EPR correlations, teleportation, explicit dephasing, and a corrected
finite Bell contradiction.

The paper is not used as proof input. Each numbered equation, additional inline/displayed
mathematical item, figure, definition, major prose claim, and interpretation group has a lifecycle entry in the
[source audit](../goal-1/1-SOURCE-AUDIT.md). False or convention-inconsistent formulas are replaced
by independently proved statements, and philosophical conclusions remain outside theorem
conclusions unless represented by an explicit mathematical predicate.

The result is deliberately finite. It is not a formalization of continuum quantum field theory,
an arbitrary spatial dynamics limit, a communication-capacity theorem, or an ontology.

## Public entry points

Import `Deutsch` for the complete production library. Narrower umbrellas are available when a
downstream project wants fewer dependencies:

| Import | Main API |
| --- | --- |
| `Deutsch.Foundations` | Concrete qubit matrices, tensor/bit conventions, Heisenberg conjugation |
| `Deutsch.Register` | Named finite registers, subsystem embeddings, Pauli operators, pure states |
| `Deutsch.Locality` | Disjoint-support commutation and exact Heisenberg invariance |
| `Deutsch.Descriptor` | Valid descriptor families, evolution, generation, Pauli-word reconstruction |
| `Deutsch.Gates` | NOT, square-root NOT, rotations, Hadamard, CNOT, Bell and inverse Bell |
| `Deutsch.Information` | Densities, effects, POVMs, reduction, Kraus channels, dependence and recovery |
| `Deutsch.EPR` | Corrected pair/circuit descriptors, densities, statistics, and provenance |
| `Deutsch.Teleportation` | Coherent circuit, correction, correctness, semantic protocol, statistics |
| `Deutsch.Decoherence` | Named dephasing consequences, record errors, EPR stability, correlation boundary |
| `Deutsch.Bell` | Source correction, finite inequality, corrected quantum bridge, contradiction |
| `Deutsch.Paper` | Canonical `equation01`–`equation46` façade over the topical APIs |

The [reuse guide](reuse.md) points to examples compiled against the public root, and the
[paper façade guide](paper.md) maps the numbered sequence to those reusable APIs. The topic guides
give the representation and theorem boundaries in more detail:
[conventions](conventions.md), [representation](representation.md),
[registers](registers.md), [locality](locality.md), [descriptors](descriptors.md),
[gates](gates.md), [information](information.md), [EPR](epr.md),
[teleportation](teleportation.md), [decoherence](decoherence.md), and [Bell](bell.md).

## Formalized mathematical content

- Arbitrary finite named qubit registers have explicit computational bases, selected-subsystem and
  ordered-injection embeddings, support witnesses, a matrix/endomorphism bridge, and embedded
  Pauli/projector algebra. Normalized pure states admit exact unitary preparation from the fixed
  reference ket.
- Operators supported on disjoint finite subsystems commute. Conjugation by a supported isometry,
  and in particular a physical unitary, fixes a disjoint observable exactly. The expectation
  corollaries quantify over arbitrary kets, including a compiled non-product Bell ket.
- Descriptor triples/families have explicit Pauli validity laws, cross-coordinate commutation,
  unitary preservation, complete global matrix-unit generation, and exact initial/evolved
  Pauli-word bases with reconstruction.
- Named and current-descriptor gates have exact unitarity, basis action, chronology, support, and
  Pauli conjugation results. Target/control and the paper's reversed logical-bit convention are
  fixed by executable tests.
- Density states, effects, finite POVMs, Born bounds and normalization, partial trace, finite Kraus
  channels, channel/effect duality, and selected-subsystem no-signalling are constructive public
  APIs. Local statistics, joint detectability, recovery, descriptor dependence, and supplied
  provenance are separate definitions.
- The EPR layer proves the named four-wire circuit, phase-aware state identities, corrected
  descriptors, maximally mixed singleton reductions, all-effect local independence, exact joint
  probabilities, joint detectability, and equal-final-state/distinct-history examples.
- The teleportation layer proves the five-wire coherent chronology, all correction branches,
  arbitrary-pure-input factorization, receiver-density equality, and corrected observable
  calculations. A separate uniform-branch encoder/decoder recovers every one-qubit density and
  exposes local inaccessibility, joint detection, correction necessity examples, and supplied
  transport metadata.
- Named coordinate dephasing has exact entry action, fixed points, idempotence, basis-state
  stability, complementary-basis disturbance, and a paper-zero CNOT environment realization.
  Record dephasing fixes the semantic teleportation encoder and preserves recovery, while a real
  record-bit flip makes the unchanged decoder fail.
- The corrected Bell layer proves the three-Boolean pigeonhole inequality for normalized
  nonnegative distributions over deterministic setting-local response tables. The corrected EPR
  agreement probabilities at `0,2π/3,4π/3` contradict that finite model; equality on
  positive-weight equal-setting responses is derived from probability one rather than assumed.

## Source corrections and boundary checks

The main compiled corrections are:

- The paper labels the `+1` eigenvalue of `Z` as logical bit `1`, the reverse of the usual raw
  matrix index. Every CNOT and outcome statement uses this convention explicitly.
- Under `R_x(theta)=cos(theta/2)I-i sin(theta/2)X` and `U† A U`, the correct rotation is
  `Y ↦ cos(theta)Y-sin(theta)Z` and `Z ↦ sin(theta)Y+cos(theta)Z`. Equation (18) has both
  sine signs reversed, and that error propagates into several later descriptor displays. The
  library compiles corrected forms and special-angle inequality witnesses.
- The conventional Hadamard Bell preparation agrees with the source's displayed EPR ket only up
  to the explicit phase `-i`; the phase-aware equality is proved rather than discarded silently.
- The corrected EPR outcome law is
  `P(different)=sin²((theta-phi)/2)`, while
  `P(both paper-one)=1/2 cos²((theta-phi)/2)`. The source's Equations (28) and (41) use
  complementary events unless Bob is explicitly relabeled.
- Teleportation Equations (29), (31), (32), (34), (35), (36), and (37) inherit or expose rotation
  sign issues. Corrected density, all-effect, purity, and full-circuit verification theorems are
  independently compiled, so success does not depend on the false printed operator formula.
- Equation (45) is false at `(a₀,a₁,a₂)=(1,0,1)`, where its two sides are `1` and `2`.
  The corrected complementary partition is truth-table verified, but the production Bell proof
  uses an independent pigeonhole lemma.
- A same-register unitary cannot move an arbitrary mixed density to the fixed pure reference;
  purity gives a compiled maximally-mixed counterexample. Density Schrödinger/Heisenberg duality
  is the valid general substitute.
- The source's three named `Z` moments do not witness entanglement: an explicit mixture of product
  basis densities has the same moments and nonfactorizing correlation while differing from the
  Bell density.

## Information and locality distinctions

The library intentionally does not collapse the following notions:

- exact operator equality, equality after one conjugation, and equality of one-state expectations;
- equality of all local effect statistics, equality of a selected joint statistic, and equality of
  global densities;
- descriptor nonconstancy, local statistical dependence, joint detectability, decoder recovery,
  and supplied preparation/process history;
- disjoint-support dynamical locality, channel no-signalling, and Bell's counterfactual
  setting-local response assumption;
- coherent record copying, nonselective dephasing, an outcome-conditioned instrument, and an
  observer learning an outcome.

These distinctions are reflected in types and theorem hypotheses, not just prose.

## Explicit limitations and next work

The following items remain outside the proved scope and are recorded as partial, excluded, or
unresolved in the source audit:

- A continuum or general-dynamics extrapolation needs a topology, an approximation theorem, error
  bounds, and supported Hamiltonian/channel hypotheses.
- Arbitrary-axis matrix-exponential rotations and CNOT-plus-rotations universality were not needed
  for the finite circuit identities and have no public proof here.
- Outcome-conditioned instruments and posterior-state rules require an additional instrument API;
  the current dephasing channels are nonselective.
- The coherent teleportation circuit is proved for arbitrary pure input, but no explicit
  arbitrary-entangled-reference circuit theorem is packaged. The separate semantic channel is the
  identity on every one-qubit density, and no theorem identifies it with dephasing and reduction of
  the coherent five-wire circuit.
- The Bell result is for finite deterministic response tables with a setting-independent
  distribution. Extending it to every stochastic factorizable model requires a formal refinement
  theorem, for example by adjoining finite local random seeds; continuum settings would require
  measure theory.
- Communication capacities, entanglement necessity, the cited “nonlocality without entanglement”
  task, and philosophical claims about actual outcomes or many worlds are not inferred from the
  proved finite examples.
- The repository contains the original PDF, the canonical corrected Markdown, and all three
  figures. The PDF and an independently prepared verified transcription have been compared with
  the canonical edition; stable hashes guard the PDF and figures, and intentional differences are
  disclosed by the edition's editorial note.

These are bounded extension paths, not hidden premises of completed theorems.

## Verification and reproducibility

The repository pins Lean and mathlib in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The documented verification sequence is:

```bash
lake clean deutsch
lake build
python3 -B goal-1/check_source_audit.py
python3 -B goal-1/check_lean_integrity.py
python3 -B goal-1/check_doc_links.py
```

The final audit records the cleaned-build job count, source/example counts, ordered principal
axiom-report count, accepted foundational axioms, source-map cardinalities, documentation links,
and whitespace/diff checks in [Stage 12](../goal-1/12-LIBRARY-AUDIT.md). `lake clean deutsch`
removes only the `deutsch` package's generated project build outputs; it does not alter sources,
dependency builds, or the pinned dependency manifest.

Final verification on 2026-07-16 produced:

- a clean default build of 3309 jobs;
- 65 scanned Lean sources, ten public-root umbrellas, 49 locked production import edges, 15
  verification-root imports, and seven compiled reuse examples;
- 402 ordered principal axiom reports, with only `Classical.choice`, `Quot.sound`, and `propext`;
- complete source coverage with zero `Planned` lifecycle entries;
- 14 required public Markdown documents and 118 valid repository-local links; and
- identical SHA-256 manifests for all 110 non-generated files, plus identical worktree status,
  before and after the clean build.

The focused examples, source/integrity/documentation checkers, forbidden construct scan,
production/test import boundary, trailing-whitespace scan, and `git diff --check` all pass.
