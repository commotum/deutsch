# 9-ANALYSIS

## Status

- Complete.

## Current Facts

- `Deutsch.Register.PureState.exists_fixed_reference_representation` proves fixed-reference
  Heisenberg representation for every normalized pure register ket.
- `Deutsch.Information.maximallyMixedQubit_cannot_evolve_to_reference` proves the complementary
  same-register boundary: unitary conjugation cannot turn a mixed density into the pure reference
  density because purity is invariant.
- The library has exact finite density operators, positive semidefiniteness, arbitrary subsystem
  reduction, pure-density construction, and fixed-reference unitary preparation, but it does not
  yet combine them into a compiled enlarged-register purification theorem for arbitrary density
  states.
- `Deutsch.EPR.pairDensity theta phi` is the actual two-qubit resource produced by the paper
  circuit. Both singleton reductions are maximally mixed, and several nonfactorizing correlations
  are known, but no production predicate/theorem yet states that this resource is not a product
  density.
- `Deutsch.Teleportation.coherentProtocol_factorizes` proves the literal five-wire circuit on every
  one-qubit amplitude pair; `teleportedDensity_reduce_receiver` gives exact receiver density for
  normalized pure inputs.
- Separately, `protocolDecoder_encoder_mapOperator` and
  `protocolDecoder_encoder_mapDensity` prove that a semantic finite Kraus encoder/decoder is the
  identity on every one-qubit operator/density. No compiled theorem currently identifies a channel
  derived from the literal coherent circuit with that identity action.

## Updated Assumptions

- A canonical finite purification should be constructible on two copies of the qubit-label
  register by vectorizing the positive square root of the density operator. Its norm follows from
  trace one, and tracing out the copied register returns the original density.
- Once that enlarged pure state is built, the existing pure-state unitary-preparation theorem
  should supply a fixed-reference unitary and Heisenberg prediction representation without
  contradicting the same-register purity obstruction.
- A reusable product-density predicate should be defined at the density-operator level with the
  basis split made explicit. The actual EPR resource can then be refuted as product using exact
  matrix entries or a theorem that a product pure state cannot have its proven maximally mixed
  marginal.
- A literal coherent teleportation channel can be obtained by initializing the four ancillary
  wires, applying `coherentProtocol`, and reducing to `q5`. Equality on all one-qubit matrix units
  is sufficient to prove equality on every operator and density.
- If an arbitrary-reference theorem follows cleanly from the exact operator identity/tensor
  construction, include it. Do not claim it merely from pure-state tests or from the separate
  semantic channel.

## Big Picture Objective

- Close the three supporting analysis gaps: arbitrary finite mixed states receive an exact
  enlarged-system fixed-reference representation; the actual EPR resource is formally non-product;
  and the literal coherent teleportation circuit induces the identity channel rather than merely
  agreeing with a separately defined semantic channel on nearby examples.

## Detailed Implementation Plan

- Add an Information purification module:
  - define the doubled register and selected original subsystem;
  - construct the vectorized positive-square-root purification of an arbitrary density;
  - prove normalization and exact reduction to the supplied density;
  - obtain a fixed-reference unitary preparation on the enlarged register;
  - state all-observable Heisenberg prediction equality for observables embedded from the original
    subsystem; and
  - retain the explicit same-register mixed-state obstruction.
- Add a generic EPR product/non-product layer:
  - define product kets/operators/densities under an explicit register split;
  - prove the actual `pairDensity` resource (at least its resource-preparation setting, preferably
    every local-rotation setting) is not product;
  - tie the result to the exact circuit-produced density, not only to an abstract correlation
    table.
- Add a coherent teleportation channel bridge:
  - define the input/output register equivalence and the channel induced by ancillary
    initialization, literal `coherentProtocol`, and receiver reduction;
  - prove its operator action is the reindexed identity for every one-qubit operator;
  - derive every-density and every-effect preservation;
  - identify it with the existing semantic decoder/encoder identity action; and
  - prove an arbitrary finite reference extension if the literal matrix/tensor infrastructure
    supports a direct derivation.
- Add focused tests, exact axiom targets, integrity requirements, and precise documentation for
  each result.

## No-Cheating Checks

- The purification reduction theorem must unfold an explicit enlarged pure state; an existential
  premise saying “assume a purification” does not count.
- The fixed-reference theorem must use a unitary on the enlarged register and must not assert that
  a same-register unitary changes density rank or purity.
- The EPR theorem must reject an explicitly defined product-density decomposition of
  `pairDensity` itself. A correlation inequality without a bridge to product densities does not
  count.
- The teleportation channel must contain the literal `coherentProtocol` matrix in its construction.
  A restatement of `protocolDecoder_encoder_mapOperator` under a new name does not count.
- Prove operator/density equality, not only three Bloch moments, one rank-one effect, or the
  parameterized real great-circle input family.
- Any arbitrary-reference statement must be a compiled tensor/channel equality. Do not infer it
  verbally from ordinary identity-channel behavior.
- Audit for proof holes, project axioms, unsafe/opaque escapes, and unexpected foundational
  dependencies.

## Completion Requirements

- Every finite density has a compiled explicit purification on an enlarged register, exact
  reduction to the original system, unitary preparation from the enlarged fixed reference, and
  an appropriately scoped Heisenberg prediction theorem.
- The same-register purity obstruction remains compiled and documented beside the enlarged-system
  result.
- The actual EPR circuit resource has a compiled non-product/entanglement theorem against a clear
  product-density definition.
- A channel explicitly constructed from the literal coherent teleportation circuit acts as the
  reindexed identity on every one-qubit operator and density and is connected to the semantic
  encoder/decoder result.
- Any advertised arbitrary-reference guarantee is directly proved; otherwise the limitation
  remains explicit.
- Focused tests, all four targets, both axiom audits, integrity/boundary/source/doc checks,
  whitespace, and `git diff --check` pass.

## Stage Results

- Added `Deutsch/Information/Purification.lean` and exported it through
  `Deutsch.Information`.  For every finite `Density Q`, the module:
  - vectorizes the positive CFC square root on `Sum Q Q`;
  - proves the resulting ket has norm one;
  - proves the standard partial trace over the second copy is the supplied density, first with
    explicit retained labels and then reindexed literally back to `Q`;
  - proves equality of expectations for every original-system operator embedded on the first
    copy; and
  - obtains an actual unitary on the doubled register whose fixed-reference Heisenberg predictions
    agree for every embedded operator.
  The existing maximally mixed same-register purity obstruction remains compiled and is presented
  beside the enlarged construction.
- Added `Deutsch/EPR/Entanglement.lean` and exported it through `Deutsch.EPR`.  The module defines
  explicit product-ket, product-operator, and product-density predicates for the two coordinates
  of `Fin 2`.  It computes the exact circuit ket's amplitude determinant as `-1/2` for every
  `theta` and `phi`, proves the normalized ket is entangled at every setting, and directly refutes
  a tensor product of two genuine one-qubit densities for the actual `pairDensity theta phi`.
  The density proof uses exact matrix entries and the zero-minor condition forced by a product
  operator, not the separate three-moment correlation witness.
- Added `Deutsch/Teleportation/ChannelBridge.lean` and exported it through
  `Deutsch.Teleportation`.  Each Kraus entry is a literal matrix slice of `coherentProtocol` with
  `q1` carrying the message, `q2`--`q5` initialized to raw `1` (paper zero), `q1`--`q4` discarded,
  and `q5` retained.  The compiled results prove:
  - Kraus completeness from the normalized, input-independent junk state;
  - the canonical receiver reindex on every operator and density;
  - preservation of every transported message effect and equality for every physical receiver
    effect;
  - equality with the partial trace of an explicitly initialized and coherently evolved
    five-wire operator; and
  - pointwise agreement with the independently defined semantic decoder-after-encoder action.
- No arbitrary-reference tensor-extension theorem was added.  Ordinary all-operator identity
  action does not by itself satisfy the stage's direct tensor-equality requirement, so
  `docs/teleportation.md` and `docs/project-report.md` state this limitation explicitly.
- Added seven focused Information wrappers, five EPR product/entanglement wrappers, eight literal
  teleportation-channel wrappers, and exact production axiom targets.  The integrity verifier now
  requires all three module paths and import edges, all focused wrappers, 29 purification
  declarations, 15 EPR product/entanglement declarations, and 27 channel-bridge declarations.
- Updated `docs/information.md`, `docs/epr.md`, `docs/teleportation.md`, and
  `docs/project-report.md`.  No canonical-paper source prose or equation was changed in this stage.
- Focused verification passed:
  - `lake build Deutsch.Information.Purification DeutschTests.Information` (3252 jobs);
  - `lake build Deutsch.EPR.Entanglement DeutschTests.EPR` (2724 jobs); and
  - `lake build Deutsch.Teleportation.ChannelBridge DeutschTests.Teleportation` (2725 jobs).
- The stage-boundary command
  `lake build Deutsch DeutschTests DeutschErrata DeutschErrataTests` passed with 3341 jobs.
- `python3 goal-1/check_lean_integrity.py` passed over 91 Lean sources and 595 representative axiom
  reports.  It found no proof hole, project axiom, unsafe/opaque escape, verification import,
  reverse Errata import, editorial-history production language, superseded name, or compatibility
  alias.  The only observed dependency axioms were `Classical.choice`, `Quot.sound`, and
  `propext`.
- Both `lake env lean DeutschTests/Audit.lean` and
  `lake env lean DeutschErrataTests/Audit.lean` passed with only the accepted foundations.
  `python3 goal-2/check_errata_boundary.py`, `python3 goal-1/check_source_audit.py`,
  `python3 goal-1/check_doc_links.py`, and `git diff --check` also passed.  The documentation audit
  checked 16 public Markdown files and 129 repository-local links.
- Two independent read-only cross-reviews found no mathematical or no-cheating defect:
  - the purification review checked square-root orientation, normalization, subsystem/complement
    labels, partial trace, reindexing, all-operator expectations, and enlarged unitary scope; and
  - the teleportation review checked the paper-zero convention, wire ordering, literal matrix
    provenance, Kraus completeness, every-operator/density/effect statements, receiver partial
    trace, semantic dependency direction, and the absent arbitrary-reference claim.
- Stage 9 therefore closes all three required supporting gaps at the strongest scope actually
  compiled.  The only intentionally unadvertised strengthening is arbitrary-reference
  teleportation, which is not required for the proved one-qubit identity-channel contract and
  remains stated as a limitation rather than inferred.
