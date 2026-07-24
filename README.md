# Deutsch–Hayden Information-Flow Formalization

This repository contains a finite-dimensional Lean 4 formalization of David Deutsch and Patrick
Hayden's *Information Flow in Entangled Quantum Systems*. The `Deutsch` library exposes the
complete numbered presentation through `Deutsch.Paper` and reusable results through topical
modules. The small `DeutschErrata` library is a separate comparison companion; see the
[errata companion](docs/errata.md).

The public foundations pin Lean/mathlib; fix the bit, tensor, Heisenberg, rotation, CNOT, and Bell
conventions; and provide finite named registers with exact subsystem embeddings, support
witnesses, embedded Pauli/projector algebra, pure states, and fixed-reference prediction
equivalence. The locality layer proves exact commutation and Heisenberg invariance for operations
with disjoint finite supports, including arbitrary-ket expectation corollaries. The descriptor
layer supplies valid global Pauli triples, complete cross-label relations, unitary preservation,
constructive generation of the full operator algebra, and explicit initial/evolved Pauli-word
bases.

The gate layer proves exact one-qubit and arbitrary-axis rotations, their current-descriptor
forms, arbitrary-register NOT/CNOT, Bell/inverse-Bell chronology, basis amplitudes, and the
corresponding Pauli maps. The information layer supplies finite density states, effects and POVMs,
partial trace, finite Kraus channels, selected-subsystem no-signalling, one-qubit tomography,
semantic dependence/recovery predicates, and a classical one-time-pad boundary example. Every
finite density also has an explicit positive-square-root purification on a doubled register,
exact reduction to the original density, and an enlarged-unitary fixed-reference representation
for every embedded original-system observable; the same-register mixed-state purity obstruction
remains separate.

The EPR layer implements the four-wire circuit, proves the phase-aware state and descriptor
identities, establishes maximally mixed singleton marginals, and derives the exact joint and
comparison probabilities through both pair-density and literal-record routes. Direct amplitude
and density-matrix proofs show that the actual circuit resource is entangled and non-product at
every pair of local rotation settings. The teleportation layer implements the five-wire coherent
chronology, realizes its physical correction gate, derives the full descriptor chain, and proves
exact arbitrary-input receiver transfer at ket and reduced-density level. Literal matrix slices
of the coherent circuit form a channel whose receiver partial trace is the reindexed identity on
every operator and density and preserves every effect probability; that action agrees pointwise
with the separately constructed decoder-after-encoder. The semantic encoder alone is not
identified with a measurement/dephasing realization of the pre-correction circuit, and no
arbitrary-reference tensor theorem is claimed.

The dephasing layer supplies computational-coordinate Kraus dephasing, a paper-zero CNOT
environment realization, exact repeated-record stability, a record-bit-error failure,
preservation of the bounded EPR comparison statistic, and record-dephasing recovery for the
semantic teleportation encoder. It also constructs a classically correlated separable mixture
showing that the three displayed `Z` moments alone are not an entanglement witness.

The Bell layer derives the all-angle moment laws and the three-setting quantum agreement table,
proves the finite local-assignment inequality, and refutes every normalized nonnegative
distribution over explicit setting-local deterministic response tables that reproduces those
moments. Its strongest theorem derives positive-support equal-setting agreement from the
probability-one predictions; zero-weight tables remain unconstrained. Counterfactual Bell
locality is kept distinct from dynamical support locality and operational no-signalling. A
separate constructive refinement expands finite factorizable stochastic response kernels into
complete deterministic response tables while preserving all marginals and joint outcomes, then
applies the same contradiction under the named finite stochastic assumptions.

See [Global Conventions](docs/conventions.md),
[Representation Decision](docs/representation.md),
[Finite Registers](docs/registers.md), [Finite-Support Locality](docs/locality.md),
[Descriptor Triples](docs/descriptors.md), [Gates and Bell Chronology](docs/gates.md),
[Density States and Information Dependence](docs/information.md),
[EPR Circuit and Correlations](docs/epr.md),
[Coherent Teleportation and Receiver Semantics](docs/teleportation.md),
[Explicit Dephasing and Classical Records](docs/decoherence.md), and
[Finite Bell Moments](docs/bell.md). For downstream use, see
[Reusing the Public Lean API](docs/reuse.md). The
[equation-by-equation paper façade](docs/paper.md) maps all 46 numbered equations to the reusable
topical APIs, and the [Final Project Report](docs/project-report.md) summarizes scope and
verification.

## Build and audit

The repository pins Lean `v4.32.0` and mathlib `v4.32.0`. With `elan` and `lake` available, run:

```bash
lake clean deutsch
lake build
python3 -B goal-1/check_source_audit.py
python3 -B goal-1/check_lean_integrity.py
python3 -B goal-1/check_doc_links.py
python3 -B goal-2/check_errata_boundary.py
```

Focused verification modules can be compiled with:

```bash
lake env lean DeutschTests/Foundations/Concrete.lean
lake env lean DeutschTests/Foundations/Abstract.lean
lake env lean DeutschTests/Foundations/MatrixSemantics.lean
lake env lean DeutschTests/Register.lean
lake env lean DeutschTests/Locality.lean
lake env lean DeutschTests/Descriptor.lean
lake env lean DeutschTests/Gates.lean
lake env lean DeutschTests/Information.lean
lake env lean DeutschTests/EPR.lean
lake env lean DeutschTests/Teleportation.lean
lake env lean DeutschTests/Decoherence.lean
lake env lean DeutschTests/Bell.lean
lake env lean DeutschTests/Paper.lean
lake env lean DeutschTests/Examples.lean
lake env lean DeutschTests/Audit.lean
lake env lean DeutschErrataTests/Audit.lean
```
