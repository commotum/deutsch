# Deutsch–Hayden Information-Flow Formalization

This repository contains a Lean 4 reconstruction and audit of David Deutsch and Patrick
Hayden's *Information Flow in Entangled Quantum Systems*. The paper is treated as a source of
obligations, not as trusted proof input.

The current public layers pin Lean/mathlib; fix the project's bit, tensor, Heisenberg, rotation,
CNOT, and Bell conventions; and provide finite named registers with exact subsystem embeddings,
support witnesses, embedded Pauli/projector algebra, pure states, and fixed-reference prediction
equivalence. They also prove exact commutation and Heisenberg invariance for operations with
disjoint finite supports, with arbitrary-ket expectation corollaries. The descriptor layer adds
valid global Pauli triples, complete cross-label relations, unitary preservation, constructive
generation of the full operator algebra, and explicit initial/evolved Pauli-word bases. The gate
layer adds exact one-qubit rotations, current-descriptor NOT/CNOT, arbitrary-register
CNOT, Bell/inverse Bell chronology, basis amplitudes, and all corresponding Pauli maps. The
information layer adds finite density states, effects and POVMs, partial trace, finite Kraus
channels, selected-subsystem no-signalling, one-qubit tomography, semantic dependence/recovery
predicates, and a classical one-time-pad boundary example. The EPR layer fixes the four-wire
circuit, proves phase-aware state and corrected descriptor
identities, establishes maximally mixed singleton marginals and exact joint probabilities, and
compiles counterexamples to the source's complementary Equations (28) and (41), including the
unnumbered non-product resource-correlation witness. The teleportation
layer fixes the five-wire coherent chronology, realizes the correction gate explicitly, compiles
the propagated descriptor-sign corrections, and proves exact arbitrary-input receiver transfer
at ket and reduced-density level. A separately scoped uniform-branch semantic model supplies an
operational encoder/decoder recovery theorem; a circuit-to-dephasing bridge is deferred.
The explicit-decoherence layer now supplies computational-coordinate Kraus dephasing, a named
paper-zero CNOT environment realization, exact repeated-record stability, a real record-bit-error
failure, preservation of the bounded EPR comparison statistic, and record-dephasing recovery for
the semantic teleportation encoder. It also compiles a classically correlated separable mixture
showing that the source's three Z moments alone are not an entanglement witness. The stronger
five-wire coherent-state-to-semantic-encoder identification remains a documented API boundary.
The corrected finite Bell layer derives the three-setting quantum agreement table, proves the
finite local-assignment inequality, and refutes every normalized nonnegative distribution over
the explicit setting-local deterministic response tables that reproduces that table. Its strongest
theorem derives positive-support equal-setting agreement from the probability-one predictions;
zero-weight tables remain unconstrained, and this counterfactual Bell locality is kept distinct
from dynamical support locality and operational no-signalling.
See
[Global Conventions](docs/conventions.md),
[Representation Decision](docs/representation.md),
[Finite Registers](docs/registers.md), [Finite-Support Locality](docs/locality.md),
[Descriptor Triples](docs/descriptors.md), [Gates and Bell Chronology](docs/gates.md),
[Density States and Information Dependence](docs/information.md),
[EPR Circuit and Corrected Correlations](docs/epr.md),
[Coherent Teleportation and Receiver Semantics](docs/teleportation.md),
[Explicit Dephasing and Classical Records](docs/decoherence.md), and
[Corrected Finite Bell Audit](docs/bell.md). For a compact downstream-oriented entry point, see
[Reusing the Public Lean API](docs/reuse.md); the end-to-end scope, corrections, limits, and audit
results are summarized in the [Final Project Report](docs/project-report.md).

## Build and audit

The repository pins Lean `v4.32.0` and mathlib `v4.32.0`. With `elan` and `lake` available, run:

```bash
lake clean deutsch
lake build
python3 -B goal-1/check_source_audit.py
python3 -B goal-1/check_lean_integrity.py
python3 -B goal-1/check_doc_links.py
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
lake env lean DeutschTests/Examples.lean
lake env lean DeutschTests/Audit.lean
```

The staged implementation and verification record is in [`goal-1`](goal-1/0-plan.md).
