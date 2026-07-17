# Representation Decision

## Decision

The foundations select a hybrid architecture.

- Concrete finite complex matrices are the public executable convention layer and the calculation
  kernel for explicit gates and small circuits.
- Finite-dimensional complex endomorphisms are the selected Hilbert-space route for reusable
  tensor-locality and measurement semantics. The public register layer now bridges its concrete
  matrices to endomorphisms; the public information layer builds density, measurement, reduction,
  and channel semantics directly on the concrete matrices.
- Bridges between these layers must be explicit theorems. No result may silently identify a
  product-index matrix with an abstract tensor endomorphism.

The convention kernel is
[`Deutsch.Foundations.Concrete`](../Deutsch/Foundations/Concrete.lean). Public finite-register
matrices, their Hilbert-space bridge, subsystem embeddings, and pure-state predictions are
described in [Finite Registers, Embeddings, and Pure States](registers.md). Exact commutation and
Heisenberg invariance for disjoint finite supports are described in
[Finite-Support Locality](locality.md). The abstract density and measurement types described below
remain probes under `DeutschTests.*`; the supported concrete API is documented in
[Density States, Channels, and Information Dependence](information.md).

## Concrete matrix layer

One-qubit operators use `Matrix (Fin 2) (Fin 2) ℂ`; two-qubit operators use product row and
column indices. This representation makes entries, basis action, Kronecker order, conjugate
transpose, and exact circuit composition directly executable. The convention suite proves Pauli
relations, unitary and Hermitian probes, all selected-factor `X` actions, CNOT basis and generator
actions, a rotation sign check, and two-sided Bell/inverse composition. See
[Global Conventions](conventions.md) for the exact statements.

[`DeutschTests.Foundations.MatrixSemantics`](../DeutschTests/Foundations/MatrixSemantics.lean)
compiles a second concrete probe:

- `Density` bundles `Matrix.PosSemidef` and mathlib's unnormalized trace equal to one.
- `Effect` requires positivity of `E` and `I - E`.
- `FiniteMeasurement` is a finite effect family whose matrix sum is the identity.
- `bornWeights_normalize` and `bornProbabilities_normalize` prove normalization from completeness.
- `maximallyMixed` is the explicit diagonal density `diag(1/2, 1/2)`.
- The two computational effects are proved valid and each has Born probability `1/2` in that
  mixed state; their explicit sum is one.

This demonstrates that mixed states are matrices, not vectors, and that the trace API is usable.
This Stage 2 example does not itself prove rank two or non-purity; the later public information
layer proves an exact maximally-mixed purity obstruction.

## Abstract finite-Hilbert probe

[`DeutschTests.Foundations.Abstract`](../DeutschTests/Foundations/Abstract.lean) compiles with
finite-dimensional complex inner-product spaces and uses

```lean
Operator H = Module.End ℂ H.
```

Its verification-only API contains:

- a positive trace-one `Density`;
- an `Effect` satisfying `0 ≤ E ≤ 1`;
- `probability ρ E = re (trace (ρE))`;
- `pureDensity`, constructed from a normalized vector via a rank-one operator;
- `FiniteMeasurement`, a finite effect family summing to the identity;
- `sum_probability_eq_one`, proving normalization for any such family;
- `tensor_adjoint` for abstract tensor maps;
- `disjoint_binary_operators_commute` and `binary_locality_api_probe`.

In the binary locality probe, `A.rTensor K` acts on the first factor and `B.lTensor H` on the
second. The matrix analogue `disjoint_matrix_operators_commute` compiles too. This is evidence that
the abstract layer makes binary tensor locality concise; it is not yet a coordinate bridge
between the two representations. The public finite-register theorem now proves the corresponding
arbitrary-`Finset` result directly from the concrete subsystem embeddings.

## Mixed states and Born-rule limits

Mixed states are positive trace-one operators. `pureDensity` is a separate constructor; the
development does not assume that unitary conjugation can turn an arbitrary mixed density into a
fixed pure reference state. The public theorem
`maximallyMixedQubit_cannot_evolve_to_reference` now makes that boundary executable using unitary
invariance of purity.

Both probes take the real part of `trace (ρE)` for the real-valued presentation. Stage 2 proves
finite-family normalization and an explicit valid example, but it does not yet prove in general
that every weight is real and lies in `[0,1]`. Positivity of `ρ` and `E` does not make the product
`ρE` positive semidefinite in the matrix order. The public information layer closes this
obligation with a cyclic-trace factorization proof and exports stable POVM, partial-trace, and
finite Kraus-channel APIs.

## Alternatives considered

Matrices alone were rejected as the final architecture. They are excellent for finite
calculation, but basis choices, tensor reassociation, and arbitrary or nonadjacent subsystem
embeddings would otherwise pervade semantic theorems.

An abstract-endomorphism-only kernel was also rejected. Explicit gate entries, raw basis order,
and sign-sensitive finite calculations become less transparent, which weakens the independent
convention checks required by the source audit.

Continuous-linear-map wrappers, bundled quantum channels/POVMs, partial traces, and probability
monads were not selected in Stage 2. The pinned mathlib release supplies the required primitive
linear algebra but no single built-in density/effect/channel stack that removes the outstanding
proof obligations. Adding a heavier abstraction before a downstream theorem requires it would
hide rather than resolve those choices.

## Migration risks and bridge obligations

- `matrixEndEquiv` now identifies register matrices with endomorphisms of the corresponding
  computational-basis Hilbert space. There is still no proved coordinate equivalence between
  arbitrary abstract tensor-product endomorphisms and product-index matrices.
- Finite-set subsystem embedding, nonadjacent named support, ordered injection placement, and
  register-wide basis cardinality are public. Arbitrary disjoint finite supports now have a public
  commutation and unitary Heisenberg-invariance API. Abstract tensor reassociation remains a
  downstream obligation.
- The abstract `Density`, `Effect`, `FiniteMeasurement`, and `probability` are test-only.
- General Born-weight reality and `[0,1]` bounds, POVM outcome distributions, channels, and partial
  traces are now public in `Deutsch.Information`; instruments and conditioned state updates remain
  downstream.
- Pair indices flatten as raw `00,01,10,11`, while the paper-labelled basis is `11,10,01,00`.
  Any future `Fin 4` or bit-vector representation must prove that reindexing explicitly.
- `heisenberg` is unbundled matrix algebra; physical evolution requires separately proved
  unitarity.
- Multi-qubit code must not confuse local tensor operands with descriptors already embedded in a
  global algebra, the ambiguity identified around paper equation (15).

## Module and namespace policy

- Reusable public code lives under `Deutsch.*`; verification code lives under `DeutschTests.*`.
- Public modules do not import the umbrella `Mathlib.Tactic`. Verification modules may use heavy
  tactics; the explicit finite Pauli calculation module imports only the narrow tactics it needs.
- Foundation definitions live in `Deutsch.Foundations`; public registers, embeddings, and pure
  states live in `Deutsch.Register`; finite supported-operation locality lives in
  `Deutsch.Locality`; descriptor triples, completeness, and comparison relations live in
  `Deutsch.Descriptor`; stable density operators, effects, measurements, reductions, channels, and
  semantic dependence predicates live in `Deutsch.Information`.
- Convention tests may unfold explicit matrices. Later reusable modules should depend on named
  lemmas rather than repeating entrywise proofs.
- New principal public theorems must be added to the representative axiom audit.

## Reproducibility

From the repository root:

```bash
lake env lean DeutschTests/Foundations/Concrete.lean
lake env lean DeutschTests/Foundations/Abstract.lean
lake env lean DeutschTests/Foundations/MatrixSemantics.lean
lake env lean DeutschTests/Register.lean
lake env lean DeutschTests/Locality.lean
lake env lean DeutschTests/Descriptor.lean
lake env lean DeutschTests/Information.lean
lake build
python3 -B goal-1/check_lean_integrity.py
```

The pinned versions and exact resolved dependency commit are checked by the integrity script.
