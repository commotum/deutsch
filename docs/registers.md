# Finite Registers, Embeddings, and Pure States

The public register layer represents an arbitrary finite family of named qubits. Its core modules
are [register basics](../Deutsch/Register/Basic.lean),
[subsystem embeddings](../Deutsch/Register/Embedding.lean),
[pure states and predictions](../Deutsch/Register/State.lean), and
[embedded Pauli operators](../Deutsch/Register/Pauli.lean). All declarations below are in the
`Deutsch.Register` namespace. The raw-bit and tensor conventions remain those fixed by
[Global Conventions](conventions.md). The theorem layer built from these support witnesses is
documented in [Finite-Support Locality](locality.md).

## Register and Hilbert-space types

A register is indexed by any type `Q` with `Fintype Q` and `DecidableEq Q`; qubits therefore have
names rather than implicit numeric positions. The public types separate four roles:

```lean
Basis Q            = Q → QubitIndex
CoordinateVector Q = Basis Q → ℂ
Ket Q              = EuclideanSpace ℂ (Basis Q)
Operator Q         = Matrix (Basis Q) (Basis Q) ℂ
```

`Basis Q` is the set of raw computational-basis assignments. `card_basis` proves that it has
cardinality `2 ^ Fintype.card Q`. A `CoordinateVector Q` is the underlying coordinate function,
whereas `Ket Q` equips the same finite coordinates with the Hilbert-space structure used for
norms, inner products, and adjoints. `Operator Q` remains an explicit matrix, so finite
calculations and entrywise convention checks stay transparent.

The paper reverses the usual raw bit labels: paper bit `0` is raw `Fin 2` index `1`. Accordingly,
`paperZeroAssignment Q` is the constant assignment `fun _ ↦ 1`, `basisKet` converts a basis
assignment into a Hilbert-space ket, and `referenceKet Q` is the paper's all-zero ket.
`norm_basisKet` and `norm_referenceKet` prove that these kets are normalized.

## The matrix/endomorphism bridge

`matrixEndEquiv Q` is the explicit algebra equivalence

```lean
Operator Q ≃ₐ[ℂ] Module.End ℂ (Ket Q).
```

It is the only identification used between concrete matrices and Hilbert-space endomorphisms.
`matrixEndEquiv_apply` states that its action is matrix-vector multiplication after converting
between `Ket Q` and its coordinate function; `matrixEndEquiv_conjTranspose` states that matrix
conjugate transpose becomes the Hilbert-space adjoint. The state API names this action `act` and
records composition in `act_mul`.

This bridge is not an equivalence between arbitrary abstract tensor-product endomorphisms and a
chosen product-index matrix. Such a tensor-coordinate bridge, including reassociation, remains a
separate obligation.

## Selected subsystems and exact support

For a finite set `s : Finset Q`, `SubsystemBasis s` and `ComplementBasis s` are assignments on
the selected labels and their complement. `splitBasis s` is the explicit equivalence

```lean
Basis Q ≃ SubsystemBasis s × ComplementBasis s.
```

`embedSubsystem s A` reindexes `A ⊗ₖ I` through this split. Its bundled form,
`embedSubsystemAlgHom s`, makes preservation of zero, one, addition, scalar multiplication, and
multiplication available through the named `embedSubsystem_*` theorems. The embedding is
injective and preserves conjugate transpose, Hermiticity, unitarity, and Heisenberg conjugation;
the corresponding declarations are `embedSubsystem_injective`,
`embedSubsystem_conjTranspose`, `embedSubsystem_isHermitian`, `embedSubsystem_unitary`, and
`embedSubsystem_heisenberg`.

`IsSupportedOn s A` means exactly that some `SubsystemOperator s` embeds to `A`. It is support
relative to this chosen tensor factorization, not a claim that `s` is the smallest possible
support. The public closure theorems cover zero, one, addition, scalar multiplication,
multiplication, adjoint, and Heisenberg conjugation when the operands have the same declared
support. `embedQubit q` is the singleton specialization. Its entry theorem
`embedQubit_apply_ite` says that an embedded one-qubit matrix can change coordinate `q` and is
diagonal on every other coordinate.

The Pauli module uses this embedding to define `xAt`, `yAt`, `zAt`,
`paperBitOneProjectorAt`, and `paperBitZeroProjectorAt`. It proves the local Pauli and projector
algebra as full operator equalities. It also proves `embedQubit_commute_of_ne`: arbitrary
one-qubit operators embedded at two different named coordinates commute. The locality layer
generalizes this to arbitrary operators on disjoint finite multi-qubit supports through
`embedSubsystem_commute_of_disjoint` and `supportedOperators_commute_of_disjoint`.

## Ordered placement

A `Finset Q` selects ambient labels but does not remember which input factor goes to which label.
For an operator whose input register is named by `K`, ordered placement instead uses an injection

```lean
p : K ↪ Q.
```

`placementFinset p` is its ambient range, `placementEquiv p` identifies `K` with that range, and
`alongBasisEquiv p` transports `Basis K` without discarding the domain labels. `embedAlong p A`
then places `A : Operator K` in `Operator Q`; its bundled form is `embedAlongAlgHom p`.
`embedAlong_apply_ite` makes the ordering explicit: the local entry is evaluated at
`fun k ↦ x (p k)` and `fun k ↦ y (p k)`, while source and target assignments must agree outside
`Set.range p`.

Thus, when `K = Fin n`, the factor order is the order carried by `Fin n` and the map `p`, not an
iteration order inferred from the range `Finset`. Two injections with the same range can represent
different placements of a nonsymmetric operator. The `embedAlong_*` API proves algebraic laws,
injectivity, adjoint, Hermiticity, unitarity, Heisenberg compatibility, and support on
`placementFinset p`.

## Heisenberg evolution and pure-state predictions

The project direction is

```lean
heisenberg U A = Uᴴ * A * U.
```

This definition accepts any matrix and is useful as an algebraic conjugation expression.
`heisenberg_chronology`, `heisenberg_add`, `heisenberg_conjTranspose`, and
`heisenberg_isHermitian` need no cancellation. Results that do cancel `U` against `Uᴴ` make
unitarity explicit: `heisenberg_one_of_unitary`, `heisenberg_mul_of_unitary`, and
`heisenberg_unitary` each take a unitary-group membership hypothesis. `evolve` is the variant
whose evolution matrix is already bundled as `UnitaryOperator Q`.

`PureState Q` packages a ket with norm one, and `PureState.evolve` requires a unitary hypothesis
to preserve that invariant. Pure-state expectation is

```lean
expectation psi A = ⟪psi, act A psi⟫_ℂ.
```

`expectation_after_action` proves the exact Schrödinger/Heisenberg scalar identity

```text
expectation (act U psi) A = expectation psi (heisenberg U A).
```

This identity itself is algebraic and does not require `U` to be unitary. The specialization
`fixed_reference_prediction` uses `referenceKet Q`. Physical preparation is supplied separately:
`exists_unitary_act_reference` proves that every normalized `psi : Ket Q` is exactly
`act U (referenceKet Q)` for some unitary matrix `U`, and
`PureState.exists_unitary_preparation` packages the same result for `PureState Q`. The proof
extends the target unit vector to an orthonormal basis; it does not assume the desired preparation
matrix. `PureState.exists_fixed_reference_representation` combines preparation and prediction:
for every pure state it supplies one unitary `U`, exact ket equality with the prepared reference,
and the fixed-reference expectation equality for every operator `A`.

`heisenberg_eigenvector` gives the corresponding contravariant eigenvector transport. If
`A v = lambda • v` and `U` is unitary, then `Uᴴ v` is a `lambda`-eigenvector of
`heisenberg U A`. Here unitarity is essential because the proof cancels `U * Uᴴ`.

## Four notions of equality

The development keeps the following claims distinct:

- **Coordinate equality** is equality of `CoordinateVector Q` or `Ket Q` values in the fixed
  computational basis, such as `act U (referenceKet Q) = psi`. It is exact equality, not equality
  merely up to a global phase.
- **Operator equality** is equality of every entry of two `Operator Q` matrices, equivalently of
  their endomorphisms through the injective `matrixEndEquiv Q`. It implies equal expectations for
  every ket, but is much stronger than one observed scalar equality.
- **One-state expectation equality** compares `expectation psi A` with another scalar for one
  fixed state and observable. `expectation_after_action` is such an equality. It does not identify
  two operators and does not determine other observables or states.
- **All-state and joint-distribution equality** go further again. Equality of expectations for all
  states quantifies over every `psi`, not merely one prepared state. Joint-distribution equality
  compares every outcome probability in a complete measurement family, potentially across
  several observables or times. The current pure expectation API proves neither kind of claim
  from one expectation value. The later [information layer](information.md) provides single-time
  finite POVMs and proves that all effect probabilities determine a density; multi-time
  instruments remain outside that result.

No converse between these levels should be used without a separately proved theorem.

## Downstream semantic layer

The register layer deliberately stops before mixed-state and operational measurement semantics.
Those definitions and theorems are now supplied separately by
[Density States, Channels, and Information Dependence](information.md). The arbitrary normalized-
state preparation theorem in this register module remains a pure-state statement and must not be
applied to a mixed density operator; the information layer instead gives trace-density evolution
and an explicit obstruction to same-register mixed-to-pure standardization.

The current API supplies the register algebra, exact embeddings, embedded Pauli/projector facts,
and the matrix/Hilbert bridge. [Finite-Support Locality](locality.md) uses it to prove arbitrary
disjoint-support commutation, unitary Heisenberg invariance, and arbitrary-ket expectation
corollaries. [Descriptor Triples and Algebraic Completeness](descriptors.md) then builds valid
global Pauli triples, exact initial/evolved reconstruction, and full operator-algebra generation.
Reusable named gate/circuit theorems are documented in [Gates and Bell Chronology](gates.md), and
the stronger statistical semantics are documented in the information layer.
