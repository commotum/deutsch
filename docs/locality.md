# Finite-Support Locality

The public locality layer proves an exact theorem about operators on finite named-qubit registers:
operators with disjoint declared supports commute, and a unitary supported on one finite subsystem
fixes every observable supported on a disjoint subsystem under Heisenberg evolution. The reusable
modules are [disjoint-support algebra](../Deutsch/Locality/Basic.lean) and
[Heisenberg locality](../Deutsch/Locality/Heisenberg.lean), both in the `Deutsch.Locality`
namespace. The focused positive and negative regressions are in
[`DeutschTests.Locality`](../DeutschTests/Locality.lean).

The support predicate and embeddings used here are documented in
[Finite Registers, Embeddings, and Pure States](registers.md). In particular,
`IsSupportedOn s A` is an exact witness that `A` is an operator on `s` tensored with the identity
on its complement. It does not assert that `s` is the smallest possible support.

## Arbitrary finite supports commute

For arbitrary `s t : Finset Q`, `embedSubsystem_mul_embedSubsystem_apply_of_disjoint` computes
each entry of

```lean
embedSubsystem s A * embedSubsystem t B
```

when `Disjoint s t`. The proof sums through the unique intermediate basis assignment compatible
with the two local actions. `embedSubsystem_commute_of_disjoint` then proves the full operator
equality

```lean
embedSubsystem s A * embedSubsystem t B =
  embedSubsystem t B * embedSubsystem s A.
```

This is not restricted to singleton coordinates, adjacent labels, Pauli matrices, or product
operators within the selected subsystems. `supportedOperators_commute_of_disjoint` eliminates the
two embedding witnesses and exposes the semantic form: any global operators with disjoint
`IsSupportedOn` witnesses commute. Commutation is purely algebraic; it needs neither unitarity nor
a state hypothesis.

The focused tests instantiate the result on the nonadjacent multi-label supports `{0, 2}` and
`{1, 4}` in a five-qubit register. They also cover empty support. An operator embedded from the
empty subsystem commutes with every disjoint supported operator, and
`nonzero_scalar_has_empty_support` records that a nonzero scalar multiple of the identity can have
empty declared support.

## From commutation to Heisenberg invariance

The project convention is `heisenberg U A = Uᴴ * A * U`. Commutation alone does not cancel the
two copies of `U`. `heisenberg_eq_gram_mul_of_commute` states the exact nonunitary result:

```lean
U * A = A * U  ->  heisenberg U A = (Uᴴ * U) * A.
```

Thus the Gram factor `Uᴴ * U` remains for a general matrix. The algebraic cancellation theorem
`heisenberg_eq_self_of_commute_of_isometry` consumes precisely the one-sided isometry identity
`Uᴴ * U = 1`. Its support-aware version is
`heisenberg_eq_self_of_disjoint_support_of_isometry`.

Physical finite-register evolution is stated with an explicit unitary-group hypothesis.
`heisenberg_eq_self_of_disjoint_support` proves

```lean
Disjoint s t ->
U ∈ Matrix.unitaryGroup (Basis Q) ℂ ->
IsSupportedOn s U ->
IsSupportedOn t A ->
heisenberg U A = A.
```

`evolve_eq_self_of_disjoint_support` is the corresponding theorem for a bundled
`UnitaryOperator Q`. The unitary theorem derives the needed `Uᴴ * U = 1` identity and then uses
the isometry theorem; unitarity is not hidden in the definition of `heisenberg`.

## Operator equality first, predictions second

The locality proof establishes the operator equality before mentioning a state.
`expectation_heisenberg_eq_of_disjoint_support` then evaluates that equality in an arbitrary
`psi : Ket Q`. Combining it with the general Schrödinger/Heisenberg identity gives
`expectation_after_local_unitary_eq`:

```lean
expectation (act U psi) A = expectation psi A.
```

Both corollaries quantify over every ket; they do not assume that `psi` is separable, normalized,
or prepared from the fixed reference ket. This is an all-ket consequence of one operator
equality, not an inference from one observed expectation value.

The regression `bellKet` makes the entangled-state case formal rather than relying on a name. It
is the raw-index vector `( |00⟩ + |11⟩ ) / √2`. `norm_bellKet` proves norm one,
`bellPureState` packages that proof, and `bellKet_not_product` refutes an explicit two-coordinate
factorization predicate using the cross-product identity. Both Heisenberg and Schrödinger forms
of remote-`Z` expectation invariance are instantiated on this proved normalized, non-product ket.

## Hypotheses that cannot be dropped

The negative regressions distinguish genuine theorem boundaries from typing artifacts:

- Overlap matters: `same_coordinate_x_and_z_do_not_commute` proves that embedded `X` and `Z` on
  the same coordinate fail to commute. `overlapping_x_changes_z` computes the Heisenberg result as
  `-zAt`, and `overlapping_supported_unitary_does_not_fix_z` packages support, unitarity, failed
  disjointness, and failed invariance together.
- Support witnesses cannot be fabricated: `xAt_zero_not_supported_on_one` proves that `X` on
  coordinate `0` is not supported only on coordinate `1`.
- Unitarity matters: `zero_has_disjoint_support_but_does_not_fix_remote_z` uses a zero evolution
  matrix with support disjoint from a nonzero remote `Z`. Its Heisenberg conjugation is zero, not
  the remote observable, exactly as the Gram-factor theorem predicts.

## Exact scope

These theorems concern exact matrices representing operations with explicit finite
`IsSupportedOn` witnesses. They establish finite supported-operator commutation, unitary
Heisenberg invariance, and the resulting ket expectation equalities.

The later [information layer](information.md) adds density/effect/POVM semantics and proves that a
finite Kraus channel embedded on one selected subsystem preserves every disjoint reduced density,
without a product-state premise. Neither layer establishes an exact continuum or spatial-dynamics
limit, an intrinsic theorem locating provenance, or an ontological account of locality. Those
claims do not follow merely from the absence of a register label in a finite support witness.
