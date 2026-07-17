# Descriptor Triples and Algebraic Completeness

The descriptor layer gives a precise finite-register meaning to the paper's global triples. Its
public modules are [descriptor validity](../Deutsch/Descriptor/Basic.lean),
[constructive algebra generation](../Deutsch/Descriptor/Generation.lean),
[Pauli-word reconstruction](../Deutsch/Descriptor/PauliBasis.lean), and
[comparison relations](../Deutsch/Descriptor/Comparison.lean). Focused positive, boundary, and
negative regressions are in [`DeutschTests.Descriptor`](../DeutschTests/Descriptor.lean). The
underlying operator, support, bit-label, and Heisenberg conventions remain those documented in
[Finite Registers](registers.md) and [Global Conventions](conventions.md).

## Valid triples and families

`Axis` has three values, `x`, `y`, and `z`, with cyclic successor `X -> Y -> Z -> X`. A
`Descriptor Q` is a readable triple of global matrices in `Operator Q`; it is not a one-qubit
matrix and it is not a state. `Descriptor.component` selects one of its axes.

`Descriptor.Valid d` stores only three independent, axis-quantified obligations:

```lean
(d.component a).IsHermitian
d.component a * d.component a = 1
d.component a * d.component a.next = Complex.I • d.component a.next.next
```

The API derives component unitarity, the three reverse products with coefficient `-i`, and all
same-triple anticommutators. Those results are not duplicated as assumptions. In particular,
`Valid.mul_yx`, `Valid.mul_zy`, and `Valid.mul_xz` are derived by taking adjoints of the positive
cyclic laws.

A `DescriptorFamily Q` assigns one global triple to each named qubit. Family validity adds
`PairwiseCommutes`: for every two distinct labels and every two axes, the corresponding global
operators commute. It does not check only one favored pair such as `X` against `Z`.

`Descriptor.initial q` is exactly `xAt q`, `yAt q`, and `zAt q`. Its components have exact
singleton support at `q`. `DescriptorFamily.initial_valid` proves both every local Pauli law and
every arbitrary cross-label component relation.

## Shared unitary evolution

`Descriptor.evolve U d` applies the project convention `U† A U` to all three components.
`DescriptorFamily.evolve U D` uses the same global `U` for every label. The chronology theorems
inherit the register convention rather than introducing a second circuit-order rule.

Hermiticity alone is preserved by arbitrary conjugation, but multiplication and identity require
cancellation. Consequently, `Descriptor.Valid.evolve`,
`DescriptorFamily.PairwiseCommutes.evolve`, and `DescriptorFamily.Valid.evolve` all consume an
explicit unitary-group hypothesis. The tests verify that zero-matrix evolution destroys validity.

## Constructive algebraic completeness

`DescriptorFamily.GeneratesOperatorAlgebra D` means exactly

```lean
Algebra.adjoin ℂ (DescriptorFamily.components D) = ⊤.
```

This is an operator-algebra statement, not an ontological assertion and not a count of symbols.
`initial_generates_operator_algebra` proves it for the initial family on every finite named
register, including the empty register. The proof uses only the initial `X` and `Z` components:

1. `(I ± Z)/2` constructs the two coordinate projectors.
2. A commuting unordered product constructs `Matrix.single x x 1` for every basis assignment.
3. Products of embedded `X` matrices implement the exact transition from `y` to `x`.
4. Sandwiching that transition between the two diagonal projectors constructs
   `Matrix.single x y 1`.
5. The standard matrix basis expansion places every `Operator Q` in the generated subalgebra.

`GeneratesOperatorAlgebra.evolve` maps the generator set through the unitary conjugation
automorphism and proves that every unitary-evolved complete family remains complete.

## Explicit Pauli-word reconstruction

The independent completeness route is computational. A `PauliWord Q` chooses `I`, `X`, `Y`, or
`Z` at every label. `PauliWord.initialPauliString` is its exact global matrix, and
`PauliWord.coefficient A word` is the explicit Hilbert--Schmidt dual coefficient. The theorem
`PauliWord.reconstruction` proves

```lean
∑ word, coefficient A word • initialPauliString word = A
```

for every `A : Operator Q`. `PauliWord.basis` bundles the strings as a genuine `Module.Basis`,
with a two-sided analysis/synthesis equivalence and a proved Kronecker-delta coefficient law.
`initialPauliString_single` identifies a word supported at one label with the corresponding
initial descriptor component.

`evolvedReconstruction` and `evolvedBasis` transport the entire expansion through an arbitrary
bundled unitary. `evolvedPauliString_single` identifies the transported one-site strings with the
components of the evolved descriptor family. Thus both algebra generation and an exact
coefficient reconstruction survive physical evolution.

## Three distinct comparison levels

The comparison API deliberately does not overload equality:

- Exact family equality is Lean equality of all global component matrices.
- `IsUnitaryConjugate D E` means one shared bundled unitary evolves `D` into `E`; this is proved an
  equivalence relation.
- `ReferenceExpectationEquivalent D E` compares only the three component expectations for every
  label in `referenceKet Q`; this too is an equivalence relation, but it is explicitly
  fixed-state and componentwise.

Exact equality implies reference-expectation equivalence. A unitary that fixes the reference ket
also makes a family reference-expectation equivalent to its evolution. The converse is not
claimed. The regression `referenceStabilizer = -Z` fixes the one-qubit paper-zero reference ket,
conjugates the initial family, and changes its `X` operator to `-X`. Lean proves simultaneously
that the two families are unitary-conjugate, reference-expectation equivalent, and not operator
equal.

## Invalid and boundary cases

The focused tests prevent partial checks from being renamed validity:

- The zero triple is Hermitian and satisfies one cyclic equation, but fails the square law.
- The identity triple is Hermitian and satisfies every square law, but fails the cyclic Pauli law.
- Repeating one physically valid descriptor at two different labels satisfies every per-label
  law but fails the family cross-commutation condition.
- Empty initial families are valid and complete; cross-label commutation for a singleton-label
  family is vacuous.

These results formalize the algebraic content of the descriptor claims. They do not identify a
descriptor triple with a reduced state, infer operator equality from one fixed-reference
expectation, define where information is operationally accessible, or establish philosophical
claims about ontology. Statistical and operational notions remain separate downstream layers.
The finite density/effect definitions and their deliberately separate descriptor, detectability,
recovery, and provenance predicates are documented in
[Density States, Channels, and Information Dependence](information.md).
