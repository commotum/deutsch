# Global Conventions

This document fixes the conventions used by the Lean development. The executable equalities in
[`DeutschTests.Foundations.Concrete`](../DeutschTests/Foundations/Concrete.lean) are the authority
when an informal diagram, a common textbook convention, or intuition disagrees. Stage 2 supplies
small finite oracles; the public [gate layer](gates.md) turns them into reusable symbolic and
arbitrary-register theorems.

## One-qubit matrices and paper-labelled bits

The concrete convention layer uses
`QubitMatrix = Matrix (Fin 2) (Fin 2) ℂ`, with raw row and column indices in the order `0, 1`.
The Pauli matrices are

```text
X = [[0, 1], [1, 0]]
Y = [[0, -i], [i, 0]]
Z = [[1, 0], [0, -1]].
```

The paper's logical labels are the reverse of the common quantum-computing labels:

| Paper value | Raw `Fin 2` index | Ket | `Z` eigenvalue | Projector |
| --- | ---: | --- | ---: | --- |
| `1` | `0` | `ketOne = ![1, 0]` | `+1` | `(I + Z) / 2` |
| `0` | `1` | `ketZero = ![0, 1]` | `-1` | `(I - Z) / 2` |

`paper_bit_projectors` checks both projector matrices, while `paper_bit_z_eigenvalues` checks both
eigenvector equations. Consequently, digits in names such as `cnot_basis_01` are paper logical
labels, not raw matrix coordinates.

The algebra oracles establish `X*Y = iZ`, `Y*X = -iZ`, and `X² = Y² = Z² = I`. The
`pauli_hermitian`, `pauli_unitary`, and `pauli_traces` probes also exercise mathlib's conjugate
transpose, matrix unitary-group, and unnormalized trace APIs.

## Tensor factors and basis order

`TwoQubitMatrix` has row and column index type `QubitIndex × QubitIndex`. In `A ⊗ₖ B`, `A`
acts on the first/left coordinate and `B` acts on the second/right coordinate. Likewise,

```lean
tensorKet left right (i, j) = left i * right j
```

Mathlib's `finProdFinEquiv` flattens raw pairs in the order

```text
(0,0) → 0, (0,1) → 1, (1,0) → 2, (1,1) → 3.
```

Because paper bits reverse the raw indices, the corresponding paper-labelled order is `11, 10,
01, 00`. `fin_pair_basis_order` checks all four raw pairs. `x_left_factor_all_basis` and
`x_right_factor_all_basis` independently apply `X ⊗ₖ I` and `I ⊗ₖ X` to every paper-labelled
two-qubit basis ket. `kronecker_mulVec_tensorKet` records the product-vector action used by those
tests.

The named finite-register basis and its selected-factor embeddings are now public. A `Finset`
selects a subsystem, while an injection preserves the input register labels when placing a
multi-qubit operator on nonadjacent ambient coordinates. These maps do not introduce an implicit
linear flattening order; see [Finite Registers, Embeddings, and Pure States](registers.md).
Abstract tensor reassociation and its coordinate bridge remain future obligations.

## Products, chronology, and adjoints

Matrix multiplication acts on kets right-to-left. If a Schrödinger circuit applies `U` and then
`V`, its matrix is `V * U`. Matrix adjoint notation `Aᴴ` is conjugate transpose. The project fixes
Heisenberg evolution as

```lean
heisenberg U A = Uᴴ * A * U.
```

This direction is not interchangeable with `U * A * Uᴴ`. For the phase gate
`S = diag(1, i)`, `phase_gate_pins_heisenberg_direction` proves `Sᴴ X S = -Y`, while
`opposite_phase_conjugation_differs` proves `S X Sᴴ = Y`. The abstract tensor-operator probe
`tensor_adjoint` separately checks mathlib's adjoint law for `TensorProduct.map`.
`phase_gate_transforms_x_eigenvectors` also checks both `X` eigenvectors after applying `Sᴴ`, so
the operator chronology and transformed-eigenbasis chronology agree in a phase-sensitive case.

The public `heisenberg` helper accepts arbitrary matrices because it is an algebraic operation.
Calling it physical unitary evolution requires a separate unitarity hypothesis or bundled unitary;
the public [finite-support locality API](locality.md) keeps that distinction explicit. For a
commuting but nonunitary matrix it first proves the exact residual factor
`heisenberg U A = (Uᴴ * U) * A`, and cancels it only from an isometry or unitary hypothesis.

## CNOT

The paper convention names the first/left factor as target and the second/right factor as control.
Logical control value `1` activates `X` on the target:

```lean
cnotTargetLeftControlRight = I_target ⊗ₖ P_control,0 + X_target ⊗ₖ P_control,1.
```

The four independently evaluated basis cases are

```text
00 → 00    10 → 10    01 → 11    11 → 01,
```

with digits ordered `(target, control)` and interpreted as paper bits. The proof
`cnot_projector_formula_is_explicit_permutation` expands the projector formula into an independently
defined permutation matrix. `cnot_involution` checks that applying it twice is the identity.

The six Heisenberg generator oracles are

```text
target X → X ⊗ I       control X → X ⊗ X
target Y → -(Y ⊗ Z)  control Y → X ⊗ Y
target Z → -(Z ⊗ Z)  control Z → I ⊗ Z.
```

These are `cnot_conjugates_target_x/y/z` and `cnot_conjugates_control_x/y/z`. The target-side
minus signs are compatible with the paper's `+1 ↔ bit 1` convention; importing a standard-label
CNOT formula without changing projectors would give the wrong result.

## Rotation sign

The Stage 2 oracle instantiates the Schrödinger convention

```text
Rₓ(π/2) = (I - iX) / √2,
```

which is `exp(-iθX/2)` at `θ = π/2`. Under the project's Heisenberg direction,
`rx_pi_div_two_pins_heisenberg_y` and `rx_pi_div_two_pins_heisenberg_z` prove

```text
Rₓ(π/2)† Y Rₓ(π/2) = -Z,
Rₓ(π/2)† Z Rₓ(π/2) =  Y.
```

These signs are computed from the matrices rather than imported from a rotation mnemonic. The
public symbolic theorems prove the corresponding formulas for every real angle. The arbitrary-axis
layer derives the same specialization from the matrix exponential and the Rodrigues formula; see
[Gates, Rotations, and Bell Chronology](gates.md).

## Hadamard and Bell chronology

For Fig. 1, time runs upward: CNOT acts first, then Hadamard acts on the right/control wire.
Right-to-left matrix chronology therefore gives

```lean
paperBellTransform = (I ⊗ₖ H) * CNOT
paperBellTransformInverse = CNOT * (I ⊗ₖ H).
```

`paper_hadamard_involution`, `cnot_involution`, and
`hadamard_on_right_control_involution` check the component involutions.
`paper_bell_chronology_inverse_left` and `paper_bell_chronology_inverse_right` check both matrix
products, so one accidentally reversed definition cannot pass merely by sharing the same mistake
with its inverse.

The public gate layer now proves both inverse laws, exact transition amplitudes, pair support,
unitarity, and all twelve descriptor transformations in equations (20)–(21).

## Semantic scope

The convention oracles are exact matrix equalities. They do not by themselves establish an
operational information claim, a channel theorem, equality only up to global phase, or a statement
about arbitrary register sizes. Register equality levels and the current state and measurement
proof limits are recorded in [Finite Registers, Embeddings, and Pure States](registers.md) and
[Representation Decision](representation.md). The exact arbitrary-register theorem and its
limits are recorded in [Finite-Support Locality](locality.md). Descriptor validity, algebraic
completeness, and the separation of conjugacy from equality are recorded in
[Descriptor Triples and Algebraic Completeness](descriptors.md).
Exact gate matrices, phases, rotation signs, and Bell chronology are recorded in
[Gates, Rotations, and Bell Chronology](gates.md).
