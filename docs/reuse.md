# Reusing the public Lean API

The verification module
[`DeutschTests/Examples.lean`](../DeutschTests/Examples.lean) is the executable companion to this
guide. It imports only the public root:

```lean
import Deutsch

namespace MyProject

open Deutsch Deutsch.Bell Deutsch.Foundations Deutsch.Gates Deutsch.Information Deutsch.Locality
  Deutsch.Register
open scoped BigOperators

noncomputable section
```

This is the simplest import for downstream work and checks that the public root actually exports
every layer used below. Larger developments may instead import a narrower root such as
`Deutsch.Register`, `Deutsch.Gates`, `Deutsch.Information`, or `Deutsch.Bell` to reduce dependency
surface. Production code should not import `DeutschTests`: that namespace contains verification
wrappers rather than library declarations.

Readers following the numbered derivation can instead import `Deutsch.Paper`, which exposes
`Deutsch.Paper.equation01` through `Deutsch.Paper.equation46`. New proofs should normally use the
underlying topical declarations demonstrated below; the
[equation-by-equation façade guide](paper.md) gives the module map.

## Named registers and Heisenberg gates

`DeutschTests.Examples.named_pauli_is_embedded` checks the basic named-register construction:

```lean
theorem named_pauli_is_embedded :
    xAt (1 : Fin 3) = embedQubit (1 : Fin 3) pauliX :=
  rfl
```

Here `xAt q` is a global operator on the full register, not a standalone two-by-two matrix.
`DeutschTests.Examples.named_rotation_preserves_its_x_axis` then reuses the public gate theorem
`rotationXAt_heisenberg_x`:

```lean
theorem named_rotation_preserves_its_x_axis (theta : ℝ) :
    Register.heisenberg (rotationXAt (1 : Fin 3) theta) (xAt (1 : Fin 3)) =
      xAt (1 : Fin 3) :=
  rotationXAt_heisenberg_x 1 theta
```

Named multi-qubit gates make placement order explicit. This example places local coordinate `0`
on target `0` and local coordinate `1` on control `2`:

```lean
theorem named_cnot_uses_target_control_placement :
    cnotAt (0 : Fin 3) (2 : Fin 3) (by decide) =
      embedAlong
        (targetControlPlacement (0 : Fin 3) (2 : Fin 3) (by decide))
        cnotLocal :=
  rfl
```

The project fixes Heisenberg evolution as `Uᴴ * A * U`. Named CNOT and Bell constructors take
explicit target/control coordinates, and the paper's logical bits reverse the raw matrix indices;
see [Global Conventions](conventions.md) before translating external formulas.

## Disjoint-support locality

`DeutschTests.Examples.local_x_fixes_remote_z` instantiates the general supported-unitary theorem:

```lean
theorem local_x_fixes_remote_z :
    Register.heisenberg (xAt (0 : Fin 3)) (zAt (2 : Fin 3)) =
      zAt (2 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 2)
```

`IsSupportedOn s A` is an at-most-support witness. The locality theorem also needs disjointness and
unitarity; support alone does not justify cancellation. This operator statement is distinct from
channel no-signalling and from the counterfactual locality assumption in the Bell layer.

## Operational information semantics

`DeutschTests.Examples.one_time_pad_hides_secret_locally` demonstrates a semantic statement rather
than a syntactic descriptor check:

```lean
theorem one_time_pad_hides_secret_locally (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2)) oneTimePadDensity :=
  oneTimePad_locallyStatisticsIndependent q
```

`LocallyStatisticsIndependent s family` compares every effect statistic on the selected reduced
subsystem. It does not assert that the full density family is constant: the joint parity effect in
this example still detects the secret. See
[Density States and Information Dependence](information.md) for density/effect duality, channels,
recovery, and the distinctions among the information predicates.

## Bell predictions and contradiction

`DeutschTests.Examples.three_setting_quantum_probability` consumes the quantum half of the Bell
API:

```lean
theorem three_setting_quantum_probability
    (i j : Setting) (hij : i ≠ j) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle j) =
      (1 / 4 : ℝ) :=
  threeSetting_sameOutcomeProbability_of_ne i j hij
```

The strongest integrated wrapper in the example file is
`DeutschTests.Examples.quantum_table_refutes_normalized_local_model`:

```lean
theorem quantum_table_refutes_normalized_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_normalized_local_model_reproduces_epr_three_settings
    weight weight_nonnegative weight_normalized
```

The conclusion is limited to the displayed finite deterministic response-table model. The theorem
derives equal-setting agreement on positive-weight support from probability-one reproduction;
zero-weight tables remain unconstrained. It is neither the dynamical locality theorem above nor an
ontological conclusion. See [Finite Bell derivations](bell.md) for the full assumption audit and
the independent direct Equation-(40)–(46) route.

## Compile the examples

From the repository root:

```bash
lake env lean DeutschTests/Examples.lean
```

When copying several snippets into one file, close the namespace and noncomputable section from
the prelude in the ordinary way:

```lean
end
end MyProject
```
