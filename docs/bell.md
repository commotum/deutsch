# Finite Bell derivations

The Bell layer exposes two independently checkable finite contradiction cores and a constructive
extension of the response-table core to stochastic models:

- `Deutsch.Bell.Moments` follows Equations (40)–(46) as expectations of Boolean response
  functions on one finite weighted space.
- `Deutsch.Bell.Finite`, `Deutsch.Bell.Quantum`, and `Deutsch.Bell.Contradiction` give a separate
  three-setting agreement-counting argument over explicit deterministic local response tables.
- `Deutsch.Bell.Stochastic` turns any finite setting-independent factorizable stochastic response
  model into such a table distribution while preserving its observable probabilities.

Neither route imports or identifies the project's operator-support locality and channel
no-signalling predicates with Bell's counterfactual response-table assumptions.

## Quantum statistics

The EPR layer proves

```text
P(different at theta, phi) = sin²((theta - phi) / 2)
P(both paper-one)          = 1/2 cos²((theta - phi) / 2).
```

Thus equal settings give equal raw outcomes with probability one. The three angles used by the
finite contradiction are `0`, `2π/3`, and `4π/3`; every distinct pair in that family has
same-outcome probability `1/4`.

The literal four-wire Figure 2 circuit is connected to the pair-density calculation, not merely
compared by a final trigonometric formula:

- `fourWireTimeThree_leftRecord_probability_eq_pairDensity` and
  `fourWireTimeThree_rightRecord_probability_eq_pairDensity` identify the two record marginals;
- `fourWireTimeThree_jointRecord_probability_eq_pairDensity` identifies the joint paper-one event;
- `fourWireTimeFour_comparison_probability_eq_unequal_pair_sum` first reduces the final comparison
  to the structural unequal-pair basis sum; and
- `fourWireTimeFour_comparison_probability_eq_pairDensity` identifies that result with the
  two-qubit unequal-outcome probability.

## Direct Equations (40)–(46)

`FiniteProbabilityWeight` supplies nonnegative normalized weights on a finite sample type.
`ReproducesAngleEPRMoments` states the Equation (40) one-site means and Equation (41) joint
paper-one moments for two Boolean response functions on arbitrary settings equipped with a real
angle. Taking the setting type to be `ℝ` and the angle map to be the identity gives the
all-real-angle presentation.

The direct chain is:

| Display | Production result |
| --- | --- |
| (42) | `angleEquation42_mean_square_zero` expands the Boolean square and evaluates its expectation as zero. |
| (43) | `angleEquation43_equal_on_positive_support` derives equality at every sample of strictly positive weight. |
| (44) | `angleEquation44_alice_joint_moment` substitutes the equal response inside the expectation. |
| (45) | `equation45_complementary_partition` proves the pointwise complementary-event partition. |
| (46) | `equation46_chain` proves the displayed equalities and inequalities, and `equation46_contradiction` derives `False`. |

`restrictRealAngleMomentsToThreeSettings` restricts one all-real-angle model along
`threeSettingAngle`, so the same model that supplies Equations (42)–(44) supplies the
three-setting premises of Equations (45)–(46).

In the Equation (46) proof, the expanded mean is

```text
3/8 - E[a(0) a(2π/3) a(4π/3)].
```

The triple product is pointwise nonnegative, so the chain ends at `1/2 ≤ 3/8`.
`Deutsch.Bell.Moments` imports neither `Deutsch.Bell.Finite` nor
`Deutsch.Bell.Contradiction`; the direct expectation route therefore remains independent of the
agreement-counting route.

## Independent three-setting assignment route

`Deutsch.Bell.Setting` is `Fin 3`. A `LocalAssignment` contains two Boolean response tables:

- `aliceResponse assignment aliceSetting` accepts only Alice's setting;
- `bobResponse assignment bobSetting` accepts only Bob's setting.

A real `weight : LocalAssignment → ℝ` is pointwise nonnegative and normalized. It has no setting
argument, making measurement-setting independence explicit in this finite model.
`HasPerfectEqualSettingSupport weight` says that every positive-weight assignment gives equal
Alice and Bob values at equal settings; zero-weight assignments are deliberately unconstrained.
`perfectEqualSettingSupport_of_agreementProbability_one` derives that support condition from the
observable probability-one equal-setting equations.

For every three-bit response table, at least one of the pairs `(0,1)`, `(1,2)`, or `(0,2)` agrees.
`local_three_setting_bell_inequality` averages that fact:

```text
1 ≤ P(A₀ = B₁) + P(A₁ = B₂) + P(A₀ = B₂).
```

The quantum values make the right side `3/4`.
`epr_three_settings_refute_normalized_local_model` derives the contradiction from nonnegative
normalized weights and reproduction of the complete three-setting agreement table;
`no_normalized_local_model_reproduces_epr_three_settings` is its reusable negated form.

The finite inequality imports no quantum state API, while the special-angle quantum theorems
import no hidden-variable definitions. `ReproducesThreeSettingQuantumAgreements` is the explicit
bridge between the layers.

## Finite stochastic response models

`StochasticLocalModel Ω` states the conventional finite factorizable assumptions directly. The
finite hidden type `Ω` carries one nonnegative normalized `hiddenWeight` with no setting argument.
At each hidden value, `aliceKernel` receives only Alice's setting and `bobKernel` only Bob's
setting. Each `BoolResponseKernel` is nonnegative and normalized, and
`stochasticJointOutcomeProbability` is the hidden-weighted product of the two local response
probabilities. Thus setting independence, parameter locality, and outcome factorization are
visible in the definition rather than supplied later as an informal reading.

The reduction to complete tables is constructive. For each hidden value, `responseTableWeight`
takes the product of the response probabilities at all three settings. `conditionalTableWeight`
then multiplies the Alice and Bob table weights, giving a product distribution on the six
coordinates

```text
(A₀, A₁, A₂, B₀, B₁, B₂).
```

`refinedLocalWeight` averages this conditional six-coordinate coupling over the original hidden
weight. No complete response table is an input to the stochastic model. The product coupling is
constructed from its six local kernels, and the normalization proofs sum out every unobserved
coordinate.

The preservation results are pointwise in the selected settings and outcomes:

| Observable | Preservation theorem |
| --- | --- |
| Alice's one-party outcome | `refinedLocalWeight_preserves_alice_outcome` |
| Bob's one-party outcome | `refinedLocalWeight_preserves_bob_outcome` |
| Every Alice–Bob joint outcome | `refinedLocalWeight_preserves_joint_outcome` |
| Every Alice–Bob agreement probability | `refinedLocalWeight_preserves_agreement` |

Consequently, `refinedLocalWeight_reproduces_three_setting_agreements` transfers reproduction of
the full three-by-three EPR agreement table to the deterministic-table contract.
`epr_three_settings_refute_stochastic_local_model` then applies the independently proved table
contradiction. Its premises contain no response-table or perfect-equal-setting-support hypothesis:
normalization and nonnegativity of the table weight are proved by the construction, and
equal-setting support follows downstream from the reproduced probability-one agreements.

This refinement is not part of the direct Equations (42)–(46) proof.
`Deutsch.Bell.Moments` derives that expectation chain from its own finite common-space moment
contract, and it does not import `Deutsch.Bell.Stochastic`. The stochastic theorem instead widens
the scope of the independent three-setting response-table route.

## Scope of the conclusion

The compiled conclusions reject the listed finite common-space or finite-hidden-variable,
Boolean-response, setting-locality, factorization, setting-independent-weight, normalization,
nonnegativity, and quantum-reproduction premises as the relevant conjunction. They do not select
one premise as uniquely responsible, choose an ontology, or turn matrix-valued descriptors into
an interpretive conclusion.

This response-table locality is distinct from:

- commutation of operators with disjoint finite support;
- Heisenberg invariance under a remote supported unitary;
- preservation of a disjoint reduced density by a selected-subsystem channel; and
- operational no-signalling or local statistical independence.

Import `Deutsch.Bell.AngleMoments` for all-setting Equations (42)–(44),
`Deutsch.Bell.Moments` for the finite Equation (45)–(46) chain,
`Deutsch.Bell.Finite` for the counting inequality, `Deutsch.Bell.Quantum` for the EPR
probabilities, `Deutsch.Bell.Stochastic` for the finite factorizable refinement, or
`Deutsch.Bell` for the complete Bell API.

For the separate comparison with the original typesetting, see
[Printed-form comparison](errata.md).
