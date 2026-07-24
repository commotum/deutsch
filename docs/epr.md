# EPR Pair, Circuit, Statistics, and Provenance

The finite EPR layer is split into the phase-sensitive [two-qubit pair](../Deutsch/EPR/Pair.lean),
the [named four-qubit circuit](../Deutsch/EPR/Circuit.lean), its
[two-qubit density/effect statistics](../Deutsch/EPR/Statistics.lean), the
[literal record statistics](../Deutsch/EPR/RecordStatistics.lean), and
[preparation provenance](../Deutsch/EPR/Provenance.lean). Focused regression theorems are in
[`DeutschTests.EPR`](../DeutschTests/EPR.lean).

This page uses the paper-bit, tensor, and chronology choices fixed in
[Global Conventions](conventions.md), the rotation and CNOT definitions from
[Gates, Rotations, and Bell Chronology](gates.md), the density/effect predicates from
[Density States, Channels, and Information Dependence](information.md), and the support meaning
from [Finite-Support Locality](locality.md).

## Registers, order, and circuit chronology

Paper bit `1` is raw `Fin 2` index `0`, while paper bit `0` is raw index `1`. On the pair register,
coordinate `0` is written first and is the inverse-Bell target; coordinate `1` is written second
and is its control. Thus `paperOneOne` is raw assignment `(0,0)` and `paperZeroZero` is raw
assignment `(1,1)`. No outcome relabelling is implicit in the EPR API.

Matrix products act on kets right-to-left. The two-qubit definitions therefore read

```text
pairPreparation       = inverse Bell on coordinates (0,1)
pairRotations theta phi = Rₓ(1,phi) Rₓ(0,theta)
pairCircuit theta phi = pairRotations theta phi * pairPreparation.
```

`pairPreparation_unitary`, `pairRotations_unitary`, and `pairCircuit_unitary` prove the associated
unitarity claims.

The named circuit uses `EPRQubit = Fin 4` with `q1 = 0`, `q2 = 1`, `q3 = 2`, and `q4 = 3`:

| Boundary | Compiled unitary | Schrödinger operation added at that boundary |
| --- | --- | --- |
| `t = 1` | `timeOneUnitary` | inverse Bell, target `q2`, control `q3` |
| `t = 2` | `timeTwoUnitary theta phi` | `Rₓ(theta)` on `q2` and `Rₓ(phi)` on `q3` |
| `t = 3` | `timeThreeUnitary theta phi` | coherent CNOTs `q2 → q1` and `q3 → q4`, with the record qubit as target |
| `t = 4` | `timeFourUnitary theta phi` | comparison CNOT, target `q1`, control `q4` |

All four time-boundary operators have explicit unitarity theorems. The circuit also proves finite
support for the inverse-Bell and rotation layers on `{q2,q3}`, each recording gate on its named
pair, and the comparison gate on `{q1,q4}`. These are finite-register support statements, not a
continuum model of spatial separation.

## Equation (22): exact relative sign and explicit global phase

The library-phased inverse-Bell output is `pairKet`, and `pairKet_eq` proves the exact paper-labelled
formula

```text
pairKet = (1/√2) (|1,1⟩ - |0,0⟩).
```

The source display is represented separately by `equation22Ket`.
`equation22Ket_eq_globalPhase` proves

```text
equation22Ket = -i • pairKet.
```

The relative minus sign is therefore retained, while the conventional Hadamard phase remains
visible. The API does not silently replace equality up to phase with exact ket equality.

For general settings, `pairPureState_ket_eq_four_coordinates` gives the exact rotated ket in the
correlated directions `samePairKet` and `crossPairKet`. The coefficient theorems
`sameCoefficient_eq_cos_sub_half` and `crossCoefficient_eq_I_mul_sin_sub_half` reduce those
coefficients to

```text
cos((theta - phi)/2),       i sin((theta - phi)/2),
```

respectively.

## Equations (25) and (27)

The four-wire descriptor surface consists of `timeOneDescriptors`, `timeTwoDescriptors`, and
`timeThreeDescriptors`. `equation23_q2` and `equation23_q3` give the two exact inverse-Bell
triples, while `equation24_q1` and `equation24_q4` prove that the two coordinates outside the
prepared pair remain initial through time two.

Under the compiled convention `heisenberg U A = U† A U`, an `x` rotation acts by

```text
Y ↦ cos(a) Y - sin(a) Z,
Z ↦ sin(a) Y + cos(a) Z.
```

The six component theorems `timeTwo_q2_x/y/z` and `timeTwo_q3_x/y/z`, bundled by
`equation25_q2` and `equation25_q3`, derive the two Equation (25) triples. For example, the `q2`
components are

```text
x = X₂
y = cos(theta) [-Y₂ X₃] - sin(theta) [-Z₂ X₃]
z = sin(theta) [-Y₂ X₃] + cos(theta) [-Z₂ X₃].
```

Equation (27) is compiled as twelve component theorems `timeThree_q1_x` through
`timeThree_q4_z`, bundled by `equation27_q1` through `equation27_q4`. Each bundle factors the two
recording CNOTs through `timeTwoDescriptors`, so every expanded term follows from the already
proved time-two descriptor identities. The gates are coherent unitaries; calling them records
describes their circuit role and does not add measurement or decoherence semantics.

## Maximally mixed marginals and all-effect independence

`referencePairPureState`, `pairPureState theta phi`, and `pairDensity theta phi` package the exact
pair circuit as normalized pure and density states. For either coordinate `q`,
`pairDensity_reduce_singleton` proves

```text
(pairDensity theta phi).reduce {q} = singletonMaximallyMixed q.
```

This is a density-operator equality, not just a check of the three displayed Pauli expectations in
Equation (26). `pairDensity_locallyStatisticsIndependent` upgrades it to
`LocallyStatisticsIndependent`: every effect on either one-qubit reduction has the same Born
probability for every two pairs of settings. The concrete effects `paperOneMarginalEffect 0` and
`paperOneMarginalEffect 1` have probability `1/2` by
`pairDensity_left_paperOne_probability` and `pairDensity_right_paperOne_probability`. These are
the pair-level `1/2` marginal identities used for Equation (40)'s numerical values; they do not
define a measurement instrument on the later four-wire record state.

## Equations (28), (40), and (41): pair and literal-record routes

`differentEffect` is the joint effect selecting paper outcomes `(1,0)` and `(0,1)`.
`jointPaperOneEffect` selects `(1,1)`. Their compiled Born probabilities are

```text
pairDensity_different_probability:
  P(different) = sin²((theta - phi)/2)

pairDensity_jointPaperOne_probability:
  P(1,1) = (1/2) cos²((theta - phi)/2).
```

The four-wire route is independent of this shortcut. `fourWireTimeThreeDensity theta phi` and
`fourWireTimeFourDensity theta phi` are pure densities obtained by evolving the all-paper-zero
reference state through `timeThreeUnitary` and `timeFourUnitary`. The corresponding equality
theorems expose those evolved-reference definitions directly. The record effects are local effects
on `q1,q4`: `recordOutcomeEffect left right` is the two-bit computational basis effect placed along
`recordPlacement`, while the two marginal effects are `zPlusEffect q1` and `zPlusEffect q4`.

The literal circuit proves Equation (40) as

```text
fourWireTimeThree_leftRecord_probability:
  P(q1 records 1) = 1/2

fourWireTimeThree_rightRecord_probability:
  P(q4 records 1) = 1/2,
```

and Equation (41) as

```text
fourWireTimeThree_jointRecord_probability:
  P(q1 and q4 both record 1) = (1/2) cos²((theta - phi)/2).
```

After the comparison CNOT, `finalComparisonPaperOneEffect = zPlusEffect q1` selects different
recorded outcomes. Thus Equation (28) is represented directly on the time-four state by

```text
fourWireTimeFour_comparison_probability:
  P(q1 records 1 after comparison) = sin²((theta - phi)/2).
```

The `*_eq_pairDensity` theorems first prove that each four-wire probability equals the independently
defined pair probability; only then are the trigonometric pair formulas reused. This is equality of
the relevant computational-record statistics, not equality between the record reduced density and
the coherent pair density: tracing out the source wires removes record-basis coherences.

The boundary theorems prove that the final comparison probability is zero at equal settings and
one whenever `theta - phi = pi`. No selective measurement, collapse, or outcome-conditioned
instrument is inserted into either result.

The source's unnumbered resource-correlation display is also compiled independently.
`pairDensity_z_expectation` gives zero for either local `Z` mean,
`pairDensity_equal_settings_zz_expectation` gives joint `ZZ` mean one, and
`pairDensity_zero_resource_correlation` therefore proves that the joint mean is not the product
of the marginals at the unrotated resource setting. This is a correlation witness, not by itself
a general separability criterion.

The four coordinate theorems `pairDensity_paperOneOne_probability`,
`pairDensity_paperZeroZero_probability`, `pairDensity_paperOneZero_probability`, and
`pairDensity_paperZeroOne_probability` expose the same calculation before the two joint events are
assembled. These are direct effects on the two-qubit pair density and remain an independently
checkable calculation alongside the literal record route.

## Keeping operational claims separate

The EPR layer uses different evidence for different kinds of dependence:

| Evidence | What it establishes | What it does not establish |
| --- | --- | --- |
| `equation25_q2/q3` and `equation27_q1`--`equation27_q4` | exact parameter-dependent descriptor operators | local statistical access or intrinsic location |
| `pairDensity_locallyStatisticsIndependent` | independence of every effect statistic on either singleton | independence of joint effects on the pair |
| `pairSettingFamily_statisticallyDetectable` | a joint effect distinguishes two finite setting choices | which preparation route occurred |
| `RouteHistory` and the two `Preparation` values | explicitly supplied construction history | recovery of that history from the final density |

Concretely, `pairSettingFamily` contains `pairDensity 0 0` and `pairDensity pi 0`.
`pairSettingFamily_locallyStatisticsIndependent q` proves singleton-local independence for either
`q`, while `pairSettingFamily_statisticallyDetectable` packages `differentEffect` as a global
`StatisticallyDetectable` witness. This is an operational separation within one finite family:
local all-effect independence and global detectability both hold.

Accordingly, descriptor occurrence, `LocallyStatisticsIndependent`, a varying joint Born
probability, and preparation provenance are not substituted for one another. The semantic
predicates and their exact quantifiers are documented in
[Density States, Channels, and Information Dependence](information.md).

## Equations (38)--(39): explicit phase and two supplied histories

`equation38Ket theta` records Equation (38) in the source's displayed paper-bit convention:

```text
(1/√2) [sin(theta/2) crossPairKet - i cos(theta/2) samePairKet].
```

Because `samePairKet` is `|1,1⟩ - |0,0⟩`, its second term is exactly the source's
`i cos(theta/2) (|0,0⟩ - |1,1⟩)`. The theorem
`equation38Ket_eq_globalPhase_pairPureState` makes the phase scope explicit:

```text
equation38Ket theta = -i • (pairPureState theta 0).ket.
```

Thus Equation (38) and the compiled circuit describe the same ray and density, while their ket
equality retains the same visible global-phase convention already documented for Equation (22).

`leftRotationRoute theta` rotates the first pair coordinate by `theta` after preparing the EPR
resource. `rightRotationRoute theta` instead rotates the second coordinate by `-theta`.
`equation39_route_kets_eq` proves that these operators have the same action on the prepared
reference ket; it does not assert that the two operators are equal.

The provenance layer packages both routes as normalized pure states and densities.
`equation39_route_pure_kets_eq` and `equation39_route_densities_eq` give their exact output
equalities. `leftRouteDensity_eq_pairDensity` and `rightRouteDensity_eq_pairDensity` identify both
with the public family `pairDensity theta 0`.

History remains separate data. `RouteHistory.left theta` and `RouteHistory.right theta` feed the
two explicit `Preparation` values `leftRoutePreparation` and `rightRoutePreparation`.
`routePreparation_histories_distinct` proves that the tags differ pointwise, while
`routePreparations_same_final_density` proves that their realized final densities agree. This is a
non-identifiability example for supplied provenance; it does not reconstruct history from a final
density operator or make history an intrinsic state property.

## Exact scope and exclusions

The compiled EPR results concern exact matrices on finite two- and four-qubit registers, exact
descriptor identities, finite density operators, and finite effects. In particular, this layer
does not establish:

- a measurement instrument, collapse, post-measurement conditioning, or repeated-record theorem;
- an environment interaction, decoherence channel, pointer basis, or robustness under decoherence;
- a Bell or hidden-variable theorem, counterfactual joint distribution, or Bell-independence
  assumption;
- continuum spacetime dynamics, exact isolation of spatial regions, or an ontological information
  location claim.

The coherent circuit can supply inputs to later models of those topics, but none of them follows
from the words “record,” a finite support witness, descriptor parameter occurrence, or equality of
final states.
