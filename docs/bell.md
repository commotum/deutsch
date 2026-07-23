# Corrected finite Bell audit

The source's Bell section contains a valid finite contradiction idea but not a valid printed proof.
This library formalizes a corrected three-setting pigeonhole inequality and keeps its assumptions
separate from the project's dynamical locality and no-signalling theorems.

## Source corrections

The EPR layer proves the following raw-outcome probabilities:

```text
P(different at theta, phi) = sin²((theta - phi) / 2)
P(both paper-one)          = 1/2 cos²((theta - phi) / 2).
```

Consequently equal settings give equal raw outcomes with probability one. The source's printed
Equation (41) uses the complementary Bob event and cannot be combined with the unrelabelled record
variables as written. Equations (42)–(44) therefore also require either an explicit Bob relabeling
or a corrected argument.

Equation (45) is independently false at `(a₀,a₁,a₂)=(1,0,1)`: its right side evaluates to
`2`, not `1`. The source-regression API compiles that counterexample and verifies the corrected
complementary-event partition on all eight Boolean triples. The agreement-counting proof below
does not use Equation (45); the separate expectation proof uses the complementary partition.

## Finite deterministic model

`Deutsch.Bell.Setting` is `Fin 3`. A `LocalAssignment` contains two Boolean response tables:

- `aliceResponse assignment aliceSetting` accepts only Alice's setting;
- `bobResponse assignment bobSetting` accepts only Bob's setting.

A real `weight : LocalAssignment → ℝ` is required to be pointwise nonnegative and normalized.
It has no setting argument, making measurement-setting independence explicit in this finite model.
`HasPerfectEqualSettingSupport weight` says that every positive-weight assignment gives equal
Alice/Bob values at equal settings. Zero-weight assignments are deliberately unconstrained.
`perfectEqualSettingSupport_of_agreementProbability_one` derives this support statement from
nonnegativity, normalization, and the observable probability-one equal-setting equations; the
strongest contradiction therefore does not assume support equality separately.

This is a distribution over deterministic counterfactual response tables. It directly models the
paper's assumption that a single-valued result exists for each of the finitely many settings. A
general theorem refining every stochastic factorizable response model into such deterministic
tables is not part of this library, so the result should not be advertised as a formal
equivalence with every formulation of Bell locality.

## Pigeonhole inequality

For every three-bit response table, at least one of the pairs `(0,1)`, `(1,2)`, or `(0,2)` agrees.
`commonAssignment_indicator_sum_ge_one` proves this pointwise, and
`local_three_setting_bell_inequality` averages it to

```text
1 ≤ P(A₀ = B₁) + P(A₁ = B₂) + P(A₀ = B₂).
```

The three EPR angles are `0`, `2π/3`, and `4π/3`. The quantum layer derives, rather than
assumes, that each distinct pair has same-outcome probability `1/4`; it also proves perfect
equal-setting agreement. Thus the right side required by the quantum predictions is `3/4`, which
contradicts the local bound. `corrected_epr_three_settings_refute_local_assignments` is the
reusable lower-level support-explicit theorem. The stronger
`corrected_epr_three_settings_refute_normalized_local_model` has no perfect-support premise: from
nonnegative normalized weights and reproduction of the complete quantum table, it derives
probability-one equal-setting agreement and then equality on every positive-weight response
table. Zero-weight tables remain unconstrained.
`no_normalized_local_model_reproduces_corrected_epr_three_settings` is the strongest reusable
negated form.

The quantum special-angle proofs import the corrected EPR density/effect theorem but no
hidden-variable definitions. Conversely, the finite inequality imports no quantum state API.
`ReproducesThreeSettingQuantumAgreements` is the explicit bridge between those layers.

## Direct Equations (42)--(46) expectation proof

[`Deutsch.Bell.Moments`](../Deutsch/Bell/Moments.lean) formalizes the displayed source route
independently of the agreement-counting theorem. `FiniteProbabilityWeight` supplies a nonnegative
normalized weight on a finite sample type, and `ReproducesThreeSettingEPRMoments` states exactly
the Equation (40) one-site means and Equation (41) joint paper-one moments for separate Alice and
Bob response functions.

The compiled chain is:

| Display | Production result |
| --- | --- |
| (42) | `equation42_mean_square_zero` expands the Boolean square and evaluates its mean as zero. |
| (43) | `equation43_equal_on_positive_support` derives equal responses only at samples of strictly positive weight. |
| (44) | `equation44_alice_joint_moment` replaces Bob's response inside an expectation on that positive support. |
| (45) | `equation45_complementary_partition` uses the actual complement of the Boolean disjunction. |
| (46) | `equation46_chain` proves every displayed equality and inequality; `equation46_contradiction` derives the contradiction. |

In the Equation (46) proof, the expanded mean is proved equal to

```text
3/8 - E[a(0) a(2π/3) a(4π/3)].
```

The triple product is pointwise nonnegative, so the chain ends at `1/2 ≤ 3/8`.
`Deutsch.Bell.Moments` imports the three-setting trigonometric facts but imports neither
`Deutsch.Bell.Finite` nor `Deutsch.Bell.Contradiction`; the direct expectation and pigeonhole
arguments therefore remain independently checkable.

## What “locality” means here

The Bell theorem's counterfactual locality assumption concerns simultaneous response tables whose
Alice and Bob entries depend only on their respective settings, together with a setting-independent
common distribution. It is not definitionally the same as:

- disjoint finite supports and commutation of operators;
- Heisenberg invariance under a remote supported unitary;
- preservation of a disjoint reduced density by a selected-subsystem channel;
- ordinary operational no-signalling or local statistical independence.

The earlier library theorems establish those dynamical and operational properties under their own
hypotheses. They neither construct nor refute the counterfactual assignment space assumed here.

## Interpretive boundary and reuse

The compiled conclusion is only that the listed normalized-weight, deterministic local-response,
setting-independent-distribution, and corrected quantum-reproduction assumptions are
inconsistent. Perfect agreement is one independently derived part of the reproduced quantum
table. The theorem does not
prove that a particular premise is uniquely responsible, select a single-outcome or many-worlds
ontology, or turn matrix-valued descriptors into a philosophical conclusion.

Import `Deutsch.Bell.Moments` for the displayed expectation chain, `Deutsch.Bell.Finite` for the
agreement-counting inequality, `Deutsch.Bell.Quantum` for the EPR probabilities, or
`Deutsch.Bell` for both integrated contradictions.
