# Density States, Channels, and Information Dependence

The public information layer is [`Deutsch.Information`](../Deutsch/Information.lean), split into
[density states, effects, and POVMs](../Deutsch/Information/State.lean),
[selected-subsystem reduction](../Deutsch/Information/Reduction.lean),
[explicit finite-register purification](../Deutsch/Information/Purification.lean),
[finite Kraus channels](../Deutsch/Information/Channel.lean),
[channels on selected subsystems](../Deutsch/Information/LocalChannel.lean),
[semantic dependence predicates](../Deutsch/Information/Dependence.lean),
[one-qubit tomography and mixed-state boundaries](../Deutsch/Information/Qubit.lean), and a
[classical one-time-pad boundary example](../Deutsch/Information/OneTimePad.lean). Focused
positive, negative, and boundary regressions are in
[`DeutschTests.Information`](../DeutschTests/Information.lean). The matrix, register, and paper-bit
conventions remain those in [Global Conventions](conventions.md) and
[Finite Registers](registers.md).

## Density states, effects, and Born probabilities

A `Density Q` is a concrete register matrix that is positive semidefinite and has trace one. An
`Effect Q` stores positivity of both `E` and `I-E`, and a `POVM Q Outcome` is a finite effect family
whose operators sum to the identity. A POVM describes outcome probabilities only; it is not an
instrument and does not specify a post-measurement state.

The complex Born weight and its real probability are

```text
bornWeight      rho E = trace (rho E)
bornProbability rho E = re (trace (rho E)).
```

The reality and bounds are theorems, not extra structure fields. For arbitrary positive
semidefinite `rho` and `E`, `trace_mul_nonneg_of_posSemidef` factors `E = C†C`, cycles the trace,
and applies positivity to `C rho C†`. The layer then proves that every Born weight is real, every
probability lies in `[0,1]`, and every finite POVM normalizes. `Effect.binaryPOVM` pairs any effect
with its complement. `computationalBasisPOVM` and `basisDensity_basisEffect_probability` give exact
finite-register computational-basis semantics.

Every density is itself an effect: its nonnegative eigenvalues sum to one, so each is at most one.
Testing statistical equivalence against the two density operators then proves
`density_eq_iff_effect_probabilities` in every finite dimension.

`pureDensity` turns the existing normalized `PureState` into a rank-one density operator, and
`densityExpectation_pureDensity` proves agreement with the earlier ket expectation. Unitary
Schrödinger evolution is `rho.evolve U hU`; `densityExpectation_evolve` proves its exact duality
with the project convention `U† A U`.

## Explicit purification and the same-register boundary

The pure fixed-reference theorem remains valid: every normalized finite-register ket has a
unitary preparation from the paper-zero reference ket. It does not extend to arbitrary mixed
states by a same-register unitary. `purity_evolve` proves unitary invariance of
`re (trace (rho rho))`, while `maximallyMixedQubit_cannot_evolve_to_reference` gives an executable
counterexample: the maximally mixed qubit has purity `1/2`, and every computational-basis reference
density has purity `1`.

The enlarged-register result is constructive. For any finite qubit-label type `Q`,
`PurificationRegister Q = Sum Q Q` supplies labelled original and copy registers.
`purificationKet rho` vectorizes the positive square root `CFC.sqrt rho.op`; its normalization
follows from

```text
trace (sqrt(rho) * sqrt(rho)) = trace rho = 1.
```

`purification_reduce_original` then proves directly from the partial-trace sum that discarding the
copy returns `rho` on the selected original subsystem. `purificationReducedDensity_eq` transports
those labels back to `Q` and states the exact equality `purificationReducedDensity rho = rho`.
No existential “assume a purification” premise is used.

The operational bridges retain their quantifiers. `purification_embedded_expectation` proves that
every operator `A : Operator Q` has the same expectation in `rho` as `A` embedded on the original
copy has in the explicit pure state. `exists_unitary_preparation_purification` prepares that
enlarged pure state from the enlarged paper-zero reference, and
`exists_purification_fixed_reference_representation` packages one such unitary together with the
fixed-reference Heisenberg prediction equality for every embedded `A`.

This does not contradict the same-register obstruction: the preparation unitary acts on
`PurificationRegister Q`, and the mixed state appears only after the second copy is discarded.
For evolution that stays on `Q`, the general density-level statement remains
`densityExpectation_evolve`.

## Selected-subsystem reduction and tomography

For `s : Finset Q`, `partialTrace s` first reindexes the global basis into selected and complement
coordinates and then explicitly sums the complement diagonal. Positivity and trace preservation
are derived from that formula. Its central duality theorem is

```text
trace (partialTrace s rho * A) = trace (rho * embedSubsystem s A).
```

Consequently, `rho.reduce s` is a density state and every reduced local effect has exactly the
same Born probability as its globally embedded form.
`reduced_density_eq_iff_embedded_effect_probabilities` identifies arbitrary reduced-state equality
with equality of all globally embedded local effect probabilities.

On one qubit, `xPlusEffect`, `yPlusEffect`, and `zPlusEffect` are the three Pauli `+1` effects;
`zPlusEffect` is exactly the paper's `bit 1` projector `(I+Z)/2`. The tomography theorem
`density_eq_of_pauliPlus_probabilities` proves that equality of these three probabilities
determines a one-qubit density. The singleton reduction theorem then connects density equality,
all local effect statistics, and the three Pauli statistics. These bridges support the later EPR
and teleportation calculations without prejudging their concrete values.

## Finite Kraus channels and no-signalling

A `KrausChannel Q R K` supplies finitely many typed matrices
`K k : Matrix (Basis R) (Basis Q) ℂ` and the trace-preserving completeness equation

```text
∑ k, (K k)† * K k = I.
```

Its Schrödinger action preserves positive semidefiniteness and trace, so `mapDensity` maps density
states to density states. The Heisenberg `dualEffect` is again a valid effect, and
`bornProbability_mapDensity` proves exact Born-rule duality. Identity, unitary, and composed
channels are public, with composition proved to act by ordinary function composition on density
states.

A fixed channel cannot create an operational parameter distinction that was absent at its input.
`KrausChannel.statisticsIndependent_mapDensity` is this finite data-processing result. Separately,
`KrausChannel.onSubsystem` embeds every Kraus operator on a selected named subsystem. If `s` and
`t` are disjoint, `onSubsystem_reduce_disjoint` proves

```text
((channel.onSubsystem s).mapDensity rho).reduce t = rho.reduce t
```

for every global density `rho`, with no product-state premise. The proof first shows that the dual
channel fixes every effect embedded on `t`, then uses effect extensionality. This is an exact finite
same-register no-signalling theorem. It does not model parameter-dependent channels, changing
register types, continuum spatial dynamics, measurement instruments, decoherence, or discarded
environments.

## Separate information predicates

The API deliberately keeps operational, representational, recovery, and historical claims
distinct:

| Predicate | Meaning | Not implied by the name |
| --- | --- | --- |
| `EffectStatisticallyEquivalent rho sigma` | Every effect has the same probability | Descriptor syntax equality |
| `WeaklyDistinguishable rho sigma` | Some effect has unequal probability | Perfect single-shot discrimination |
| `StatisticsIndependent family` | Every parameter pair is effect-statistically equivalent | Absence of preparation history |
| `LocallyStatisticsIndependent s family` | Every effect on the reduced state of `s` is independent | Joint independence on a larger subsystem |
| `LocallyDetectable s family` | Some reduced-state effect detects a parameter pair | Recovery of a named target family |
| `DescriptorNonconstant family` | A named descriptor component changes | Operational accessibility |
| `Recovers decoder encoded target` | A specified state transformer exactly returns the target | Physicality unless the decoder is a channel |
| `Preparation.ProvenanceNonconstant` | Explicit supplied history data changes | Recoverability of history from the final density |

In finite dimension, `EffectStatisticallyEquivalent rho sigma` is exactly `rho = sigma`, and
`WeaklyDistinguishable rho sigma` is exactly `rho ≠ sigma`. Reduced-state equality is likewise
equivalent to local effect-statistical equivalence. `LocallyDetectable.statisticallyDetectable`
embeds a local witness globally, and fixed Kraus channels preserve statistical equivalence.
`ProcessPreparation` and `Preparation` carry explicit factorization/history data rather than
attempting to reconstruct provenance from a final state.

## Classical one-time-pad boundary

The diagonal two-qubit family `oneTimePadDensity secret` is the uniform mixture of

```text
(key, key + secret),    key ∈ Fin 2.
```

`oneTimePadDensity_reduce_singleton` proves that either coordinate is exactly maximally mixed for
both secrets, and `oneTimePad_locallyStatisticsIndependent` upgrades this to every effect on the
chosen singleton. Jointly, `parityEffect` reads the secret with probability one, so
`oneTimePad_statisticallyDetectable` proves global detectability. `parityDecoder` is an explicit
finite Kraus measurement-and-preparation channel, and `parityDecoder_recovers` proves exact
recovery of the one-qubit secret family.

The provenance boundary is separate. `swappedOneTimePadDensity` constructs the same mixture with
ciphertext and key coordinates exchanged, and `swappedOneTimePadDensity_eq` proves equality of the
final density families. `oneTimePadPreparationLeft` and `oneTimePadPreparationRight` retain these
two construction routes as explicit, pointwise-distinct histories while realizing the same final
density. Thus the final density alone does not reconstruct the supplied provenance.

This is a scoped classical diagonal example. It does not consume the paper's EPR circuit, assert
entanglement, formalize the literature on “nonlocality without entanglement,” or infer an intrinsic
spatial information location from the symmetric final state.

## Scope

This layer establishes finite density/effect/POVM semantics, explicit doubled-register
purification, selected-subsystem statistics, one-qubit tomography, typed finite channels,
selected-subsystem no-signalling, and carefully separated information predicates. It does not
define measurement instruments, post-measurement conditioning, entropy or capacities, perfect
discrimination, continuum dynamics, generic decoherence, or provenance as an intrinsic property
of a final density operator. Concrete EPR, teleportation, decoherence, and Bell claims are
implemented in their separate public layers so their additional circuit, channel, and
counterfactual assumptions remain visible.
