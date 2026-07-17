# Explicit dephasing and classical records

The library uses *decoherence* only for a named finite Kraus channel in a named basis.  The EPR
and five-wire teleportation circuits remain coherent unitary models; inserting a channel changes
their global state and therefore requires a separate theorem about whichever state or statistic is
claimed to survive.

## Coordinate dephasing

`Deutsch.Information.coordinateDephasing q` is the nonselective computational-basis measurement
of coordinate `q`.  Its two Kraus operators are the two embedded rank-one projectors.  As in the
rest of the project, paper bit `1` is raw index `0`, while paper bit `0` is raw index `1`; the sum of
the two projectors is independent of this naming reversal.

For every register operator `A` and basis words `x,y`, the exact action is

```text
(coordinateDephasing q).mapOperator A x y =
  if x q = y q then A x y else 0.
```

Thus the channel preserves trace, fixes every computational-basis density, and is idempotent.  It
does not preserve arbitrary quantum information: its Heisenberg dual kills `xAt q`, and
`coordinateDephasing_changes_xPlusEffect` proves that the `X=+1` effect is changed.  The compiled
raw-bit regression separately shows why preserving the record basis is not the same as tolerating
classical bit errors.

This is a nonselective channel.  It contains no outcome value and is not an
outcome-conditioned measurement instrument.

## Named environment realization

The one-qubit realization fixes all of the assumptions that are implicit in the paper's
environment language:

- `cnotEnvironmentState` is paper zero, hence raw computational index `1`;
- `cnotEnvironmentCoupling` is a unitary CNOT with the system as control and environment as
  target;
- `cnotEnvironmentKraus environmentOutput` takes the corresponding matrix element against the
  fixed input environment bit;
- summing over `environmentOutput` discards the environment.

`cnotEnvironmentKraus_eq_coordinateDephasingKraus` calculates the two resulting Kraus matrices,
and `cnotEnvironmentDephasing_mapDensity` proves agreement with coordinate dephasing on every
one-qubit density.  This is one exact finite dilation, not a claim that every physical environment
measures in the computational basis.

## Teleportation records

`Deutsch.Decoherence.protocolRecordDephasing` composes coordinate dephasing on record coordinates
`0` and `1` of the semantic teleportation register and leaves receiver coordinate `2` untouched.
Its entry formula retains exactly the blocks for which both record bits agree.

The semantic encoder in [`Deutsch.Teleportation.Protocol`](../Deutsch/Teleportation/Protocol.lean)
is already block diagonal in those records.  Consequently,
`protocolRecordDephasing_encoder_mapOperator` fixes every encoded operator, not only the two test
states, and `protocolDecoder_after_recordDephasing` recovers every input density exactly.

`protocolRecordKBitFlip` supplies the contrasting real error channel: it is unitary Pauli-X on the
first record.  On either computational input it turns the encoded family into the encoding of the
opposite raw input, so the unchanged decoder returns that opposite input.

That theorem has deliberately limited scope.  It proves recovery for the separately constructed
uniform-branch encoder/decoder model.  It does not identify that mixed state with the global state
of the coherent five-wire circuit, and it does not say that the two classical records alone have
quantum capacity.  Recovery uses the records together with the receiver half of the prepared
resource.  The singleton-independence and joint-recovery results are documented in
[`teleportation.md`](teleportation.md).

## Corrected robustness claims

The formal results support these bounded readings of the source:

- repeating the same nonselective computational dephasing is harmless after the first
  application because the channel is idempotent;
- a fixed parameter-independent channel preserves an already statistically independent family,
  as described in [`information.md`](information.md);
- computational-record dephasing preserves the named teleportation encoder and decoder result;
- the explicit CNOT environment realizes this dephasing only with its fixed blank state, selected
  basis, coupling, and discard.

They do **not** prove generic immunity to noise, that an arbitrary pure qubit is maximally
vulnerable, or that a coherent CNOT by itself is a measurement.  A computational-basis pure state
is fixed by this dephasing, while a complementary-basis effect is disturbed; a classical bit flip
is a separate failure mode.  Likewise, the paper's “entanglement as a key” language is retained as
an analogy: the existing Bell-resource and decoder theorems prove sufficiency for the named
protocol, not a general entanglement-necessity theorem.

The limitation is executable. `classicallyCorrelatedDensity` is the equal mixture of the two
product computational-basis densities at raw words `00` and `11`. It has the same zero single-Z
moments and unit joint-ZZ moment as `pairDensity 0 0`, including the same nonfactorizing U03
correlation inequality, but an off-diagonal entry proves the two densities unequal. Those three
moments therefore do not by themselves witness entanglement; no general separability predicate is
silently assumed.

For the EPR circuit's transported record, `epr_c34_q4_dephasing_before_comparison_iterate` gives
the precise repeated-measurement substitute: any finite number of nonselective computational
dephasings of `q4`, immediately before the final comparison CNOT, preserves the final paper-one
probability on `q1` for every pre-comparison density. It does not assert equality of global states
or robustness of other observables.

## Reuse

Import `Deutsch.Information.Dephasing` for the generic channel and environment calculation, or
`Deutsch.Decoherence` for the teleportation bridge.  Use `mapDensity` for Schrödinger states and
`dualEffect` for Heisenberg measurement effects; the channel duality theorem relates their Born
probabilities.  Do not reuse coherent identities of the form `U† A U` after inserting dephasing:
the relevant Heisenberg action is the Kraus `dualOperator`.
