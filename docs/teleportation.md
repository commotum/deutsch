# Coherent Teleportation, Corrections, and Receiver Semantics

The teleportation layer is split into the [five-wire circuit](../Deutsch/Teleportation/Circuit.lean),
the explicit [three-qubit correction](../Deutsch/Teleportation/Correction.lean), the
[Heisenberg descriptors](../Deutsch/Teleportation/Descriptors.lean), the
[arbitrary-input correctness proof](../Deutsch/Teleportation/Correctness.lean), the
[operational encoder and decoder](../Deutsch/Teleportation/Protocol.lean), and the
[one-parameter source statistics](../Deutsch/Teleportation/Statistics.lean). Focused regression
theorems live in [`DeutschTests.Teleportation`](../DeutschTests/Teleportation.lean).

This page inherits the paper-bit, tensor-order, and Heisenberg conventions from
[Global Conventions](conventions.md), the finite-register embedding API from
[Finite Registers](registers.md), the exact gate chronology from
[Gates, Rotations, and Bell Chronology](gates.md), and the operational density/channel notions
from [Density States, Channels, and Information Dependence](information.md).

## Five wires and coherent chronology

`TeleportQubit = Fin 5` names the source wires `q1` through `q5` in that order. Paper bit `1` is
raw index `0`, and paper bit `0` is raw index `1`; the correction branch names below use paper
bits while Lean basis functions use raw indices. Matrix products act on kets right-to-left.

| Boundary | Compiled operation added in Schrödinger order |
| --- | --- |
| `timeOneUnitary theta` | prepare `q1` with `R_x(theta)` and prepare the inverse-Bell resource on `q4,q5` |
| `timeTwoUnitary theta` | apply the Bell gate with target `q1` and control `q4` |
| `timeThreeUnitary theta` | coherently copy the paper bits of `q1,q4` into record wires `q2,q3` |
| `timeFourUnitary theta` | apply the explicit correction to `q2,q3,q5` |
| `timeFiveUnitary theta` | rotate `q5` by `R_x(-theta)` for the source's final verification |

The boundary operators and every constituent gate have unitarity theorems. The preparation,
Bell, and record gates also expose finite support and the two disjoint layers expose exact
commutation. These are coherent finite-dimensional operations. In particular, the names
“record” and “Bell measurement gate” describe circuit roles; no measurement, collapse,
dephasing, or classical communication is implicit.

## Equation (33): an explicit correction, not an assumption

For distinct coordinates `k,l,m`, the compiled correction is

```text
correctionGate k l m = CZ(l,m) · CNOT(k → m) · Z(k) · Z(l),
```

where `cnotAt m k` uses the project's target-first argument order. `correctionGate_unitary`
proves this matrix is unitary. The nine theorems `equation33_k_x` through `equation33_m_z`
derive its action on all Pauli generators. The four basis-branch theorems separately derive the
paper-labelled receiver corrections:

| Paper record | Receiver branch, including the compiled record phase |
| --- | --- |
| `00` | `I` |
| `01` | `-Z` |
| `10` | `-X` |
| `11` | `ZX` |

Global branch phases are retained in the coherent ket proof. They may be irrelevant to an
isolated conditional ray, but erasing them before recombining coherent branches would be
incorrect.

## Descriptor equations

Under `heisenberg U A = U† A U`, `R_x(theta)` acts by

```text
Y ↦ cos(theta) Y - sin(theta) Z,
Z ↦ sin(theta) Y + cos(theta) Z.
```

The resulting Equation (29) triple is

```text
q1 = (X1,
      cos(theta) Y1 - sin(theta) Z1,
      sin(theta) Y1 + cos(theta) Z1).
```

`equation29_q1` proves this full triple. `equation30_q4` and `equation30_q5` derive the resource
descriptors exactly. `equation31_q1`, `equation31_q4`, `equation32_q2`, and `equation32_q3` then
derive the Bell and record expressions from the same unitary chronology.

`equation34_q5` derives the receiver triple after the explicit Equation (33) gate, and
`timeFive_q5_z` derives the final Equation (37) verification observable. These are operator
equalities. The fixed-reference expectation and Born-probability results below are proved
separately, so one-state statistics are not substituted for operator identities.

## Exact arbitrary-input transfer

`initializedInputKet alpha beta` places
`alpha |paper 0⟩ + beta |paper 1⟩` on `q1` and initializes the other four wires in their
paper-zero basis states. `coherentProtocol` is the parameter-free resource, Bell, record, and
correction circuit. The principal theorem is

```text
coherentProtocol_factorizes alpha beta:
  coherentProtocol (initializedInputKet alpha beta)
    = fixedJunkKet ⊗ (alpha |paper 0⟩ + beta |paper 1⟩) on q5.
```

Here the tensor product is represented by the exact coordinate function
`factorizedOutputKet`; it contains no hidden basis permutation or residual global phase. The
proof expands the pre-correction state, applies the explicit correction gate on all coherent
branches, and then proves the coordinatewise factorization. It does not infer purity or transfer
from an identity expectation.

For normalized amplitudes, `teleportedDensity_reduce_receiver` strengthens the ket result to an
exact reduced-density identity on the actual singleton `{q5}`. Therefore every receiver effect,
not merely the three Pauli moments displayed by the source, has the input-state probability.

The coherent factorization is proved for every pair of complex amplitudes; normalization is
needed only when packaging those amplitudes as `PureState` and `Density`. No external reference
system is included in this five-wire theorem. The separate semantic channel theorem below is an
identity on every one-qubit operator and density, but this stage does not claim a compiled
`identity ⊗ id_reference` theorem for an arbitrary entangled reference.

## Operational encoder, decoder, and information boundaries

`ProtocolMessage = Fin 1` is a semantic one-qubit input register, while `ProtocolQubit = Fin 3`
contains two record coordinates and one encrypted receiver. `protocolBranchCorrection` packages
the four matrices above, and `protocolCorrectionGate_eq_branch_on_basis` connects each matrix to
the explicit Equation (33) circuit rather than postulating a decoder.

`protocolEncoder` uniformly embeds a message into the four record blocks, with the receiver
encrypted by the adjoint branch. `protocolDecoder` applies the branch correction and discards the
records. `protocolDecoder_encoder_mapOperator` proves equality with every input operator;
`protocolDecoder_encoder_mapDensity` and `protocolDecoder_recovers` expose the corresponding
density and operational-recovery statements.

For the explicit two-input basis family, `protocolEncodedFamily_reduce_singleton` proves that
each record coordinate and the receiver is maximally mixed. Consequently
`protocolEncodedFamily_locallyStatisticsIndependent` quantifies independence of every singleton
effect statistic. This local statement coexists with two distinct joint statements:
`protocolEncodedFamily_recordK_receiver_jointlyDetectable` gives an exact detecting subsystem,
while `protocolEncodedFamily_jointRegister_statisticallyDetectable` derives full-register
detectability from the physical decoder and its recovery theorem.

The correction-bit boundary is also explicit. In addition to the nonidentity branch matrices,
`protocol_omit_recordK_changes_receiver_z_observable` proves that the paper-`10` branch changes
the receiver `Z` observable, while `protocol_omit_recordL_changes_receiver_x_observable` proves
that the paper-`01` branch changes `X`. These are scoped operational witnesses, not generic
channel-capacity or necessity claims. `protocolPreparation` carries supplied input and endpoint
metadata; `protocolPreparation_supplied_transport` exposes its explicitly stored Alice-to-Bob
route, and `protocolPreparation_provenanceNonconstant` proves that its input metadata varies.
Neither theorem infers a route or history from the final density operator.

This semantic encoder is a separately constructed, uniformly weighted branch model used to state
channel properties cleanly. Its branch corrections are tied to the explicit Equation (33) gate,
but this stage does not prove that the whole encoder equals the coherent five-wire pre-correction
circuit followed by a dephasing/discard operation. The five-wire source circuit remains a
coherent unitary model. An explicit bridge through a measurement/dephasing environment belongs to
the next layer; without it, the coherent record wires are not called measured or classical.

## Equations (35)--(36) and final verification

For the source family `R_x(theta)|paper 0⟩`, the compiled amplitudes are

```text
alpha = cos(theta/2),
beta  = -i sin(theta/2).
```

`timeFour_act_reference_factorizes` specializes arbitrary-input transfer to this circuit.
`equation36_receiver_density` gives the receiver Bloch vector through exact density equality, and
`equation36_receiver_all_effects` upgrades it to every receiver effect. The vector is
`(0, +sin(theta), -cos(theta))` under the fixed paper-bit convention.
`equation35_receiver_purity` separately computes purity `1`, so certainty is not being inferred
from the identity effect.

`equation35Effect` is the Equation (35) receiver effect, and `equation35_effect_op` exposes its
operator as

```text
(I + sin(theta) q5y - cos(theta) q5z) / 2.
```

`equation35_receiver_probability_one` proves certainty on the singleton receiver density, while
`equation35_teleported_probability_one` proves the embedded five-wire form. The final verification
is proved both for the evolved five-wire density and for the literal `timeFiveUnitary` reference
output by `timeFive_teleported_paperZero_probability_one` and
`timeFive_reference_output_paperZero_probability_one`. The tested effect is pinned to the
paper-zero projector by `receiverPaperZeroEffect_op_eq_projector`. These probability theorems are
separate from the Equation (37) operator identity, preserving the distinction between an
operator equality and a fixed-reference expectation.

## Exact scope and exclusions

The layer establishes exact finite matrices, coherent state transfer, receiver reduction,
all-effect equality, an explicit correction realization, and exact operational recovery in a
finite channel model. It does not yet establish:

- a measurement instrument, conditioned post-measurement state, collapse rule, or classical
  communication event;
- an environment interaction, pointer basis, redundant record, decoherence timescale, or
  robustness to noise;
- a generic arbitrary-reference tensor extension of the identity channel;
- a continuum spacetime propagation theorem or an ontological location of information.

Those distinctions are deliberate. Descriptor parameter occurrence, local statistical
independence, joint detectability, channel recovery, and supplied preparation history are
different predicates and are not substituted for one another.
