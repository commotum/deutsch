import Deutsch.Teleportation.Correctness
import Deutsch.Teleportation.Protocol
import Mathlib.Data.Matrix.PEquiv

/-!
# Literal coherent teleportation channel

This module turns the five-wire coherent circuit into a one-qubit channel.  The channel Kraus
operators are literal matrix slices of `coherentProtocol`: the input wire is initialized together
with four paper-zero ancillary wires, and the four nonreceiver output wires label the discarded
environment.

The resulting operator action is the identity after the canonical reindexing from the semantic
one-qubit message register to the physical receiver singleton.
-/

namespace Deutsch
namespace Teleportation

open Foundations Information Register
open scoped BigOperators ComplexOrder Matrix MatrixOrder

noncomputable section

/-- Canonical identification of the semantic message basis with the physical receiver basis. -/
def messageReceiverBasisEquiv : Basis ProtocolMessage ≃ Basis ReceiverQubit :=
  protocolMessageBasisEquiv.symm.trans (singletonBasisEquiv q5)

/-- Reindex a semantic one-qubit operator onto the physical receiver singleton. -/
def reindexMessageOperator (A : Operator ProtocolMessage) : Operator ReceiverQubit :=
  Matrix.reindexRingEquiv ℂ messageReceiverBasisEquiv A

/-- Place a message basis input on `q1` and initialize all four ancillas to paper zero. -/
def coherentProtocolInputBasis (input : Basis ProtocolMessage) : Basis TeleportQubit :=
  teleportBits (protocolMessageBasisEquiv.symm input) 1 1 1 1

/-- Combine the four discarded output bits with a physical receiver basis assignment. -/
def coherentProtocolOutputBasis
    (junk : Basis JunkQubit) (receiver : Basis ReceiverQubit) :
    Basis TeleportQubit :=
  teleportBits (junk 0) (junk 1) (junk 2) (junk 3)
    ((singletonBasisEquiv q5).symm receiver)

/--
One Kraus matrix obtained directly by fixing the four discarded output wires of the literal
five-wire coherent circuit.
-/
def coherentProtocolKraus (junk : Basis JunkQubit) :
    Matrix (Basis ReceiverQubit) (Basis ProtocolMessage) ℂ :=
  fun receiver input =>
    coherentProtocol
      (coherentProtocolOutputBasis junk receiver)
      (coherentProtocolInputBasis input)

/-- The basis-reindexing isometry from the message register to the receiver singleton. -/
def messageReceiverIsometry :
    Matrix (Basis ReceiverQubit) (Basis ProtocolMessage) ℂ :=
  messageReceiverBasisEquiv.symm.toPEquiv.toMatrix

theorem messageReceiverIsometry_conjTranspose :
    messageReceiverIsometryᴴ =
      messageReceiverBasisEquiv.toPEquiv.toMatrix := by
  ext input receiver
  simp only [messageReceiverIsometry, Matrix.conjTranspose_apply,
    PEquiv.toMatrix_apply]
  split_ifs with hleft hright <;>
    simp_all [eq_comm]

theorem messageReceiverIsometry_conjTranspose_mul :
    messageReceiverIsometryᴴ * messageReceiverIsometry =
      (1 : Operator ProtocolMessage) := by
  ext input output
  rw [Matrix.mul_apply, ← messageReceiverBasisEquiv.sum_comp]
  simp [messageReceiverIsometry, Matrix.conjTranspose_apply,
    PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]

/-- Conjugating by the receiver isometry is exactly matrix reindexing. -/
theorem messageReceiverIsometry_mapOperator (A : Operator ProtocolMessage) :
    messageReceiverIsometry * A * messageReceiverIsometryᴴ =
      reindexMessageOperator A := by
  rw [messageReceiverIsometry_conjTranspose, messageReceiverIsometry,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private def basisInputAlpha (bit : QubitIndex) : ℂ :=
  if bit = 1 then 1 else 0

private def basisInputBeta (bit : QubitIndex) : ℂ :=
  if bit = 0 then 1 else 0

private theorem initializedInputKet_basis (bit : QubitIndex) :
    initializedInputKet (basisInputAlpha bit) (basisInputBeta bit) =
      basisKet (teleportBits bit 1 1 1 1) := by
  fin_cases bit <;>
    simp [basisInputAlpha, basisInputBeta, initializedInputKet]

private theorem act_basisKet_apply
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Operator Q) (output input : Basis Q) :
    act U (basisKet input) output = U output input := by
  change (U *ᵥ Pi.single input 1) output = U output input
  rw [Matrix.mulVec_single_one]
  rfl

private theorem junkBits_eta_bridge (junk : Basis JunkQubit) :
    junkBits (junk 0) (junk 1) (junk 2) (junk 3) = junk := by
  funext q
  fin_cases q <;> rfl

@[simp] private theorem singletonBasisEquiv_symm_receiverBits_bridge
    (bit : QubitIndex) :
    (singletonBasisEquiv q5).symm (receiverBits bit) = bit := rfl

/--
Every literal environment slice of the five-wire circuit is the fixed junk amplitude times the
canonical message-to-receiver isometry.
-/
theorem coherentProtocolKraus_eq (junk : Basis JunkQubit) :
    coherentProtocolKraus junk =
      fixedJunkKet junk • messageReceiverIsometry := by
  ext receiver input
  rw [← protocolMessageBasisEquiv.apply_symm_apply input,
    ← (singletonBasisEquiv q5).apply_symm_apply receiver]
  generalize protocolMessageBasisEquiv.symm input = inputBit
  generalize (singletonBasisEquiv q5).symm receiver = receiverBit
  have hfactor := coherentProtocol_factorizes
    (basisInputAlpha inputBit) (basisInputBeta inputBit)
  rw [initializedInputKet_basis] at hfactor
  have hentry := congrArg
    (fun psi : Ket TeleportQubit =>
      psi (teleportBits (junk 0) (junk 1) (junk 2) (junk 3) receiverBit))
    hfactor
  rw [act_basisKet_apply] at hentry
  fin_cases inputBit <;> fin_cases receiverBit <;>
    simpa [coherentProtocolKraus, coherentProtocolInputBasis,
      coherentProtocolOutputBasis, factorizedOutputKet, receiverInputKet,
      messageReceiverIsometry, messageReceiverBasisEquiv,
      basisInputAlpha, basisInputBeta, junkBits_eta_bridge,
      basisKet, basisVector, receiverBits, Pi.single,
      PEquiv.toMatrix_apply] using hentry

/-- The discarded, input-independent junk amplitudes have total probability one. -/
theorem fixedJunkKet_probability_normalized :
    ∑ junk : Basis JunkQubit,
      star (fixedJunkKet junk) * fixedJunkKet junk = 1 := by
  have h :
      (fun junk => fixedJunkKet junk) ⬝ᵥ
        star (fun junk => fixedJunkKet junk) = 1 := by
    change
      (((2 : ℂ)⁻¹) •
        (-Pi.single (junkBits 0 0 0 0) 1 -
          Pi.single (junkBits 0 0 1 1) 1 -
          Pi.single (junkBits 1 1 0 0) 1 +
          Pi.single (junkBits 1 1 1 1) 1)) ⬝ᵥ
        star (((2 : ℂ)⁻¹) •
          (-Pi.single (junkBits 0 0 0 0) 1 -
            Pi.single (junkBits 0 0 1 1) 1 -
            Pi.single (junkBits 1 1 0 0) 1 +
            Pi.single (junkBits 1 1 1 1) 1)) = 1
    simp [junkBits]
    norm_num
  simpa only [dotProduct, Pi.star_apply, mul_comm] using h

/--
The Kraus channel obtained by initializing the four ancillary wires, applying the literal
five-wire `coherentProtocol`, and discarding the first four output wires.
-/
def coherentProtocolChannel :
    KrausChannel ProtocolMessage ReceiverQubit (Basis JunkQubit) where
  kraus := coherentProtocolKraus
  complete := by
    simp_rw [coherentProtocolKraus_eq, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, ← mul_smul,
      messageReceiverIsometry_conjTranspose_mul]
    rw [← Finset.sum_smul, fixedJunkKet_probability_normalized]
    simp

/-- The literal circuit channel is the identity after message-to-receiver basis reindexing. -/
theorem coherentProtocolChannel_mapOperator (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A = reindexMessageOperator A := by
  simp only [coherentProtocolChannel, KrausChannel.mapOperator]
  simp_rw [coherentProtocolKraus_eq, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    messageReceiverIsometry_mapOperator]
  rw [← Finset.sum_smul]
  rw [show (∑ junk : Basis JunkQubit,
      fixedJunkKet junk * star (fixedJunkKet junk)) = 1 by
        simpa only [mul_comm] using fixedJunkKet_probability_normalized]
  simp

/-- Reindexing preserves positive semidefiniteness. -/
theorem reindexMessageOperator_posSemidef
    {A : Operator ProtocolMessage} (hA : A.PosSemidef) :
    (reindexMessageOperator A).PosSemidef := by
  simpa [reindexMessageOperator, Matrix.reindexRingEquiv] using
    hA.submatrix messageReceiverBasisEquiv.symm

/-- Reindexing preserves the matrix trace. -/
theorem reindexMessageOperator_trace (A : Operator ProtocolMessage) :
    Matrix.trace (reindexMessageOperator A) = Matrix.trace A := by
  unfold reindexMessageOperator Matrix.trace Matrix.diag
  exact Equiv.sum_comp messageReceiverBasisEquiv.symm (fun input => A input input)

/-- Explicit transport of a message density to the physical receiver singleton. -/
def reindexMessageDensity (rho : Density ProtocolMessage) : Density ReceiverQubit where
  op := reindexMessageOperator rho.op
  positive := reindexMessageOperator_posSemidef rho.positive
  trace_one := by rw [reindexMessageOperator_trace, rho.trace_one]

/-- Exact all-density action of the channel induced by the literal coherent circuit. -/
theorem coherentProtocolChannel_mapDensity (rho : Density ProtocolMessage) :
    coherentProtocolChannel.mapDensity rho = reindexMessageDensity rho := by
  apply Density.ext
  exact coherentProtocolChannel_mapOperator rho.op

/-- Explicit transport of a message effect to the physical receiver singleton. -/
def reindexMessageEffect (effect : Effect ProtocolMessage) : Effect ReceiverQubit where
  op := reindexMessageOperator effect.op
  positive := reindexMessageOperator_posSemidef effect.positive
  complement_positive := by
    have h := reindexMessageOperator_posSemidef effect.complement_positive
    have heq :
        reindexMessageOperator (1 - effect.op) =
          1 - reindexMessageOperator effect.op := by
      unfold reindexMessageOperator
      rw [map_sub, map_one]
    rw [← heq]
    exact h

@[simp]
theorem reindexMessageDensity_op (rho : Density ProtocolMessage) :
    (reindexMessageDensity rho).op = reindexMessageOperator rho.op := rfl

@[simp]
theorem reindexMessageEffect_op (effect : Effect ProtocolMessage) :
    (reindexMessageEffect effect).op = reindexMessageOperator effect.op := rfl

/-- Reindexing both a state and an effect preserves its complex Born weight. -/
theorem bornWeight_reindexMessage (rho : Density ProtocolMessage)
    (effect : Effect ProtocolMessage) :
    bornWeight (reindexMessageDensity rho) (reindexMessageEffect effect) =
      bornWeight rho effect := by
  unfold bornWeight
  rw [reindexMessageDensity_op, reindexMessageEffect_op]
  have hmul :
      reindexMessageOperator rho.op * reindexMessageOperator effect.op =
        reindexMessageOperator (rho.op * effect.op) := by
    exact (map_mul
      (Matrix.reindexRingEquiv ℂ messageReceiverBasisEquiv)
      rho.op effect.op).symm
  rw [hmul, reindexMessageOperator_trace]

/-- Every one-qubit effect has the same probability after literal coherent teleportation. -/
theorem coherentProtocolChannel_preserves_all_effects
    (rho : Density ProtocolMessage) (effect : Effect ProtocolMessage) :
    bornProbability (coherentProtocolChannel.mapDensity rho)
        (reindexMessageEffect effect) =
      bornProbability rho effect := by
  rw [coherentProtocolChannel_mapDensity]
  exact congrArg Complex.re (bornWeight_reindexMessage rho effect)

/-- Equivalent prediction form, quantified directly over every physical receiver effect. -/
theorem coherentProtocolChannel_agrees_on_every_receiver_effect
    (rho : Density ProtocolMessage) (effect : Effect ReceiverQubit) :
    bornProbability (coherentProtocolChannel.mapDensity rho) effect =
      bornProbability (reindexMessageDensity rho) effect := by
  rw [coherentProtocolChannel_mapDensity]

/--
The literal five-wire circuit channel and the semantic decoder-after-encoder construction agree
on every operator, after the canonical output reindexing.
-/
theorem coherentProtocolChannel_eq_protocolDecoder_encoder_mapOperator
    (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A =
      reindexMessageOperator
        (protocolDecoder.mapOperator (protocolEncoder.mapOperator A)) := by
  rw [protocolDecoder_encoder_mapOperator]
  exact coherentProtocolChannel_mapOperator A

/-- Density-state form of the literal/semantic channel identification. -/
theorem coherentProtocolChannel_eq_protocolDecoder_encoder_mapDensity
    (rho : Density ProtocolMessage) :
    coherentProtocolChannel.mapDensity rho =
      reindexMessageDensity
        (protocolDecoder.mapDensity (protocolEncoder.mapDensity rho)) := by
  rw [protocolDecoder_encoder_mapDensity]
  exact coherentProtocolChannel_mapDensity rho

/--
The five-wire output operator obtained by placing an arbitrary message operator on `q1`, fixing
the other four input wires to paper zero, and conjugating by the literal coherent protocol.

The displayed finite matrix sum is the entrywise form of that initialized conjugation.
-/
def coherentProtocolFiveWireOutputOperator
    (A : Operator ProtocolMessage) : Operator TeleportQubit :=
  fun output input =>
    ∑ right : Basis ProtocolMessage,
      (∑ left : Basis ProtocolMessage,
        coherentProtocol output (coherentProtocolInputBasis left) * A left right) *
        star (coherentProtocol input (coherentProtocolInputBasis right))

private theorem channelBridgeComplementReceiver_ne_last
    (q : {q : TeleportQubit // q ∉ ({q5} : Finset TeleportQubit)}) :
    q.1 ≠ Fin.last 4 := by
  have hq : q.1 ≠ q5 := by simpa using q.2
  simpa [q5] using hq

private theorem splitBasis_symm_coherentProtocolOutputBasis
    (receiver : Basis ReceiverQubit) (junk : Basis JunkQubit) :
    (splitBasis ({q5} : Finset TeleportQubit)).symm
        (receiver, junkComplementBasisEquiv junk) =
      coherentProtocolOutputBasis junk receiver := by
  rw [← (singletonBasisEquiv q5).apply_symm_apply receiver]
  generalize (singletonBasisEquiv q5).symm receiver = receiverBit
  funext q
  change (if h : q ∈ ({q5} : Finset TeleportQubit) then receiverBit
    else junk
      (Fin.castPred q
        (channelBridgeComplementReceiver_ne_last ⟨q, h⟩))) =
    coherentProtocolOutputBasis junk ((singletonBasisEquiv q5) receiverBit) q
  fin_cases q <;>
    simp [coherentProtocolOutputBasis, q5, teleportBits]
  all_goals congr 1

/--
Discarding the first four wires of the initialized, coherently evolved five-wire operator is
definitionally the Kraus-channel action above.
-/
theorem coherentProtocolChannel_mapOperator_eq_receiverPartialTrace
    (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A =
      partialTrace ({q5} : Finset TeleportQubit)
        (coherentProtocolFiveWireOutputOperator A) := by
  ext receiver output
  simp only [coherentProtocolChannel, KrausChannel.mapOperator,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    partialTrace, splitOperator_apply, coherentProtocolFiveWireOutputOperator]
  rw [← junkComplementBasisEquiv.sum_comp]
  simp_rw [splitBasis_symm_coherentProtocolOutputBasis]
  rfl

end

end Teleportation
end Deutsch
