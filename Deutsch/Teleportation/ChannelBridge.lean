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
open scoped BigOperators Matrix

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
    simp_all [Equiv.symm_apply_eq, eq_comm]

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

end

end Teleportation
end Deutsch
