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

end

end Teleportation
end Deutsch
