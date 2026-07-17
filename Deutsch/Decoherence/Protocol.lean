import Deutsch.Information.Dephasing
import Deutsch.Teleportation.Protocol

/-!
# Computational-record dephasing for the teleportation branch model

The semantic teleportation encoder has two designated computational record coordinates, `0` and
`1`, and a receiver coordinate `2`.  This module dephases only the records.  It does not dephase
the receiver and does not identify the semantic encoder with a discarded five-wire coherent
circuit.
-/

namespace Deutsch
namespace Decoherence

open Foundations Gates Information Register Teleportation
open scoped Matrix BigOperators

noncomputable section

/-- Sequential nonselective computational-basis dephasing of the two protocol records. -/
def protocolRecordDephasing :
    KrausChannel ProtocolQubit ProtocolQubit (QubitIndex × QubitIndex) :=
  (coordinateDephasing (1 : ProtocolQubit)).comp
    (coordinateDephasing (0 : ProtocolQubit))

/-- Record dephasing retains exactly matrix entries agreeing on both record coordinates. -/
theorem protocolRecordDephasing_mapOperator_apply
    (A : Operator ProtocolQubit) (x y : Basis ProtocolQubit) :
    protocolRecordDephasing.mapOperator A x y =
      if x 0 = y 0 ∧ x 1 = y 1 then A x y else 0 := by
  rw [protocolRecordDephasing, KrausChannel.comp_mapOperator,
    coordinateDephasing_mapOperator_apply,
    coordinateDephasing_mapOperator_apply]
  by_cases h0 : x 0 = y 0 <;> by_cases h1 : x 1 = y 1 <;>
    simp [h0, h1]

private theorem protocolEncoder_kraus_apply_eq_zero_of_record_ne
    (record : ProtocolRecord) (output : Basis ProtocolQubit)
    (input : Basis ProtocolMessage)
    (hrecord : output 0 ≠ record.1 ∨ output 1 ≠ record.2) :
    protocolEncoder.kraus record output input = 0 := by
  rcases hrecord with hrecord | hrecord
  · simp [protocolEncoder, protocolEncoderKraus, protocolBranchIsometry, hrecord]
  · simp [protocolEncoder, protocolEncoderKraus, protocolBranchIsometry, hrecord]

private theorem protocolEncoder_mapOperator_apply_of_record_ne
    (A : Operator ProtocolMessage) (x y : Basis ProtocolQubit)
    (hrecord : x 0 ≠ y 0 ∨ x 1 ≠ y 1) :
    protocolEncoder.mapOperator A x y = 0 := by
  classical
  rw [KrausChannel.mapOperator, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro record _
  by_cases hx : x 0 = record.1 ∧ x 1 = record.2
  · have hy : y 0 ≠ record.1 ∨ y 1 ≠ record.2 := by
      rcases hrecord with hK | hL
      · exact Or.inl (fun hyK => hK (hx.1.trans hyK.symm))
      · exact Or.inr (fun hyL => hL (hx.2.trans hyL.symm))
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro intermediate _
    rw [Matrix.conjTranspose_apply,
      protocolEncoder_kraus_apply_eq_zero_of_record_ne
        record y intermediate hy]
    simp
  · have hx' : x 0 ≠ record.1 ∨ x 1 ≠ record.2 := not_and_or.mp hx
    have hleft (intermediate : Basis ProtocolMessage) :
        (protocolEncoder.kraus record * A) x intermediate = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro message _
      rw [protocolEncoder_kraus_apply_eq_zero_of_record_ne
        record x message hx']
      simp
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro intermediate _
    rw [hleft]
    simp

/-- Every encoded operator is already block diagonal in the two record coordinates. -/
theorem protocolRecordDephasing_encoder_mapOperator
    (A : Operator ProtocolMessage) :
    protocolRecordDephasing.mapOperator (protocolEncoder.mapOperator A) =
      protocolEncoder.mapOperator A := by
  ext x y
  rw [protocolRecordDephasing_mapOperator_apply]
  by_cases hrecord : x 0 = y 0 ∧ x 1 = y 1
  · rw [if_pos hrecord]
  · rw [if_neg hrecord]
    exact (protocolEncoder_mapOperator_apply_of_record_ne A x y
      (not_and_or.mp hrecord)).symm

/-- Record-only dephasing fixes every density encoded by the semantic encoder. -/
theorem protocolRecordDephasing_encoder_mapDensity
    (rho : Density ProtocolMessage) :
    protocolRecordDephasing.mapDensity (protocolEncoder.mapDensity rho) =
      protocolEncoder.mapDensity rho := by
  apply Density.ext
  exact protocolRecordDephasing_encoder_mapOperator rho.op

/-- Exact decoder recovery survives the named, record-basis dephasing channel. -/
theorem protocolDecoder_after_recordDephasing
    (rho : Density ProtocolMessage) :
    protocolDecoder.mapDensity
        (protocolRecordDephasing.mapDensity (protocolEncoder.mapDensity rho)) =
      rho := by
  rw [protocolRecordDephasing_encoder_mapDensity,
    protocolDecoder_encoder_mapDensity]

/-! ## A classical record-bit error -/

/-- A real unitary/Kraus error channel that flips the first transmitted record bit. -/
def protocolRecordKBitFlip :
    KrausChannel ProtocolQubit ProtocolQubit Unit :=
  unitaryChannel (xAt (0 : ProtocolQubit)) (xAt_unitary 0)

/-- Raw computational assignment obtained by flipping one named coordinate. -/
private def flipAssignment {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (bits : Basis Q) : Basis Q :=
  Function.update bits q (flipRaw (bits q))

private theorem xAt_apply_eq_flipAssignment
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (output input : Basis Q) :
    xAt q output input = if output = flipAssignment q input then 1 else 0 := by
  rw [xAt, embedQubit_apply_ite]
  by_cases houtside : ∀ j, j ≠ q → output j = input j
  · rw [if_pos houtside]
    by_cases houtput : output = flipAssignment q input
    · subst output
      rw [if_pos rfl]
      generalize hinput : input q = inputBit
      fin_cases inputBit <;> simp_all [flipAssignment, flipRaw, pauliX]
    · rw [if_neg houtput]
      have hq : output q ≠ flipRaw (input q) := by
        intro hq
        apply houtput
        funext j
        by_cases hj : j = q
        · subst j
          simp [flipAssignment, hq]
        · simpa [flipAssignment, Function.update_of_ne hj] using houtside j hj
      generalize houtputBit : output q = outputBit at hq ⊢
      generalize hinputBit : input q = inputBit at hq ⊢
      fin_cases outputBit <;> fin_cases inputBit <;>
        simp_all [flipRaw, pauliX]
  · rw [if_neg houtside, if_neg]
    intro houtput
    subst output
    apply houtside
    intro j hj
    simp [flipAssignment, Function.update_of_ne hj]

private theorem mul_basisDensity_mul_conjTranspose_apply
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (K : Operator Q) (bits output input : Basis Q) :
    (K * (basisDensity bits).op * Kᴴ) output input =
      K output bits * star (K input bits) := by
  rw [show (basisDensity bits).op = Matrix.single bits bits 1 by
    exact Matrix.diagonal_single bits 1]
  simp only [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply]
  rw [Fintype.sum_eq_single bits]
  · rw [Fintype.sum_eq_single bits]
    · simp
    · intro other hother
      simp [Ne.symm hother]
  · intro other hother
    simp [Ne.symm hother]

private theorem basisDensity_apply
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (bits output input : Basis Q) :
    (basisDensity bits).op output input =
      if output = bits ∧ input = bits then 1 else 0 := by
  change Matrix.diagonal (Pi.single bits 1) output input = _
  rw [Matrix.diagonal_apply]
  by_cases heq : output = input
  · subst input
    by_cases hbits : output = bits
    · subst output
      simp [Pi.single]
    · simp [Pi.single, hbits]
  · rw [if_neg heq]
    rw [if_neg]
    intro hbits
    exact heq (hbits.1.trans hbits.2.symm)

/-- A Pauli-X unitary channel sends a computational density to the flipped assignment. -/
private theorem unitaryX_map_basisDensity
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (bits : Basis Q) :
    (unitaryChannel (xAt q) (xAt_unitary q)).mapDensity
        (basisDensity bits) =
      basisDensity (flipAssignment q bits) := by
  apply Density.ext
  ext output input
  change (unitaryChannel (xAt q) (xAt_unitary q)).mapOperator
      (basisDensity bits).op output input = _
  rw [unitaryChannel_mapOperator]
  rw [mul_basisDensity_mul_conjTranspose_apply,
    xAt_apply_eq_flipAssignment, xAt_apply_eq_flipAssignment,
    basisDensity_apply]
  by_cases hout : output = flipAssignment q bits <;>
    by_cases hin : input = flipAssignment q bits <;> simp [hout, hin]

private theorem channel_mapOperator_fintype_sum
    {Q R K I : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] [Fintype K] [Fintype I]
    (channel : KrausChannel Q R K) (f : I → Operator Q) :
    channel.mapOperator (∑ i, f i) = ∑ i, channel.mapOperator (f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, channel.mapOperator_add, ih,
        Finset.sum_insert ha]

private theorem flipAssignment_protocolEncodedBits_encrypted
    (record : ProtocolRecord) (bit : QubitIndex) :
    flipAssignment (0 : ProtocolQubit)
        (protocolEncodedBits record (protocolEncryptedReceiver record bit)) =
      protocolEncodedBits (flipRaw record.1, record.2)
        (protocolEncryptedReceiver (flipRaw record.1, record.2) (flipRaw bit)) := by
  rcases record with ⟨recordK, recordL⟩
  fin_cases recordK <;> fin_cases recordL <;> fin_cases bit <;>
    funext q <;> fin_cases q <;>
    simp [flipAssignment, flipRaw, protocolEncodedBits,
      protocolEncryptedReceiver]

/-- Flipping record `k` turns either encoded basis input into the opposite encoded input. -/
theorem protocolRecordKBitFlip_encodedFamily (bit : QubitIndex) :
    protocolRecordKBitFlip.mapDensity (protocolEncodedFamily bit) =
      protocolEncodedFamily (flipRaw bit) := by
  apply Density.ext
  change protocolRecordKBitFlip.mapOperator (protocolEncodedFamily bit).op = _
  rw [protocolEncodedFamily_operator, protocolEncodedFamily_operator,
    channel_mapOperator_fintype_sum]
  simp_rw [KrausChannel.mapOperator_smul]
  have hbasis (record : ProtocolRecord) :
      protocolRecordKBitFlip.mapOperator
          (basisDensity
            (protocolEncodedBits record
              (protocolEncryptedReceiver record bit))).op =
        (basisDensity
          (flipAssignment (0 : ProtocolQubit)
            (protocolEncodedBits record
              (protocolEncryptedReceiver record bit)))).op := by
    exact congrArg Density.op
      (unitaryX_map_basisDensity (0 : ProtocolQubit)
        (protocolEncodedBits record
          (protocolEncryptedReceiver record bit)))
  simp_rw [hbasis, flipAssignment_protocolEncodedBits_encrypted]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases bit <;>
    simp [flipRaw, protocolEncodedBits, protocolEncryptedReceiver]
  all_goals module

/-- A first-record bit error makes the exact decoder return the opposite basis input. -/
theorem protocolDecoder_after_recordKBitFlip (bit : QubitIndex) :
    protocolDecoder.mapDensity
        (protocolRecordKBitFlip.mapDensity (protocolEncodedFamily bit)) =
      protocolInputFamily (flipRaw bit) := by
  rw [protocolRecordKBitFlip_encodedFamily,
    protocolDecoder_recovers_inputFamily]

/-- Explicit recovery failure: a flipped classical record changes raw input `0` into raw `1`. -/
theorem protocolDecoder_after_recordKBitFlip_fails :
    protocolDecoder.mapDensity
        (protocolRecordKBitFlip.mapDensity (protocolEncodedFamily 0)) ≠
      protocolInputFamily 0 := by
  rw [protocolDecoder_after_recordKBitFlip]
  intro h
  have hop := congrArg Density.op h
  have hentry := congrArg
    (fun A : Operator ProtocolMessage ↦
      A (protocolMessageBits 1) (protocolMessageBits 1)) hop
  norm_num [protocolInputFamily, basisDensity, protocolMessageBits,
    Pi.single] at hentry

end
end Decoherence
end Deutsch
