import Deutsch.Teleportation.Correction
import Deutsch.Information.Dependence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Operational recovery semantics for coherent teleportation

This module packages the four computational branches proved for `correctionGate` into a
finite-dimensional encoder/decoder model.  Raw record index `0` is paper bit `1`, as throughout
the project.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Information Register
open scoped ComplexOrder Matrix MatrixOrder BigOperators

noncomputable section

/-- The one-qubit message register used by the semantic encoder. -/
abbrev ProtocolMessage := Fin 1

/-- Two record coordinates followed by one receiver coordinate. -/
abbrev ProtocolQubit := Fin 3

/-- Raw values of the two paper record bits `(k,l)`. -/
abbrev ProtocolRecord := QubitIndex × QubitIndex

/-- Computational basis of the one-qubit message register. -/
def protocolMessageBits (bit : QubitIndex) : Basis ProtocolMessage :=
  ![bit]

/-- Computational basis of the two-record-plus-receiver register. -/
def protocolEncodedBits (record : ProtocolRecord) (receiver : QubitIndex) :
    Basis ProtocolQubit :=
  ![record.1, record.2, receiver]

@[simp] theorem protocolMessageBits_zero (bit : QubitIndex) :
    protocolMessageBits bit 0 = bit := rfl

@[simp] theorem protocolEncodedBits_recordK
    (record : ProtocolRecord) (receiver : QubitIndex) :
    protocolEncodedBits record receiver 0 = record.1 := rfl

@[simp] theorem protocolEncodedBits_recordL
    (record : ProtocolRecord) (receiver : QubitIndex) :
    protocolEncodedBits record receiver 1 = record.2 := rfl

@[simp] theorem protocolEncodedBits_receiver
    (record : ProtocolRecord) (receiver : QubitIndex) :
    protocolEncodedBits record receiver 2 = receiver := rfl

/--
The exact one-qubit branch selected by `correctionGate`, including its record-dependent scalar.
Up to that scalar, this is `Z^l X^k` in paper bits.
-/
def protocolBranchCorrection (record : ProtocolRecord) : QubitMatrix :=
  (rawZPhase record.1 * rawZPhase record.2) •
    ((if record.2 = 0 then pauliZ else identity₂) *
      (if record.1 = 0 then pauliX else identity₂))

@[simp]
theorem protocolBranchCorrection_paper00 :
    protocolBranchCorrection (1, 1) = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [protocolBranchCorrection, rawZPhase, identity₂, pauliX, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem protocolBranchCorrection_paper01 :
    protocolBranchCorrection (1, 0) = -pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [protocolBranchCorrection, rawZPhase, identity₂, pauliX, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem protocolBranchCorrection_paper10 :
    protocolBranchCorrection (0, 1) = -pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [protocolBranchCorrection, rawZPhase, identity₂, pauliX, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem protocolBranchCorrection_paper11 :
    protocolBranchCorrection (0, 0) = pauliZ * pauliX := by
  simp [protocolBranchCorrection, rawZPhase]

theorem protocolBranchCorrection_unitary (record : ProtocolRecord) :
    protocolBranchCorrection record ∈
      Matrix.unitaryGroup QubitIndex ℂ := by
  have hZ : (if record.2 = 0 then pauliZ else identity₂) ∈
      Matrix.unitaryGroup QubitIndex ℂ := by
    split_ifs
    · exact pauliZ_unitary
    · rw [identity₂]
      exact (Matrix.unitaryGroup QubitIndex ℂ).one_mem
  have hX : (if record.1 = 0 then pauliX else identity₂) ∈
      Matrix.unitaryGroup QubitIndex ℂ := by
    split_ifs
    · exact pauliX_unitary
    · rw [identity₂]
      exact (Matrix.unitaryGroup QubitIndex ℂ).one_mem
  have hphase : star (rawZPhase record.1 * rawZPhase record.2) *
      (rawZPhase record.1 * rawZPhase record.2) = 1 := by
    rcases record with ⟨recordK, recordL⟩
    fin_cases recordK <;> fin_cases recordL <;> norm_num [rawZPhase]
  have hproduct := (Matrix.unitaryGroup QubitIndex ℂ).mul_mem hZ hX
  have hproductCT :
      ((if record.2 = 0 then pauliZ else identity₂) *
          (if record.1 = 0 then pauliX else identity₂))ᴴ *
        ((if record.2 = 0 then pauliZ else identity₂) *
          (if record.1 = 0 then pauliX else identity₂)) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hproduct.1
  rw [Matrix.mem_unitaryGroup_iff']
  change (protocolBranchCorrection record)ᴴ *
    protocolBranchCorrection record = 1
  rw [protocolBranchCorrection, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← mul_smul, hphase,
    one_smul, hproductCT]

/-- Equation (33)'s correction gate on the semantic three-coordinate register. -/
def protocolCorrectionGate : Operator ProtocolQubit :=
  correctionGate (0 : ProtocolQubit) 1 2 (by decide) (by decide) (by decide)

private theorem embedQubit_act_basisKet_expansion
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (A : QubitMatrix) (input : Basis Q) :
    act (embedQubit q A) (basisKet input) =
      A 0 (input q) • basisKet (Function.update input q 0) +
        A 1 (input q) • basisKet (Function.update input q 1) := by
  apply WithLp.ofLp_injective
  change embedQubit q A *ᵥ Pi.single input 1 =
    A 0 (input q) • Pi.single (Function.update input q 0) 1 +
      A 1 (input q) • Pi.single (Function.update input q 1) 1
  rw [Matrix.mulVec_single_one]
  funext output
  change embedQubit q A output input =
    A 0 (input q) *
        (Pi.single (Function.update input q 0) (1 : ℂ) : CoordinateVector Q) output +
      A 1 (input q) *
        (Pi.single (Function.update input q 1) (1 : ℂ) : CoordinateVector Q) output
  rw [embedQubit_apply_ite]
  by_cases hoff : ∀ j, j ≠ q → output j = input j
  · rw [if_pos hoff]
    have hout : output = Function.update input q (output q) := by
      funext j
      by_cases hj : j = q
      · subst j
        simp
      · simp [Function.update_of_ne hj, hoff j hj]
    have hupdate : Function.update input q 0 ≠ Function.update input q 1 := by
      intro h
      have hq := congrFun h q
      simp at hq
    rw [hout]
    generalize output q = outputBit
    generalize input q = inputBit
    fin_cases outputBit <;> fin_cases inputBit <;>
      simp [Pi.single, hupdate, hupdate.symm]
  · rw [if_neg hoff]
    have hne0 : output ≠ Function.update input q 0 := by
      intro h
      apply hoff
      intro j hj
      rw [h]
      simp [Function.update_of_ne hj]
    have hne1 : output ≠ Function.update input q 1 := by
      intro h
      apply hoff
      intro j hj
      rw [h]
      simp [Function.update_of_ne hj]
    simp [Pi.single, hne0, hne1]

private theorem protocolBranchCorrection_act_encodedBits
    (record : ProtocolRecord) (receiver : QubitIndex) :
    act (embedQubit (2 : ProtocolQubit) (protocolBranchCorrection record))
        (basisKet (protocolEncodedBits record receiver)) =
      correctionBasisPhase (0 : ProtocolQubit) 1 2
          (protocolEncodedBits record receiver) •
        basisKet (correctionBasisOutput (0 : ProtocolQubit) 2
          (protocolEncodedBits record receiver)) := by
  rw [embedQubit_act_basisKet_expansion]
  rcases record with ⟨recordK, recordL⟩
  fin_cases recordK <;> fin_cases recordL <;> fin_cases receiver <;>
    simp [protocolBranchCorrection, correctionBasisPhase,
      correctionBasisOutput, controlledZPhase, rawZPhase, cnotOutput,
      protocolEncodedBits, identity₂, pauliX, pauliZ, flipRaw]

/--
The branch matrices used below are not postulated decoders: on every computational branch they
are exactly the action of the explicit `correctionGate` circuit.
-/
theorem protocolCorrectionGate_eq_branch_on_basis
    (record : ProtocolRecord) (receiver : QubitIndex) :
    act protocolCorrectionGate
        (basisKet (protocolEncodedBits record receiver)) =
      act (embedQubit (2 : ProtocolQubit) (protocolBranchCorrection record))
        (basisKet (protocolEncodedBits record receiver)) := by
  rw [protocolCorrectionGate, correctionGate_act_basisKet,
    protocolBranchCorrection_act_encodedBits]

/-- Every three-coordinate basis word is uniquely a record pair and receiver bit. -/
def protocolEncodedBasisEquiv :
    ProtocolRecord × QubitIndex ≃ Basis ProtocolQubit where
  toFun rb := protocolEncodedBits rb.1 rb.2
  invFun bits := ((bits 0, bits 1), bits 2)
  left_inv rb := by
    rcases rb with ⟨⟨recordK, recordL⟩, receiver⟩
    rfl
  right_inv bits := by
    funext q
    fin_cases q <;> rfl

@[simp] theorem protocolEncodedBits_eq_iff
    (first second : ProtocolRecord) (left right : QubitIndex) :
    protocolEncodedBits first left = protocolEncodedBits second right ↔
      first = second ∧ left = right := by
  change protocolEncodedBasisEquiv (first, left) =
      protocolEncodedBasisEquiv (second, right) ↔ _
  rw [protocolEncodedBasisEquiv.injective.eq_iff]
  simp

/-- Every one-coordinate basis word is uniquely its raw bit. -/
def protocolMessageBasisEquiv : QubitIndex ≃ Basis ProtocolMessage where
  toFun := protocolMessageBits
  invFun bits := bits 0
  left_inv _ := rfl
  right_inv bits := by
    funext q
    fin_cases q
    rfl

/--
Isometric embedding into one fixed record block.  The receiver is encrypted by the adjoint of
the exact correction branch, so applying that branch later recovers the message.
-/
def protocolBranchIsometry (record : ProtocolRecord) :
    Matrix (Basis ProtocolQubit) (Basis ProtocolMessage) ℂ :=
  fun output input ↦
    if output 0 = record.1 ∧ output 1 = record.2 then
      (protocolBranchCorrection record)ᴴ (output 2) (input 0)
    else 0

private theorem protocolBranchIsometry_star_mul
    (record : ProtocolRecord) :
    (protocolBranchIsometry record)ᴴ * protocolBranchIsometry record = 1 := by
  ext input output
  rw [Matrix.mul_apply, ← protocolEncodedBasisEquiv.sum_comp,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← protocolMessageBasisEquiv.apply_symm_apply input,
    ← protocolMessageBasisEquiv.apply_symm_apply output]
  generalize protocolMessageBasisEquiv.symm input = inputBit
  generalize protocolMessageBasisEquiv.symm output = outputBit
  rcases record with ⟨recordK, recordL⟩
  fin_cases recordK <;> fin_cases recordL <;>
    fin_cases inputBit <;> fin_cases outputBit <;>
    norm_num [protocolEncodedBasisEquiv, protocolMessageBasisEquiv,
      protocolMessageBits, protocolBranchIsometry, protocolBranchCorrection, rawZPhase,
      identity₂, pauliX, pauliZ, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

private theorem protocolBranchIsometry_star_mul_of_ne
    (first second : ProtocolRecord) (hne : first ≠ second) :
    (protocolBranchIsometry first)ᴴ * protocolBranchIsometry second = 0 := by
  ext input output
  rw [Matrix.mul_apply, ← protocolEncodedBasisEquiv.sum_comp,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← protocolMessageBasisEquiv.apply_symm_apply input,
    ← protocolMessageBasisEquiv.apply_symm_apply output]
  generalize protocolMessageBasisEquiv.symm input = inputBit
  generalize protocolMessageBasisEquiv.symm output = outputBit
  rcases first with ⟨firstK, firstL⟩
  rcases second with ⟨secondK, secondL⟩
  fin_cases firstK <;> fin_cases firstL <;>
    fin_cases secondK <;> fin_cases secondL <;>
    fin_cases inputBit <;> fin_cases outputBit <;>
    simp_all [protocolEncodedBasisEquiv, protocolMessageBasisEquiv,
      protocolMessageBits, protocolBranchIsometry, protocolBranchCorrection,
      rawZPhase, identity₂, pauliX, pauliZ, Matrix.conjTranspose_apply]

set_option maxHeartbeats 400000 in
private theorem protocolBranchIsometry_sum_mul_star :
    ∑ record : ProtocolRecord,
      protocolBranchIsometry record * (protocolBranchIsometry record)ᴴ = 1 := by
  ext output input
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp_rw [Matrix.mul_apply, ← protocolMessageBasisEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [← protocolEncodedBasisEquiv.apply_symm_apply output,
    ← protocolEncodedBasisEquiv.apply_symm_apply input]
  generalize protocolEncodedBasisEquiv.symm output = outputData
  generalize protocolEncodedBasisEquiv.symm input = inputData
  rcases outputData with ⟨⟨outputK, outputL⟩, outputReceiver⟩
  rcases inputData with ⟨⟨inputK, inputL⟩, inputReceiver⟩
  fin_cases outputK <;> fin_cases outputL <;> fin_cases outputReceiver <;>
    fin_cases inputK <;> fin_cases inputL <;> fin_cases inputReceiver <;>
    norm_num [protocolEncodedBasisEquiv, protocolMessageBasisEquiv,
      protocolMessageBits, protocolBranchIsometry, protocolBranchCorrection,
      rawZPhase, identity₂, pauliX, pauliZ, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]

/-- One of four equally weighted encryption isometries. -/
def protocolEncoderKraus (record : ProtocolRecord) :
    Matrix (Basis ProtocolQubit) (Basis ProtocolMessage) ℂ :=
  (2 : ℂ)⁻¹ • protocolBranchIsometry record

private theorem protocolEncoderKraus_star_mul
    (record : ProtocolRecord) :
    (protocolEncoderKraus record)ᴴ * protocolEncoderKraus record =
      (4 : ℂ)⁻¹ • (1 : Operator ProtocolMessage) := by
  rw [protocolEncoderKraus, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← mul_smul,
    protocolBranchIsometry_star_mul]
  norm_num

/-- Uniform four-branch quantum one-time-pad encoder induced by the correction circuit. -/
def protocolEncoder :
    KrausChannel ProtocolMessage ProtocolQubit ProtocolRecord where
  kraus := protocolEncoderKraus
  complete := by
    simp_rw [protocolEncoderKraus_star_mul]
    rw [← Finset.sum_smul]
    norm_num [Fintype.sum_prod_type]

/-- Branch-controlled correction followed by discarding the two record coordinates. -/
def protocolDecoder :
    KrausChannel ProtocolQubit ProtocolMessage ProtocolRecord where
  kraus record := (protocolBranchIsometry record)ᴴ
  complete := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      protocolBranchIsometry_sum_mul_star

private theorem protocolDecoder_mul_encoderKraus
    (decoded encoded : ProtocolRecord) :
    protocolDecoder.kraus decoded * protocolEncoder.kraus encoded =
      if decoded = encoded then
        (2 : ℂ)⁻¹ • (1 : Operator ProtocolMessage)
      else 0 := by
  change (protocolBranchIsometry decoded)ᴴ *
      ((2 : ℂ)⁻¹ • protocolBranchIsometry encoded) = _
  rw [Matrix.mul_smul]
  by_cases h : decoded = encoded
  · subst decoded
    rw [if_pos rfl, protocolBranchIsometry_star_mul]
  · rw [if_neg h, protocolBranchIsometry_star_mul_of_ne decoded encoded h,
      smul_zero]

/-- The physical decoder after the physical four-branch encoder is the identity superoperator. -/
theorem protocolDecoder_encoder_mapOperator (A : Operator ProtocolMessage) :
    protocolDecoder.mapOperator (protocolEncoder.mapOperator A) = A := by
  rw [← protocolDecoder.comp_mapOperator protocolEncoder]
  classical
  simp only [KrausChannel.mapOperator, KrausChannel.comp,
    Fintype.sum_prod_type]
  simp_rw [protocolDecoder_mul_encoderKraus]
  simp
  module

/-- Exact recovery of every one-qubit density state. -/
theorem protocolDecoder_encoder_mapDensity (rho : Density ProtocolMessage) :
    protocolDecoder.mapDensity (protocolEncoder.mapDensity rho) = rho := by
  apply Density.ext
  exact protocolDecoder_encoder_mapOperator rho.op

/-- Exact recovery in the project's operational `Recovers` API. -/
theorem protocolDecoder_recovers :
    Recovers protocolDecoder.mapDensity
      (fun rho : Density ProtocolMessage ↦ protocolEncoder.mapDensity rho)
      (fun rho ↦ rho) := by
  intro rho
  exact protocolDecoder_encoder_mapDensity rho

/-- The identity superoperator result in particular preserves the paper reference density. -/
theorem protocolDecoder_encoder_reference :
    protocolDecoder.mapDensity
        (protocolEncoder.mapDensity (referenceDensity ProtocolMessage)) =
      referenceDensity ProtocolMessage :=
  protocolDecoder_encoder_mapDensity _

/-- The receiver bit before correction; record `k` selects whether it is flipped. -/
def protocolEncryptedReceiver (record : ProtocolRecord) (bit : QubitIndex) :
    QubitIndex :=
  if record.1 = 0 then flipRaw bit else bit

/-- The unit-modulus scalar on the encrypted receiver basis ket. -/
def protocolEncryptionAmplitude (record : ProtocolRecord) (bit : QubitIndex) : ℂ :=
  (protocolBranchCorrection record)ᴴ
    (protocolEncryptedReceiver record bit) bit

private theorem protocolEncryptionAmplitude_mul_star
    (record : ProtocolRecord) (bit : QubitIndex) :
    protocolEncryptionAmplitude record bit *
      star (protocolEncryptionAmplitude record bit) = 1 := by
  rcases record with ⟨recordK, recordL⟩
  fin_cases recordK <;> fin_cases recordL <;> fin_cases bit <;>
    norm_num [protocolEncryptionAmplitude, protocolEncryptedReceiver,
      protocolBranchCorrection, rawZPhase, flipRaw, identity₂, pauliX, pauliZ,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem protocolEncoderKraus_message_column
    (record : ProtocolRecord) (bit : QubitIndex)
    (output : Basis ProtocolQubit) :
    protocolEncoderKraus record output (protocolMessageBits bit) =
      if output =
          protocolEncodedBits record (protocolEncryptedReceiver record bit) then
        (2 : ℂ)⁻¹ * protocolEncryptionAmplitude record bit
      else 0 := by
  rw [← protocolEncodedBasisEquiv.apply_symm_apply output]
  generalize protocolEncodedBasisEquiv.symm output = outputData
  rcases outputData with ⟨⟨outputK, outputL⟩, outputReceiver⟩
  rcases record with ⟨recordK, recordL⟩
  fin_cases outputK <;> fin_cases outputL <;> fin_cases outputReceiver <;>
    fin_cases recordK <;> fin_cases recordL <;> fin_cases bit <;>
    norm_num [protocolEncodedBasisEquiv, protocolEncoderKraus,
      protocolBranchIsometry, protocolEncryptionAmplitude,
      protocolEncryptedReceiver, protocolBranchCorrection,
      protocolMessageBits, rawZPhase, flipRaw, identity₂, pauliX, pauliZ,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two computational-basis inputs used for explicit local-information checks. -/
def protocolInputFamily (bit : QubitIndex) : Density ProtocolMessage :=
  basisDensity (protocolMessageBits bit)

/-- Their four-branch pre-correction encodings. -/
def protocolEncodedFamily (bit : QubitIndex) : Density ProtocolQubit :=
  protocolEncoder.mapDensity (protocolInputFamily bit)

private theorem mul_basisDensity_mul_conjTranspose_apply
    (K : Matrix (Basis ProtocolQubit) (Basis ProtocolMessage) ℂ)
    (bits : Basis ProtocolMessage) (output input : Basis ProtocolQubit) :
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

private theorem protocolEncoderKraus_basisDensity
    (record : ProtocolRecord) (bit : QubitIndex) :
    protocolEncoderKraus record * (protocolInputFamily bit).op *
        (protocolEncoderKraus record)ᴴ =
      (4 : ℂ)⁻¹ •
        (basisDensity
          (protocolEncodedBits record (protocolEncryptedReceiver record bit))).op := by
  ext output input
  change (protocolEncoderKraus record *
      (basisDensity (protocolMessageBits bit)).op *
        (protocolEncoderKraus record)ᴴ) output input = _
  rw [mul_basisDensity_mul_conjTranspose_apply,
    protocolEncoderKraus_message_column,
    protocolEncoderKraus_message_column]
  rw [Matrix.smul_apply, basisDensity_apply]
  let encoded :=
    protocolEncodedBits record (protocolEncryptedReceiver record bit)
  by_cases hout : output = encoded <;> by_cases hin : input = encoded
  · subst output
    subst input
    dsimp [encoded]
    simp only [if_true, true_and, mul_one]
    rw [map_mul]
    calc
      ((2 : ℂ)⁻¹ * protocolEncryptionAmplitude record bit) *
          (star (2 : ℂ)⁻¹ *
            star (protocolEncryptionAmplitude record bit)) =
        (4 : ℂ)⁻¹ *
          (protocolEncryptionAmplitude record bit *
            star (protocolEncryptionAmplitude record bit)) := by
              norm_num
              ring
      _ = (4 : ℂ)⁻¹ := by
        rw [protocolEncryptionAmplitude_mul_star, mul_one]
  · simp [encoded, hout, hin]
  · simp [encoded, hout, hin]
  · simp [encoded, hout, hin]

theorem protocolEncodedFamily_operator (bit : QubitIndex) :
    (protocolEncodedFamily bit).op =
      ∑ record : ProtocolRecord, (4 : ℂ)⁻¹ •
        (basisDensity
          (protocolEncodedBits record (protocolEncryptedReceiver record bit))).op := by
  change protocolEncoder.mapOperator (protocolInputFamily bit).op = _
  simp only [KrausChannel.mapOperator]
  apply Finset.sum_congr rfl
  intro record _
  exact protocolEncoderKraus_basisDensity record bit

/-- Maximally mixed state on any selected singleton of the encoded register. -/
def protocolSingletonMaximallyMixed (q : ProtocolQubit) :
    Density {r : ProtocolQubit // r ∈ ({q} : Finset ProtocolQubit)} where
  op := Matrix.diagonal (fun _ ↦ (2 : ℂ)⁻¹)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    norm_num [Complex.nonneg_iff]
  trace_one := by
    simp [Matrix.trace]

private theorem partialTrace_fintype_sum
    {I : Type*} [Fintype I] (s : Finset ProtocolQubit)
    (f : I → Operator ProtocolQubit) :
    partialTrace s (∑ i, f i) = ∑ i, partialTrace s (f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, partialTrace_add, ih]
      rw [Finset.sum_insert ha]

/-- Every individual record or receiver coordinate is maximally mixed for either basis input. -/
theorem protocolEncodedFamily_reduce_singleton
    (bit : QubitIndex) (q : ProtocolQubit) :
    (protocolEncodedFamily bit).reduce ({q} : Finset ProtocolQubit) =
      protocolSingletonMaximallyMixed q := by
  apply Density.ext
  rw [Density.reduce_op, protocolEncodedFamily_operator,
    partialTrace_fintype_sum]
  simp_rw [partialTrace_smul, partialTrace_basisDensity]
  let e := singletonBasisEquiv q
  have hrestrict (record : ProtocolRecord) (receiver : QubitIndex) :
      (fun r : {r : ProtocolQubit // r ∈ ({q} : Finset ProtocolQubit)} ↦
        protocolEncodedBits record receiver r.1) =
        e (protocolEncodedBits record receiver q) := by
    funext r
    have hr : r.1 = q := Finset.mem_singleton.mp r.2
    change protocolEncodedBits record receiver r.1 =
      protocolEncodedBits record receiver q
    rw [hr]
  simp_rw [hrestrict]
  ext i j
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize e.symm i = output
  generalize e.symm j = input
  fin_cases q <;> fin_cases bit <;> fin_cases output <;> fin_cases input <;>
    norm_num [protocolSingletonMaximallyMixed, protocolEncryptedReceiver,
      protocolEncodedBits, flipRaw, Pi.single, Fin.add_def,
      Fintype.sum_prod_type, Matrix.ofNat_apply, e.injective.eq_iff]

theorem protocolEncodedFamily_recordK_maximallyMixed (bit : QubitIndex) :
    (protocolEncodedFamily bit).reduce
        ({0} : Finset ProtocolQubit) =
      protocolSingletonMaximallyMixed 0 :=
  protocolEncodedFamily_reduce_singleton bit 0

theorem protocolEncodedFamily_recordL_maximallyMixed (bit : QubitIndex) :
    (protocolEncodedFamily bit).reduce
        ({1} : Finset ProtocolQubit) =
      protocolSingletonMaximallyMixed 1 :=
  protocolEncodedFamily_reduce_singleton bit 1

theorem protocolEncodedFamily_receiver_maximallyMixed (bit : QubitIndex) :
    (protocolEncodedFamily bit).reduce
        ({2} : Finset ProtocolQubit) =
      protocolSingletonMaximallyMixed 2 :=
  protocolEncodedFamily_reduce_singleton bit 2

/-- Every singleton's complete effect statistics are independent of the encoded input bit. -/
theorem protocolEncodedFamily_locallyStatisticsIndependent
    (q : ProtocolQubit) :
    LocallyStatisticsIndependent ({q} : Finset ProtocolQubit)
      protocolEncodedFamily := by
  intro bit bit'
  apply effectStatisticallyEquivalent_of_eq
  rw [protocolEncodedFamily_reduce_singleton,
    protocolEncodedFamily_reduce_singleton]

/-- The physical decoder recovers each member of the explicit two-input family exactly. -/
theorem protocolDecoder_recovers_inputFamily :
    Recovers protocolDecoder.mapDensity protocolEncodedFamily
      protocolInputFamily := by
  intro bit
  exact protocolDecoder_encoder_mapDensity (protocolInputFamily bit)

/-- The two computational-basis message inputs are operationally distinguishable. -/
theorem protocolInputFamily_statisticallyDetectable :
    StatisticallyDetectable protocolInputFamily := by
  have hbits : protocolMessageBits 1 ≠ protocolMessageBits 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  refine ⟨0, 1, basisEffect (protocolMessageBits 0), ?_⟩
  simp [protocolInputFamily, basisDensity_basisEffect_probability, hbits]

/-- Information is detectable on the full joint encoded register because a physical decoder
recovers the detectable message family. -/
theorem protocolEncodedFamily_jointRegister_statisticallyDetectable :
    StatisticallyDetectable protocolEncodedFamily :=
  StatisticallyDetectable.of_recovers_channel protocolDecoder
    protocolDecoder_recovers_inputFamily
    protocolInputFamily_statisticallyDetectable

/-- The record-`k` and receiver coordinates, selected together. -/
def protocolRecordKReceiver : Finset ProtocolQubit := {0, 2}

/-- Reindex the selected record-`k`/receiver basis by its two raw bits. -/
def protocolRecordKReceiverBasisEquiv :
    (QubitIndex × QubitIndex) ≃
      SubsystemBasis protocolRecordKReceiver where
  toFun bits q := if q.1 = 0 then bits.1 else bits.2
  invFun bits :=
    (bits ⟨0, by simp [protocolRecordKReceiver]⟩,
      bits ⟨2, by simp [protocolRecordKReceiver]⟩)
  left_inv := by
    intro bits
    apply Prod.ext <;> simp
  right_inv := by
    intro bits
    funext q
    change (if q.1 = 0 then
        bits ⟨0, by simp [protocolRecordKReceiver]⟩
      else bits ⟨2, by simp [protocolRecordKReceiver]⟩) = bits q
    by_cases hq0 : q.1 = 0
    · rw [if_pos hq0]
      apply congrArg bits
      apply Subtype.ext
      exact hq0.symm
    · rw [if_neg hq0]
      have hmem : q.1 = 0 ∨ q.1 = 2 := by
        simpa only [protocolRecordKReceiver, Finset.mem_insert,
          Finset.mem_singleton] using q.2
      have hq2 : q.1 = 2 := hmem.resolve_left hq0
      apply congrArg bits
      apply Subtype.ext
      exact hq2.symm

private theorem protocolRecordKReceiver_restriction
    (record : ProtocolRecord) (receiver : QubitIndex) :
    (fun q : {q : ProtocolQubit // q ∈ protocolRecordKReceiver} ↦
      protocolEncodedBits record receiver q.1) =
      protocolRecordKReceiverBasisEquiv (record.1, receiver) := by
  funext q
  by_cases hq0 : q.1 = 0
  · simp [protocolRecordKReceiverBasisEquiv, hq0]
  · have hmem : q.1 = 0 ∨ q.1 = 2 := by
      simpa only [protocolRecordKReceiver, Finset.mem_insert,
        Finset.mem_singleton] using q.2
    have hq2 : q.1 = 2 := hmem.resolve_left hq0
    simp [protocolRecordKReceiverBasisEquiv, hq2]

theorem protocolEncodedFamily_recordK_receiver_operator (bit : QubitIndex) :
    ((protocolEncodedFamily bit).reduce protocolRecordKReceiver).op =
      ∑ record : ProtocolRecord, (4 : ℂ)⁻¹ •
        Matrix.diagonal
          (Pi.single
            (protocolRecordKReceiverBasisEquiv
              (record.1, protocolEncryptedReceiver record bit)) 1) := by
  rw [Density.reduce_op, protocolEncodedFamily_operator,
    partialTrace_fintype_sum]
  simp_rw [partialTrace_smul, partialTrace_basisDensity,
    protocolRecordKReceiver_restriction]

private theorem protocolEncodedFamily_reduce_recordK_receiver_ne :
    (protocolEncodedFamily 0).reduce protocolRecordKReceiver ≠
      (protocolEncodedFamily 1).reduce protocolRecordKReceiver := by
  intro h
  have hop := congrArg Density.op h
  rw [protocolEncodedFamily_recordK_receiver_operator,
    protocolEncodedFamily_recordK_receiver_operator] at hop
  let e := protocolRecordKReceiverBasisEquiv
  have hentry := congrArg
    (fun A : SubsystemOperator protocolRecordKReceiver ↦
      A (e (0, 1)) (e (0, 1))) hop
  have hsingle (prepared observed : QubitIndex × QubitIndex) :
      (Pi.single (protocolRecordKReceiverBasisEquiv prepared) (1 : ℂ) :
          SubsystemBasis protocolRecordKReceiver → ℂ)
            (protocolRecordKReceiverBasisEquiv observed) =
        if prepared = observed then 1 else 0 := by
    by_cases hprepared : prepared = observed
    · subst observed
      simp
    · have hne : e prepared ≠ e observed :=
        fun heq ↦ hprepared (e.injective heq)
      rw [if_neg hprepared]
      change Function.update
        (0 : SubsystemBasis protocolRecordKReceiver → ℂ)
          (e prepared) 1 (e observed) = 0
      rw [Function.update_of_ne hne.symm]
      rfl
  dsimp only [e] at hentry
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    Matrix.diagonal_apply] at hentry
  simp_rw [hsingle] at hentry
  norm_num [protocolEncryptedReceiver, flipRaw,
    Fintype.sum_prod_type] at hentry

/-- Record bit `k` and the receiver jointly detect the basis input, although each singleton is
maximally mixed. -/
theorem protocolEncodedFamily_recordK_receiver_jointlyDetectable :
    JointlyDetectable ({0} : Finset ProtocolQubit) ({2} : Finset ProtocolQubit)
      protocolEncodedFamily := by
  unfold JointlyDetectable
  have hset :
      ({0} : Finset ProtocolQubit) ∪ ({2} : Finset ProtocolQubit) =
        protocolRecordKReceiver := by
    decide
  rw [hset]
  refine ⟨0, 1, ?_⟩
  exact (weaklyDistinguishable_iff_ne _ _).2
    protocolEncodedFamily_reduce_recordK_receiver_ne

/-- Each singleton is locally inaccessible even though the full encoded register is detectable. -/
theorem protocolEncodedFamily_singleton_inaccessible_globally_detectable
    (q : ProtocolQubit) :
    LocallyStatisticsIndependent ({q} : Finset ProtocolQubit)
        protocolEncodedFamily ∧
      StatisticallyDetectable protocolEncodedFamily :=
  ⟨protocolEncodedFamily_locallyStatisticsIndependent q,
    protocolEncodedFamily_jointRegister_statisticallyDetectable⟩

/-- Omitting the `k`-controlled `X` correction leaves the paper-`10` branch nonidentity. -/
theorem protocol_omit_recordK_correction_leaves_nonidentity :
    protocolBranchCorrection (0, 1) ≠ identity₂ := by
  rw [protocolBranchCorrection_paper10]
  intro h
  have h00 := congrArg (fun A : QubitMatrix ↦ A 0 0) h
  norm_num [pauliX, identity₂] at h00

/-- Omitting the `l`-controlled `Z` correction leaves the paper-`01` branch nonidentity. -/
theorem protocol_omit_recordL_correction_leaves_nonidentity :
    protocolBranchCorrection (1, 0) ≠ identity₂ := by
  rw [protocolBranchCorrection_paper01]
  intro h
  have h00 := congrArg (fun A : QubitMatrix ↦ A 0 0) h
  norm_num [pauliZ, identity₂] at h00

/-- On the paper-`10` branch, leaving the `k` correction unapplied flips the receiver's
`Z` observable.  This is a branch-specific operational witness, not a generic necessity claim. -/
theorem protocol_omit_recordK_changes_receiver_z_observable :
    Foundations.heisenberg (protocolBranchCorrection (0, 1)) pauliZ ≠ pauliZ := by
  rw [protocolBranchCorrection_paper10]
  intro h
  have h00 := congrArg (fun A : QubitMatrix ↦ A 0 0) h
  norm_num [Foundations.heisenberg, pauliX, pauliZ,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] at h00

/-- On the paper-`01` branch, leaving the `l` correction unapplied flips the receiver's
`X` observable.  This is a branch-specific operational witness, not a generic necessity claim. -/
theorem protocol_omit_recordL_changes_receiver_x_observable :
    Foundations.heisenberg (protocolBranchCorrection (1, 0)) pauliX ≠ pauliX := by
  rw [protocolBranchCorrection_paper01]
  intro h
  have h01 := congrArg (fun A : QubitMatrix ↦ A 0 1) h
  norm_num [Foundations.heisenberg, pauliX, pauliZ,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] at h01

/-- Named endpoints carried by supplied protocol metadata. -/
inductive ProtocolSite where
  | alice
  | bob
  deriving DecidableEq

/-- Explicitly supplied preparation metadata. It is not inferred from the final density state. -/
structure ProtocolPreparationHistory where
  inputBit : QubitIndex
  recordOrigin : ProtocolSite
  receiverDestination : ProtocolSite
  deriving DecidableEq

/-- A provenance witness for the encoder output family. -/
def protocolPreparation :
    Preparation protocolEncodedFamily ProtocolPreparationHistory where
  history := fun bit ↦ ⟨bit, .alice, .bob⟩
  realize := fun history ↦ protocolEncodedFamily history.inputBit
  realizes := by intro bit; rfl

/-- The supplied preparation record explicitly names an Alice-to-Bob route.  The theorem only
exposes stored metadata; it does not infer transport from the encoded density state. -/
theorem protocolPreparation_supplied_transport (bit : QubitIndex) :
    (protocolPreparation.history bit).recordOrigin = ProtocolSite.alice ∧
      (protocolPreparation.history bit).receiverDestination = ProtocolSite.bob := by
  exact ⟨rfl, rfl⟩

/-- The supplied preparation history remembers which of the two inputs was encoded. -/
theorem protocolPreparation_provenanceNonconstant :
    protocolPreparation.ProvenanceNonconstant := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hbit := congrArg ProtocolPreparationHistory.inputBit h
  change (0 : QubitIndex) = 1 at hbit
  norm_num at hbit

end
end Teleportation
end Deutsch
