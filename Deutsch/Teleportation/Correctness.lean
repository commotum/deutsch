import Deutsch.Teleportation.Circuit
import Deutsch.Teleportation.Correction
import Deutsch.Information.Reduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Exact coherent teleportation correctness

The input in this module is already initialized on `q1`; consequently the parameter-free
protocol consists only of resource preparation, the Bell gate, coherent recording, and the
three-wire correction.  The main theorem is coefficient-generic: the final ket factors as a
fixed four-wire junk ket times the exact input amplitudes on `q5`.

Paper logical zero is raw matrix index `1`, so `alpha` is the coefficient at raw receiver bit
`1` and `beta` is the coefficient at raw receiver bit `0`.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Information Register
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

set_option maxHeartbeats 1000000

/-- A five-wire raw computational-basis assignment in Figure 3 wire order. -/
def teleportBits (b1 b2 b3 b4 b5 : QubitIndex) : Basis TeleportQubit :=
  ![b1, b2, b3, b4, b5]

@[simp] theorem teleportBits_q1 (b1 b2 b3 b4 b5 : QubitIndex) :
    teleportBits b1 b2 b3 b4 b5 q1 = b1 := rfl

@[simp] theorem teleportBits_q2 (b1 b2 b3 b4 b5 : QubitIndex) :
    teleportBits b1 b2 b3 b4 b5 q2 = b2 := rfl

@[simp] theorem teleportBits_q3 (b1 b2 b3 b4 b5 : QubitIndex) :
    teleportBits b1 b2 b3 b4 b5 q3 = b3 := rfl

@[simp] theorem teleportBits_q4 (b1 b2 b3 b4 b5 : QubitIndex) :
    teleportBits b1 b2 b3 b4 b5 q4 = b4 := rfl

@[simp] theorem teleportBits_q5 (b1 b2 b3 b4 b5 : QubitIndex) :
    teleportBits b1 b2 b3 b4 b5 q5 = b5 := rfl

/-- An arbitrary one-qubit ket initialized on `q1`, with every ancillary wire paper-zero. -/
def initializedInputKet (alpha beta : Complex) : Ket TeleportQubit :=
  alpha • basisKet (teleportBits 1 1 1 1 1) +
    beta • basisKet (teleportBits 0 1 1 1 1)

/-- The parameter-free coherent circuit acting on an already initialized input. -/
def coherentProtocol : Operator TeleportQubit :=
  correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5 *
    (recordingLayer * bellMeasurementGate * resourcePreparation)

theorem coherentProtocol_unitary :
    coherentProtocol ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    (correctionGate_unitary q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5)
    ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        recordingLayer_unitary bellMeasurementGate_unitary)
      resourcePreparation_unitary)

/-- The first four wires, ordered as `q1,q2,q3,q4`. -/
abbrev JunkQubit := Fin 4

/-- A raw computational-basis assignment on the four junk wires. -/
def junkBits (b1 b2 b3 b4 : QubitIndex) : Basis JunkQubit :=
  ![b1, b2, b3, b4]

/--
The normalized, input-independent junk ket left on `q1,q2,q3,q4` by the coherent protocol.
Its four nonzero raw amplitudes are `(-1/2,-1/2,-1/2,+1/2)`.
-/
def fixedJunkKet : Ket JunkQubit :=
  ((2 : Complex)⁻¹) •
    (-basisKet (junkBits 0 0 0 0) - basisKet (junkBits 0 0 1 1) -
      basisKet (junkBits 1 1 0 0) + basisKet (junkBits 1 1 1 1))

/-- The actual singleton subsystem occupied by the receiver wire. -/
abbrev ReceiverQubit := {q : TeleportQubit // q ∈ ({q5} : Finset TeleportQubit)}

/-- A raw singleton receiver assignment. -/
def receiverBits (bit : QubitIndex) : Basis ReceiverQubit := fun _ ↦ bit

@[simp] private theorem singletonBasisEquiv_q5_apply (bit : QubitIndex) :
    singletonBasisEquiv q5 bit = receiverBits bit := rfl

@[simp] private theorem receiverBits_eq (left right : QubitIndex) :
    receiverBits left = receiverBits right ↔ left = right := by
  constructor
  · intro h
    have hq := congrFun h ⟨q5, Finset.mem_singleton_self q5⟩
    simpa [receiverBits] using hq
  · intro h
    subst right
    rfl

/-- The input ket, now placed on the actual receiver singleton. -/
def receiverInputKet (alpha beta : Complex) : Ket ReceiverQubit :=
  alpha • basisKet (receiverBits 1) + beta • basisKet (receiverBits 0)

/-- Restrict a five-wire assignment to the first four wires. -/
def junkRestriction (bits : Basis TeleportQubit) : Basis JunkQubit :=
  fun i ↦ bits (Fin.castSucc i)

/-- Restrict a five-wire assignment to the receiver singleton. -/
def receiverRestriction (bits : Basis TeleportQubit) : Basis ReceiverQubit :=
  fun _ ↦ bits q5

@[simp] private theorem junkRestriction_teleportBits
    (b1 b2 b3 b4 receiver : QubitIndex) :
    junkRestriction (teleportBits b1 b2 b3 b4 receiver) =
      junkBits b1 b2 b3 b4 := by
  funext q
  fin_cases q <;> rfl

@[simp] private theorem receiverRestriction_teleportBits
    (b1 b2 b3 b4 receiver : QubitIndex) :
    receiverRestriction (teleportBits b1 b2 b3 b4 receiver) =
      receiverBits receiver := by
  funext q
  have hq : q.1 = q5 := Finset.mem_singleton.mp q.2
  have hsub : q = ⟨q5, Finset.mem_singleton_self q5⟩ := Subtype.ext hq
  subst q
  rfl

/-- Coordinate tensor product of the fixed junk ket and the receiver input ket. -/
def factorizedOutputKet (alpha beta : Complex) : Ket TeleportQubit :=
  WithLp.toLp 2 (fun bits ↦
    fixedJunkKet (junkRestriction bits) *
      receiverInputKet alpha beta (receiverRestriction bits))

private theorem teleportBits_eta (bits : Basis TeleportQubit) :
    bits = teleportBits (bits q1) (bits q2) (bits q3) (bits q4) (bits q5) := by
  funext q
  fin_cases q <;> rfl

private theorem resourcePreparation_act_initialized_basis (input : QubitIndex) :
    act resourcePreparation (basisKet (teleportBits input 1 1 1 1)) =
      invSqrtTwo • basisKet (teleportBits input 1 1 0 0) -
        invSqrtTwo • basisKet (teleportBits input 1 1 1 1) := by
  apply WithLp.ofLp_injective
  change resourcePreparation *ᵥ Pi.single (teleportBits input 1 1 1 1) 1 =
    invSqrtTwo • Pi.single (teleportBits input 1 1 0 0) 1 -
      invSqrtTwo • Pi.single (teleportBits input 1 1 1 1) 1
  rw [Matrix.mulVec_single_one]
  funext output
  rw [teleportBits_eta output]
  generalize output q1 = o1
  generalize output q2 = o2
  generalize output q3 = o3
  generalize output q4 = o4
  generalize output q5 = o5
  fin_cases input <;> fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
    fin_cases o4 <;> fin_cases o5 <;>
    simp [resourcePreparation, bellInverseAt_apply, teleportBits,
      targetControlPlacement, hadamard, flipRaw, q4, q5]
  all_goals decide

private def bellTargetRaw (input targetControl : QubitIndex) : QubitIndex :=
  if targetControl = 0 then flipRaw input else input

private theorem bellMeasurementGate_act_basis
    (input resource receiver : QubitIndex) :
    act bellMeasurementGate
        (basisKet (teleportBits input 1 1 resource receiver)) =
      invSqrtTwo •
          basisKet (teleportBits (bellTargetRaw input resource) 1 1 0 receiver) +
        (if resource = 0 then invSqrtTwo else -invSqrtTwo) •
          basisKet (teleportBits (bellTargetRaw input resource) 1 1 1 receiver) := by
  apply WithLp.ofLp_injective
  change bellMeasurementGate *ᵥ
      Pi.single (teleportBits input 1 1 resource receiver) 1 =
    invSqrtTwo •
        Pi.single (teleportBits (bellTargetRaw input resource) 1 1 0 receiver) 1 +
      (if resource = 0 then invSqrtTwo else -invSqrtTwo) •
        Pi.single (teleportBits (bellTargetRaw input resource) 1 1 1 receiver) 1
  rw [Matrix.mulVec_single_one]
  funext output
  rw [teleportBits_eta output]
  generalize output q1 = o1
  generalize output q2 = o2
  generalize output q3 = o3
  generalize output q4 = o4
  generalize output q5 = o5
  fin_cases input <;> fin_cases resource <;> fin_cases receiver <;>
    fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
    fin_cases o4 <;> fin_cases o5 <;>
    simp [bellMeasurementGate, bellAt_apply, bellTargetRaw, teleportBits,
      targetControlPlacement, hadamard, flipRaw, q1, q4]
  all_goals decide

private def recordedRaw (control : QubitIndex) : QubitIndex :=
  if control = 0 then 0 else 1

private theorem recordingLayer_act_basis
    (left resource receiver : QubitIndex) :
    act recordingLayer (basisKet (teleportBits left 1 1 resource receiver)) =
      basisKet
        (teleportBits left (recordedRaw left) (recordedRaw resource)
          resource receiver) := by
  rw [recordingLayer, act_mul, q1RecordingGate, q4RecordingGate,
    cnotAt_act_basisKet, cnotAt_act_basisKet]
  congr 1
  funext q
  fin_cases left <;> fin_cases resource <;> fin_cases receiver <;>
    fin_cases q <;>
    simp [cnotOutput, teleportBits, recordedRaw, flipRaw, q1, q2, q3, q4]

private theorem act_add_ket (A : Operator TeleportQubit)
    (psi chi : Ket TeleportQubit) :
    act A (psi + chi) = act A psi + act A chi := by
  exact (matrixEndEquiv TeleportQubit A).map_add psi chi

private theorem act_sub_ket (A : Operator TeleportQubit)
    (psi chi : Ket TeleportQubit) :
    act A (psi - chi) = act A psi - act A chi := by
  exact (matrixEndEquiv TeleportQubit A).map_sub psi chi

private theorem invSqrtTwo_mul_self :
    invSqrtTwo * invSqrtTwo = (2 : Complex)⁻¹ := by
  have hs : (Real.sqrt 2 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [invSqrtTwo]
  field_simp
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

/-- The eight coherent record branches immediately before the correction network. -/
def preCorrectionKet (alpha beta : Complex) : Ket TeleportQubit :=
  ((2 : Complex)⁻¹) •
    (alpha • basisKet (teleportBits 0 0 0 0 0) -
      beta • basisKet (teleportBits 0 0 0 0 1) +
      alpha • basisKet (teleportBits 0 0 1 1 0) +
      beta • basisKet (teleportBits 0 0 1 1 1) +
      beta • basisKet (teleportBits 1 1 0 0 0) -
      alpha • basisKet (teleportBits 1 1 0 0 1) +
      beta • basisKet (teleportBits 1 1 1 1 0) +
      alpha • basisKet (teleportBits 1 1 1 1 1))

theorem coherentPreCorrection_exact (alpha beta : Complex) :
    act (recordingLayer * bellMeasurementGate * resourcePreparation)
        (initializedInputKet alpha beta) =
      preCorrectionKet alpha beta := by
  simp only [act_mul, initializedInputKet, act_add_ket, act_sub_ket, act_smul,
    resourcePreparation_act_initialized_basis,
    bellMeasurementGate_act_basis, recordingLayer_act_basis,
    bellTargetRaw, recordedRaw]
  simp only [if_pos, if_false, one_ne_zero, flipRaw_zero, flipRaw_one]
  unfold preCorrectionKet
  rw [← invSqrtTwo_mul_self]
  module

private def explicitFinalKet (alpha beta : Complex) : Ket TeleportQubit :=
  ((2 : Complex)⁻¹) •
    (-beta • basisKet (teleportBits 0 0 0 0 0) -
      alpha • basisKet (teleportBits 0 0 0 0 1) -
      beta • basisKet (teleportBits 0 0 1 1 0) -
      alpha • basisKet (teleportBits 0 0 1 1 1) -
      beta • basisKet (teleportBits 1 1 0 0 0) -
      alpha • basisKet (teleportBits 1 1 0 0 1) +
      beta • basisKet (teleportBits 1 1 1 1 0) +
      alpha • basisKet (teleportBits 1 1 1 1 1))

private theorem factorizedOutputKet_eq_explicit (alpha beta : Complex) :
    factorizedOutputKet alpha beta = explicitFinalKet alpha beta := by
  apply WithLp.ofLp_injective
  funext output
  rw [teleportBits_eta output]
  generalize output q1 = o1
  generalize output q2 = o2
  generalize output q3 = o3
  generalize output q4 = o4
  generalize output q5 = o5
  fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
    fin_cases o4 <;> fin_cases o5 <;>
    simp only [factorizedOutputKet, junkRestriction_teleportBits,
      receiverRestriction_teleportBits]
  all_goals
    simp [explicitFinalKet, fixedJunkKet, receiverInputKet, junkBits,
      teleportBits, basisKet, basisVector, Pi.single]

@[simp] private theorem correctionBasisOutput_teleportBits
    (b1 b2 b3 b4 b5 : QubitIndex) :
    correctionBasisOutput q2 q5 (teleportBits b1 b2 b3 b4 b5) =
      teleportBits b1 b2 b3 b4 (if b2 = 0 then flipRaw b5 else b5) := by
  funext q
  fin_cases q <;>
    simp [correctionBasisOutput, cnotOutput, teleportBits, q2, q5]

private theorem correctionGate_preCorrectionKet
    (alpha beta : Complex) :
    act (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5)
        (preCorrectionKet alpha beta) =
      explicitFinalKet alpha beta := by
  unfold preCorrectionKet explicitFinalKet
  simp only [act_add_ket, act_sub_ket, act_smul,
    correctionGate_act_basisKet]
  simp only [correctionBasisOutput_teleportBits]
  simp [correctionBasisPhase, controlledZPhase, rawZPhase,
    teleportBits, q2, q3, q5, flipRaw]
  module

/-- Exact arbitrary-input output of the complete parameter-free coherent protocol. -/
theorem coherentProtocol_act_initializedInput (alpha beta : Complex) :
    act coherentProtocol (initializedInputKet alpha beta) =
      factorizedOutputKet alpha beta := by
  rw [coherentProtocol, act_mul, coherentPreCorrection_exact,
    correctionGate_preCorrectionKet,
    factorizedOutputKet_eq_explicit]

/--
Arbitrary-input coherent teleportation factorizes exactly: `q1,q2,q3,q4` contain the fixed
junk ket and `q5` contains the unchanged input amplitudes, with no residual global phase.
-/
theorem coherentProtocol_factorizes (alpha beta : Complex) :
    act coherentProtocol (initializedInputKet alpha beta) =
      factorizedOutputKet alpha beta :=
  coherentProtocol_act_initializedInput alpha beta

/-- Normalization condition for the paper-ordered amplitudes `alpha|0⟩ + beta|1⟩`. -/
def InputAmplitudesNormalized (alpha beta : Complex) : Prop :=
  alpha * star alpha + beta * star beta = 1

private theorem initializedInputKet_dot_self (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) :
    (fun bits ↦ initializedInputKet alpha beta bits) ⬝ᵥ
        star (fun bits ↦ initializedInputKet alpha beta bits) = 1 := by
  change
    (alpha • Pi.single (teleportBits 1 1 1 1 1) 1 +
        beta • Pi.single (teleportBits 0 1 1 1 1) 1) ⬝ᵥ
      star (alpha • Pi.single (teleportBits 1 1 1 1 1) 1 +
        beta • Pi.single (teleportBits 0 1 1 1 1) 1) = 1
  simp [InputAmplitudesNormalized, teleportBits] at hnorm ⊢
  simpa [mul_comm] using hnorm

private theorem receiverInputKet_dot_self (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) :
    (fun bits ↦ receiverInputKet alpha beta bits) ⬝ᵥ
        star (fun bits ↦ receiverInputKet alpha beta bits) = 1 := by
  change
    (alpha • Pi.single (receiverBits 1) 1 + beta • Pi.single (receiverBits 0) 1) ⬝ᵥ
      star (alpha • Pi.single (receiverBits 1) 1 +
        beta • Pi.single (receiverBits 0) 1) = 1
  have hne : receiverBits 1 ≠ receiverBits 0 := by
    intro h
    have hx := congrFun h ⟨q5, Finset.mem_singleton_self q5⟩
    simp [receiverBits] at hx
  simp [InputAmplitudesNormalized, hne] at hnorm ⊢
  simpa [mul_comm] using hnorm

/-- The normalized five-wire input state corresponding to normalized amplitudes. -/
def initializedInputPureState (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) : PureState TeleportQubit where
  ket := initializedInputKet alpha beta
  norm_eq_one := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    have hinner :
        ⟪initializedInputKet alpha beta, initializedInputKet alpha beta⟫_ℂ = 1 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, dotProduct,
        Pi.star_apply, starRingEnd_apply, mul_comm] using
        initializedInputKet_dot_self alpha beta hnorm
    rw [hinner]
    norm_num

/-- The normalized target state on the actual receiver singleton. -/
def receiverInputPureState (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) : PureState ReceiverQubit where
  ket := receiverInputKet alpha beta
  norm_eq_one := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    have hinner :
        ⟪receiverInputKet alpha beta, receiverInputKet alpha beta⟫_ℂ = 1 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, dotProduct,
        Pi.star_apply, starRingEnd_apply, mul_comm] using
        receiverInputKet_dot_self alpha beta hnorm
    rw [hinner]
    norm_num

/-- The physical pure output obtained by evolving the arbitrary normalized input. -/
def teleportedPureState (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) : PureState TeleportQubit :=
  (initializedInputPureState alpha beta hnorm).evolve coherentProtocol
    coherentProtocol_unitary

private theorem complementReceiver_ne_last
    (q : {q : TeleportQubit // q ∉ ({q5} : Finset TeleportQubit)}) :
    q.1 ≠ Fin.last 4 := by
  have hq : q.1 ≠ q5 := by simpa using q.2
  simpa [q5] using hq

/-- The complement of receiver `q5` is canonically the ordered four-wire junk register. -/
def junkComplementBasisEquiv :
    Basis JunkQubit ≃ ComplementBasis ({q5} : Finset TeleportQubit) where
  toFun bits q := bits (Fin.castPred q.1 (complementReceiver_ne_last q))
  invFun rest i := rest ⟨Fin.castSucc i, by
    simpa [q5] using Fin.castSucc_ne_last i⟩
  left_inv bits := by
    funext i
    simp [Fin.castPred_castSucc]
  right_inv rest := by
    funext q
    apply congrArg rest
    apply Subtype.ext
    exact Fin.castSucc_castPred q.1 (complementReceiver_ne_last q)

private theorem splitBasis_symm_receiver_junk
    (receiver : QubitIndex) (junk : Basis JunkQubit) :
    (splitBasis ({q5} : Finset TeleportQubit)).symm
        (singletonBasisEquiv q5 receiver, junkComplementBasisEquiv junk) =
      teleportBits (junk 0) (junk 1) (junk 2) (junk 3) receiver := by
  funext q
  change (if h : q ∈ ({q5} : Finset TeleportQubit) then receiver
    else junk (Fin.castPred q (complementReceiver_ne_last ⟨q, h⟩))) = _
  fin_cases q <;> simp [q5, teleportBits]
  all_goals congr 1

private theorem fixedJunkKet_dot_self :
    (fun bits ↦ fixedJunkKet bits) ⬝ᵥ star (fun bits ↦ fixedJunkKet bits) = 1 := by
  change
    (((2 : Complex)⁻¹) •
      (-Pi.single (junkBits 0 0 0 0) 1 - Pi.single (junkBits 0 0 1 1) 1 -
       Pi.single (junkBits 1 1 0 0) 1 + Pi.single (junkBits 1 1 1 1) 1)) ⬝ᵥ
    star (((2 : Complex)⁻¹) •
      (-Pi.single (junkBits 0 0 0 0) 1 - Pi.single (junkBits 0 0 1 1) 1 -
       Pi.single (junkBits 1 1 0 0) 1 + Pi.single (junkBits 1 1 1 1) 1)) = 1
  simp [junkBits]
  norm_num

private theorem junkBits_eta (bits : Basis JunkQubit) :
    bits = junkBits (bits 0) (bits 1) (bits 2) (bits 3) := by
  funext q
  fin_cases q <;> rfl

/-- Density of the normalized five-wire coherent output. -/
def teleportedDensity (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) : Density TeleportQubit :=
  pureDensity (teleportedPureState alpha beta hnorm)

/-- Density of the unchanged input amplitudes on the actual receiver singleton. -/
def receiverInputDensity (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) : Density ReceiverQubit :=
  pureDensity (receiverInputPureState alpha beta hnorm)

/-- Exact receiver reduced-density correctness for every normalized arbitrary input. -/
theorem teleportedDensity_reduce_receiver (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) :
    (teleportedDensity alpha beta hnorm).reduce
        ({q5} : Finset TeleportQubit) =
      receiverInputDensity alpha beta hnorm := by
  have hket : (teleportedPureState alpha beta hnorm).ket =
      factorizedOutputKet alpha beta := by
    exact coherentProtocol_factorizes alpha beta
  apply Density.ext
  rw [Density.reduce_op]
  ext i j
  let e := singletonBasisEquiv q5
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize hi : e.symm i = left
  generalize hj : e.symm j = right
  simp only [partialTrace, splitOperator_apply, teleportedDensity,
    receiverInputDensity, pureDensity, densityOfVector, Matrix.vecMulVec,
    Matrix.of_apply, Pi.star_apply]
  rw [hket]
  rw [← junkComplementBasisEquiv.sum_comp]
  simp_rw [e, splitBasis_symm_receiver_junk]
  simp only [factorizedOutputKet, PiLp.toLp_apply,
    junkRestriction_teleportBits, receiverRestriction_teleportBits]
  simp only [receiverInputPureState, singletonBasisEquiv_q5_apply]
  calc
    _ = (∑ x, fixedJunkKet x * star (fixedJunkKet x)) *
        (receiverInputKet alpha beta (receiverBits left) *
          star (receiverInputKet alpha beta (receiverBits right))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [← junkBits_eta x]
      rw [star_mul]
      ring
    _ = _ := by
      rw [show (∑ x, fixedJunkKet x * star (fixedJunkKet x)) = 1 by
        simpa only [dotProduct, Pi.star_apply] using fixedJunkKet_dot_self]
      rw [one_mul]

end
end Teleportation
end Deutsch
