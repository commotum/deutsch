import Deutsch.Teleportation.Descriptors
import Deutsch.Teleportation.Correctness

/-!
# Teleportation statistics for the one-parameter circuit

This module connects the `R_x(theta)` input preparation to the coefficient-generic coherent
correctness theorem.  Statistical claims are then stated for the actual receiver reduction,
keeping the paper's reversed raw-bit convention explicit.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Information Register
open scoped InnerProductSpace Matrix

noncomputable section

/-- Paper-zero amplitude prepared by the input rotation. -/
def inputAlpha (theta : Real) : Complex :=
  (Real.cos (theta / 2) : Complex)

/-- Paper-one amplitude prepared by the input rotation. -/
def inputBeta (theta : Real) : Complex :=
  -(Complex.I * (Real.sin (theta / 2) : Complex))

/-- The sine/cosine input amplitudes are normalized. -/
theorem inputAmplitudes_normalized (theta : Real) :
    InputAmplitudesNormalized (inputAlpha theta) (inputBeta theta) := by
  unfold InputAmplitudesNormalized inputAlpha inputBeta
  have hcosstar :
      star (Real.cos (theta / 2) : Complex) =
        (Real.cos (theta / 2) : Complex) := by
    exact Complex.conj_ofReal _
  have hsinstar :
      star (Real.sin (theta / 2) : Complex) =
        (Real.sin (theta / 2) : Complex) := by
    exact Complex.conj_ofReal _
  have hIstar : star Complex.I = -Complex.I := by
    exact Complex.conj_I
  have hbetastar :
      star (-(Complex.I * (Real.sin (theta / 2) : Complex))) =
        Complex.I * (Real.sin (theta / 2) : Complex) := by
    rw [star_neg, star_mul, hsinstar, hIstar]
    ring
  rw [hcosstar, hbetastar]
  calc
    (Real.cos (theta / 2) : Complex) *
          (Real.cos (theta / 2) : Complex) +
        -(Complex.I * (Real.sin (theta / 2) : Complex)) *
          (Complex.I * (Real.sin (theta / 2) : Complex)) =
        ((Real.sin (theta / 2) ^ 2 + Real.cos (theta / 2) ^ 2 : Real) :
          Complex) := by
            simp only [Complex.ofReal_add, Complex.ofReal_pow]
            ring_nf
            rw [Complex.I_sq]
            ring
    _ = 1 := by rw [Real.sin_sq_add_cos_sq]; norm_num

private theorem teleportBits_eta_statistics (bits : Basis TeleportQubit) :
    bits = teleportBits (bits q1) (bits q2) (bits q3) (bits q4) (bits q5) := by
  funext q
  fin_cases q <;> rfl

/-- `inputRotation theta` prepares exactly `cos(theta/2)|0> - i sin(theta/2)|1>` on `q1`. -/
theorem inputRotation_act_reference (theta : Real) :
    act (inputRotation theta) (referenceKet TeleportQubit) =
      initializedInputKet (inputAlpha theta) (inputBeta theta) := by
  apply WithLp.ofLp_injective
  change inputRotation theta *ᵥ Pi.single
      (paperZeroAssignment TeleportQubit) 1 =
    inputAlpha theta • Pi.single (teleportBits 1 1 1 1 1) 1 +
      inputBeta theta • Pi.single (teleportBits 0 1 1 1 1) 1
  rw [Matrix.mulVec_single_one]
  funext output
  rw [inputRotation, rotationXAt]
  change embedQubit q1 (rotationX theta) output
      (paperZeroAssignment TeleportQubit) = _
  rw [embedQubit_apply_ite]
  have houtside :
      (∀ j, j ≠ q1 →
          output j = paperZeroAssignment TeleportQubit j) ↔
        output q2 = 1 ∧ output q3 = 1 ∧
          output q4 = 1 ∧ output q5 = 1 := by
    constructor
    · intro h
      exact ⟨h q2 q2_ne_q1, h q3 q3_ne_q1,
        h q4 q4_ne_q1, h q5 q5_ne_q1⟩
    · rintro ⟨h2, h3, h4, h5⟩ j hj
      fin_cases j <;>
        simp_all [q1, q2, q3, q4, q5, paperZeroAssignment]
  simp only [houtside]
  rw [teleportBits_eta_statistics output]
  generalize output q1 = o1
  generalize output q2 = o2
  generalize output q3 = o3
  generalize output q4 = o4
  generalize output q5 = o5
  fin_cases o1 <;> fin_cases o2 <;> fin_cases o3 <;>
  fin_cases o4 <;> fin_cases o5 <;>
  simp [rotationX, rotationCosHalf, rotationSinHalf, identity₂, pauliX,
    inputAlpha, inputBeta, teleportBits, q1, q2, q3, q4, q5, Pi.single]

/-- The parameterized circuit is the generic coherent protocol preceded by its input rotation. -/
theorem timeFourUnitary_eq_coherentProtocol_mul_inputRotation (theta : Real) :
    timeFourUnitary theta = coherentProtocol * inputRotation theta := by
  unfold timeFourUnitary teleportCorrectionGate timeThreeUnitary timeTwoUnitary
    timeOneUnitary coherentProtocol
  rw [inputRotation_resourcePreparation_commute]
  simp only [Matrix.mul_assoc]

/-- On the fixed reference ket, the parameterized and initialized generic circuits coincide. -/
theorem timeFour_act_reference_eq_coherentProtocol (theta : Real) :
    act (timeFourUnitary theta) (referenceKet TeleportQubit) =
      act coherentProtocol
        (initializedInputKet (inputAlpha theta) (inputBeta theta)) := by
  rw [timeFourUnitary_eq_coherentProtocol_mul_inputRotation,
    act_mul, inputRotation_act_reference]

/-- Parameterized specialization of exact coherent factorization. -/
theorem timeFour_act_reference_factorizes (theta : Real) :
    act (timeFourUnitary theta) (referenceKet TeleportQubit) =
      factorizedOutputKet (inputAlpha theta) (inputBeta theta) := by
  rw [timeFour_act_reference_eq_coherentProtocol]
  exact coherentProtocol_factorizes (inputAlpha theta) (inputBeta theta)

/-- The normalized output density supplied by arbitrary-input correctness. -/
def parameterizedTeleportedDensity (theta : Real) : Density TeleportQubit :=
  teleportedDensity (inputAlpha theta) (inputBeta theta)
    (inputAmplitudes_normalized theta)

/-- The same parameterized state on the actual receiver singleton. -/
def parameterizedReceiverDensity (theta : Real) : Density ReceiverQubit :=
  receiverInputDensity (inputAlpha theta) (inputBeta theta)
    (inputAmplitudes_normalized theta)

/-- The unique coordinate of the receiver singleton. -/
def receiverCoordinate : ReceiverQubit :=
  ⟨q5, Finset.mem_singleton_self q5⟩

private theorem receiverCoordinate_eq (q : ReceiverQubit) :
    q = receiverCoordinate := by
  apply Subtype.ext
  simpa [receiverCoordinate] using Finset.mem_singleton.mp q.2

private theorem embedQubit_receiver_apply (A : QubitMatrix)
    (left right : QubitIndex) :
    embedQubit receiverCoordinate A
        ((singletonBasisEquiv q5) left)
        ((singletonBasisEquiv q5) right) = A left right := by
  rw [embedQubit_apply_ite, if_pos]
  · rfl
  · intro q hq
    exact False.elim (hq (receiverCoordinate_eq q))

private theorem receiver_one_apply (left right : QubitIndex) :
    (1 : Operator ReceiverQubit)
        ((singletonBasisEquiv q5) left)
        ((singletonBasisEquiv q5) right) =
      if left = right then 1 else 0 := by
  simp only [Matrix.one_apply, (singletonBasisEquiv q5).injective.eq_iff]

private theorem receiverBits_zero_ne_one :
    receiverBits 0 ≠ receiverBits 1 := by
  intro h
  have hraw := congrFun h receiverCoordinate
  norm_num [receiverBits] at hraw

private theorem receiverBits_one_ne_zero :
    receiverBits 1 ≠ receiverBits 0 :=
  Ne.symm receiverBits_zero_ne_one

private theorem pauliY_apply_raw (left right : QubitIndex) :
    pauliY left right =
      if left = 0 then
        if right = 0 then 0 else -Complex.I
      else if right = 0 then Complex.I else 0 := by
  fin_cases left <;> fin_cases right <;> norm_num [pauliY]

private theorem pauliZ_apply_raw (left right : QubitIndex) :
    pauliZ left right =
      if left = 0 then
        if right = 0 then 1 else 0
      else if right = 0 then 0 else -1 := by
  fin_cases left <;> fin_cases right <;> norm_num [pauliZ]

private theorem receiverInputKet_apply_raw (alpha beta : Complex)
    (bit : QubitIndex) :
    receiverInputKet alpha beta ((singletonBasisEquiv q5) bit) =
      if bit = 1 then alpha else beta := by
  change receiverInputKet alpha beta (receiverBits bit) = _
  fin_cases bit <;>
    simp [receiverInputKet, basisKet, basisVector, Pi.single]

private theorem input_sin_double_half (theta : Real) :
    (Real.sin theta : Complex) =
      2 * (Real.sin (theta / 2) : Complex) *
        (Real.cos (theta / 2) : Complex) := by
  have h : Real.sin theta =
      2 * Real.sin (theta / 2) * Real.cos (theta / 2) := by
    simpa only [show (2 : Real) * (theta / 2) = theta by ring] using
      Real.sin_two_mul (theta / 2)
  calc
    (Real.sin theta : Complex) =
        ((2 * Real.sin (theta / 2) * Real.cos (theta / 2) : Real) :
          Complex) := congrArg (fun x : Real ↦ (x : Complex)) h
    _ = 2 * (Real.sin (theta / 2) : Complex) *
        (Real.cos (theta / 2) : Complex) := by
          simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

private theorem input_cos_double_half (theta : Real) :
    (Real.cos theta : Complex) =
      (Real.cos (theta / 2) : Complex) ^ 2 -
        (Real.sin (theta / 2) : Complex) ^ 2 := by
  have h : Real.cos theta =
      Real.cos (theta / 2) ^ 2 - Real.sin (theta / 2) ^ 2 := by
    simpa only [show (2 : Real) * (theta / 2) = theta by ring] using
      Real.cos_two_mul' (theta / 2)
  calc
    (Real.cos theta : Complex) =
        ((Real.cos (theta / 2) ^ 2 - Real.sin (theta / 2) ^ 2 : Real) :
          Complex) := congrArg (fun x : Real ↦ (x : Complex)) h
    _ = (Real.cos (theta / 2) : Complex) ^ 2 -
        (Real.sin (theta / 2) : Complex) ^ 2 := by
          simp only [Complex.ofReal_sub, Complex.ofReal_pow]

/--
Equation (36) in density-operator form.  Thus the receiver Bloch vector is
`(0, +sin theta, -cos theta)` in the paper's reversed raw-bit convention.
-/
theorem equation36_receiver_bloch_operator (theta : Real) :
    (parameterizedReceiverDensity theta).op =
      ((2 : Complex)⁻¹) •
        (1 + (Real.sin theta : Complex) • yAt receiverCoordinate -
          (Real.cos theta : Complex) • zAt receiverCoordinate) := by
  ext i j
  let e := singletonBasisEquiv q5
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize e.symm i = left
  generalize e.symm j = right
  dsimp [e]
  change
    receiverInputKet (inputAlpha theta) (inputBeta theta)
          ((singletonBasisEquiv q5) left) *
        star (receiverInputKet (inputAlpha theta) (inputBeta theta)
          ((singletonBasisEquiv q5) right)) =
      (((2 : Complex)⁻¹) •
        (1 + (Real.sin theta : Complex) • yAt receiverCoordinate -
          (Real.cos theta : Complex) • zAt receiverCoordinate))
        ((singletonBasisEquiv q5) left) ((singletonBasisEquiv q5) right)
  rw [receiverInputKet_apply_raw, receiverInputKet_apply_raw]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    receiver_one_apply, yAt, zAt, embedQubit_receiver_apply]
  rw [input_sin_double_half theta, input_cos_double_half theta]
  have hcosstar :
      star (Real.cos (theta / 2) : Complex) =
        (Real.cos (theta / 2) : Complex) := Complex.conj_ofReal _
  have hsinstar :
      star (Real.sin (theta / 2) : Complex) =
        (Real.sin (theta / 2) : Complex) := Complex.conj_ofReal _
  have hIstar : star Complex.I = -Complex.I := Complex.conj_I
  simp only [pauliY_apply_raw, pauliZ_apply_raw]
  fin_cases left <;> fin_cases right
  all_goals
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Nat.zero_ne_one,
      Nat.one_ne_zero, eq_self, ↓reduceIte]
    simp only [inputAlpha, inputBeta, star_neg, star_mul,
      hIstar, hcosstar, hsinstar]
    ring_nf
    try rw [Complex.I_sq]
    try ring_nf
  all_goals
    rw [show theta * (1 / 2 : Real) = theta / 2 by ring]
    have h := Real.sin_sq_add_cos_sq (theta / 2)
    have hC :
        (Real.sin (theta / 2) : Complex) ^ 2 +
          (Real.cos (theta / 2) : Complex) ^ 2 = 1 := by
      exact_mod_cast h
    linear_combination hC / 2

private theorem receiver_trace_embedQubit (A : QubitMatrix) :
    Matrix.trace (embedQubit receiverCoordinate A) = Matrix.trace A := by
  change (∑ i, embedQubit receiverCoordinate A i i) = ∑ i, A i i
  rw [← (singletonBasisEquiv q5).sum_comp]
  simp only [embedQubit_receiver_apply]

private theorem receiver_trace_one :
    Matrix.trace (1 : Operator ReceiverQubit) = 2 := by
  calc
    Matrix.trace (1 : Operator ReceiverQubit) =
        Matrix.trace (embedQubit receiverCoordinate identity₂) := by
          rw [identity₂, embedQubit_one]
    _ = Matrix.trace identity₂ := receiver_trace_embedQubit identity₂
    _ = 2 := by norm_num [identity₂, Matrix.trace]

private theorem receiver_trace_x :
    Matrix.trace (xAt receiverCoordinate) = 0 := by
  rw [xAt, receiver_trace_embedQubit]
  norm_num [Matrix.trace, pauliX]

private theorem receiver_trace_y :
    Matrix.trace (yAt receiverCoordinate) = 0 := by
  rw [yAt, receiver_trace_embedQubit]
  norm_num [Matrix.trace, pauliY]

private theorem receiver_trace_z :
    Matrix.trace (zAt receiverCoordinate) = 0 := by
  rw [zAt, receiver_trace_embedQubit]
  norm_num [Matrix.trace, pauliZ]

/-- Equation (36) as the three receiver Pauli moments. -/
theorem equation36_receiver_bloch_vector (theta : Real) :
    densityExpectation (parameterizedReceiverDensity theta)
          (xAt receiverCoordinate) = 0 ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (yAt receiverCoordinate) = (Real.sin theta : Complex) ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (zAt receiverCoordinate) = -(Real.cos theta : Complex) := by
  constructor
  · rw [densityExpectation, equation36_receiver_bloch_operator]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul, yAt_mul_xAt, zAt_mul_xAt, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_add, receiver_trace_x,
      receiver_trace_y, receiver_trace_z, smul_zero, sub_zero, add_zero]
  constructor
  · rw [densityExpectation, equation36_receiver_bloch_operator]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul, yAt_mul_yAt, zAt_mul_yAt, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_add, receiver_trace_x,
      receiver_trace_y, receiver_trace_one, smul_eq_mul]
    ring
  · rw [densityExpectation, equation36_receiver_bloch_operator]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul, yAt_mul_zAt, zAt_mul_zAt, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_add, receiver_trace_x,
      receiver_trace_z, receiver_trace_one, smul_eq_mul]
    ring

/-- Exact receiver reduced-density form of Equation (36). -/
theorem equation36_receiver_density (theta : Real) :
    (parameterizedTeleportedDensity theta).reduce
        ({q5} : Finset TeleportQubit) =
      parameterizedReceiverDensity theta := by
  exact teleportedDensity_reduce_receiver
    (inputAlpha theta) (inputBeta theta) (inputAmplitudes_normalized theta)

/-- Equation (36) strengthened from three moments to every receiver effect. -/
theorem equation36_receiver_all_effects (theta : Real)
    (effect : Effect ReceiverQubit) :
    bornProbability (parameterizedTeleportedDensity theta)
        (effect.embedSubsystem ({q5} : Finset TeleportQubit)) =
      bornProbability (parameterizedReceiverDensity theta) effect := by
  rw [← bornProbability_reduce, equation36_receiver_density]

private theorem pureDensity_toEffect_probability_one
    {Q : Type*} [Fintype Q] [DecidableEq Q] (psi : PureState Q) :
    bornProbability (pureDensity psi) (pureDensity psi).toEffect = 1 := by
  let v : Basis Q → Complex := fun i ↦ psi.ket i
  have hdot : v ⬝ᵥ star v = 1 := by
    have hinner : ⟪psi.ket, psi.ket⟫_ℂ = 1 :=
      inner_self_eq_one_of_norm_eq_one psi.norm_eq_one
    change ∑ i, psi.ket i * star (psi.ket i) = 1
    simpa only [PiLp.inner_apply, RCLike.inner_apply, mul_comm,
      starRingEnd_apply] using hinner
  have hdot' : star v ⬝ᵥ v = 1 := by
    simpa only [dotProduct, Pi.star_apply, mul_comm] using hdot
  have hidempotent :
      (pureDensity psi).op * (pureDensity psi).op =
        (pureDensity psi).op := by
    simp only [pureDensity, densityOfVector,
      Matrix.vecMulVec_mul_vecMulVec]
    change Matrix.vecMulVec v ((star v ⬝ᵥ v) • star v) =
      Matrix.vecMulVec v (star v)
    rw [hdot']
    simp
  change (Matrix.trace ((pureDensity psi).op * (pureDensity psi).op)).re = 1
  rw [hidempotent, (pureDensity psi).trace_one]
  norm_num

/-- The rank-one receiver effect in Equation (35). -/
def equation35Effect (theta : Real) : Effect ReceiverQubit :=
  (parameterizedReceiverDensity theta).toEffect

/-- Equation (35) in receiver-operator form. -/
theorem equation35_effect_op (theta : Real) :
    (equation35Effect theta).op =
      ((2 : Complex)⁻¹) •
        (1 + (Real.sin theta : Complex) • yAt receiverCoordinate -
          (Real.cos theta : Complex) • zAt receiverCoordinate) := by
  exact equation36_receiver_bloch_operator theta

/-- The target receiver state passes the rank-one Equation (35) effect with certainty. -/
theorem equation35_receiver_probability_one (theta : Real) :
    bornProbability (parameterizedReceiverDensity theta)
        (equation35Effect theta) = 1 := by
  exact pureDensity_toEffect_probability_one
    (receiverInputPureState (inputAlpha theta) (inputBeta theta)
      (inputAmplitudes_normalized theta))

/-- The Equation (35) receiver state is explicitly pure, not merely certain for the
identity effect. -/
theorem equation35_receiver_purity (theta : Real) :
    purity (parameterizedReceiverDensity theta) = 1 := by
  have h := equation35_receiver_probability_one theta
  simpa [equation35Effect, bornProbability, bornWeight, purity] using h

/-- The actual five-wire output passes the embedded Equation (35) receiver effect with certainty. -/
theorem equation35_teleported_probability_one (theta : Real) :
    bornProbability (parameterizedTeleportedDensity theta)
        ((equation35Effect theta).embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 := by
  rw [equation36_receiver_all_effects]
  exact equation35_receiver_probability_one theta

/-- The receiver's paper-zero effect, expressed as the `theta = 0` rank-one target. -/
def receiverPaperZeroEffect : Effect ReceiverQubit :=
  equation35Effect 0

theorem receiverPaperZeroEffect_op :
    receiverPaperZeroEffect.op =
      ((2 : Complex)⁻¹) • (1 - zAt receiverCoordinate) := by
  rw [receiverPaperZeroEffect, equation35_effect_op]
  norm_num

/-- This effect is exactly the reversed-index paper-zero projector. -/
theorem receiverPaperZeroEffect_op_eq_projector :
    receiverPaperZeroEffect.op =
      paperBitZeroProjectorAt receiverCoordinate := by
  rw [receiverPaperZeroEffect_op,
    paperBitZeroProjectorAt_eq receiverCoordinate]

/-- U02 on the receiver: undo `R_x(theta)` before the paper-zero test. -/
def u02ReceiverRotation (theta : Real) : Operator ReceiverQubit :=
  rotationXAt receiverCoordinate (-theta)

theorem u02ReceiverRotation_unitary (theta : Real) :
    u02ReceiverRotation theta ∈
      Matrix.unitaryGroup (Basis ReceiverQubit) Complex := by
  exact rotationXAt_unitary receiverCoordinate (-theta)

/-- The post-U02 receiver density. -/
def u02ReceiverDensity (theta : Real) : Density ReceiverQubit :=
  (parameterizedReceiverDensity theta).evolve (u02ReceiverRotation theta)
    (u02ReceiverRotation_unitary theta)

/-- Pulling the paper-zero U02 test backwards gives exactly the Equation (35) effect. -/
theorem u02_paperZero_heisenberg (theta : Real) :
    heisenberg (u02ReceiverRotation theta) receiverPaperZeroEffect.op =
      (equation35Effect theta).op := by
  rw [receiverPaperZeroEffect_op, equation35_effect_op,
    heisenberg_smul, heisenberg_sub,
    heisenberg_one_of_unitary _ (u02ReceiverRotation_unitary theta),
    u02ReceiverRotation, rotationXAt_heisenberg_z]
  simp only [Real.sin_neg, Real.cos_neg, Complex.ofReal_neg, neg_smul]
  module

/-- U02's inverse rotation returns the teleported receiver to paper zero with probability one. -/
theorem u02_paperZero_probability_one (theta : Real) :
    bornProbability (u02ReceiverDensity theta) receiverPaperZeroEffect = 1 := by
  change
    (densityExpectation (u02ReceiverDensity theta)
      receiverPaperZeroEffect.op).re = 1
  rw [u02ReceiverDensity, densityExpectation_evolve,
    u02_paperZero_heisenberg]
  exact equation35_receiver_probability_one theta

private theorem verificationRotation_eq_embed_u02 (theta : Real) :
    verificationRotation theta =
      Register.embedSubsystem ({q5} : Finset TeleportQubit)
        (u02ReceiverRotation theta) := by
  ext left right
  unfold verificationRotation u02ReceiverRotation rotationXAt
  rw [embedQubit_apply_ite, embedSubsystem_apply_ite]
  by_cases houtside : ∀ q, q ≠ q5 → left q = right q
  · rw [if_pos houtside, if_pos (by simpa using houtside)]
    rw [← (singletonBasisEquiv q5).apply_symm_apply
        (fun q : ReceiverQubit ↦ left q.1),
      ← (singletonBasisEquiv q5).apply_symm_apply
        (fun q : ReceiverQubit ↦ right q.1),
      embedQubit_receiver_apply]
    rfl
  · rw [if_neg houtside, if_neg (by simpa using houtside)]

/--
The actual five-wire time-four output after the circuit's receiver-side U02 verification gate.
-/
def timeFiveTeleportedDensity (theta : Real) : Density TeleportQubit :=
  (parameterizedTeleportedDensity theta).evolve (verificationRotation theta)
    (verificationRotation_unitary theta)

/--
The evolved actual five-wire output passes the embedded paper-zero receiver effect with certainty.
This is the full-register U02 consequence, not merely a statement about an abstract target qubit.
-/
theorem timeFive_teleported_paperZero_probability_one (theta : Real) :
    bornProbability (timeFiveTeleportedDensity theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 := by
  change
    (densityExpectation (timeFiveTeleportedDensity theta)
      (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)).op).re = 1
  rw [timeFiveTeleportedDensity, densityExpectation_evolve,
    verificationRotation_eq_embed_u02, Effect.embedSubsystem_op,
    embedSubsystem_heisenberg]
  change
    (densityExpectation (parameterizedTeleportedDensity theta)
      (Register.embedSubsystem ({q5} : Finset TeleportQubit)
        (heisenberg (u02ReceiverRotation theta)
          receiverPaperZeroEffect.op))).re = 1
  rw [u02_paperZero_heisenberg]
  exact equation35_teleported_probability_one theta

/-- The normalized pure output of the literal `timeFiveUnitary` circuit on its reference ket. -/
def timeFiveReferenceOutputPureState (theta : Real) : PureState TeleportQubit where
  ket := act (timeFiveUnitary theta) (referenceKet TeleportQubit)
  norm_eq_one := by
    rw [norm_act_unitary (timeFiveUnitary theta)
      (timeFiveUnitary_unitary theta), norm_referenceKet]

/-- Density of the literal full time-five circuit output on the all-paper-zero reference input. -/
def timeFiveReferenceOutputDensity (theta : Real) : Density TeleportQubit :=
  pureDensity (timeFiveReferenceOutputPureState theta)

private theorem timeFour_reference_eq_teleportedPureState_ket (theta : Real) :
    act (timeFourUnitary theta) (referenceKet TeleportQubit) =
      (teleportedPureState (inputAlpha theta) (inputBeta theta)
        (inputAmplitudes_normalized theta)).ket := by
  rw [timeFour_act_reference_eq_coherentProtocol]
  rfl

/--
The literal full `timeFiveUnitary` reference output passes the embedded paper-zero U02 test with
probability one.
-/
theorem timeFive_reference_output_paperZero_probability_one (theta : Real) :
    bornProbability (timeFiveReferenceOutputDensity theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 := by
  change
    (densityExpectation (pureDensity (timeFiveReferenceOutputPureState theta))
      (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)).op).re = 1
  rw [densityExpectation_pureDensity]
  change
    (Register.expectation
      (act (timeFiveUnitary theta) (referenceKet TeleportQubit))
      (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)).op).re = 1
  rw [timeFiveUnitary, act_mul,
    timeFour_reference_eq_teleportedPureState_ket,
    expectation_after_action]
  rw [← densityExpectation_pureDensity]
  change
    (densityExpectation (parameterizedTeleportedDensity theta)
      (heisenberg (verificationRotation theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)).op)).re = 1
  rw [verificationRotation_eq_embed_u02, Effect.embedSubsystem_op,
    embedSubsystem_heisenberg]
  change
    (densityExpectation (parameterizedTeleportedDensity theta)
      (Register.embedSubsystem ({q5} : Finset TeleportQubit)
        (heisenberg (u02ReceiverRotation theta)
          receiverPaperZeroEffect.op))).re = 1
  rw [u02_paperZero_heisenberg]
  exact equation35_teleported_probability_one theta

end
end Teleportation
end Deutsch
