import Deutsch.Teleportation.Statistics

/-!
# Paper façade: quantum teleportation

Source-shaped entries for Equations (29)--(37).
-/

namespace Deutsch
namespace Paper

open Foundations Information Register Teleportation
open scoped Matrix

noncomputable section

/-- Equation (29): the prepared input descriptor. -/
theorem equation29 (theta : ℝ) :
    timeOneDescriptors theta q1 =
      { x := xAt q1
        y := (theta.cos : ℂ) • yAt q1 -
          (theta.sin : ℂ) • zAt q1
        z := (theta.sin : ℂ) • yAt q1 +
          (theta.cos : ℂ) • zAt q1 } :=
  Teleportation.equation29_q1 theta

/-- Equation (30): both descriptors of the entangled resource. -/
theorem equation30 (theta : ℝ) :
    timeOneDescriptors theta q4 =
        { x := xAt q4
          y := -(yAt q4 * xAt q5)
          z := -(zAt q4 * xAt q5) } ∧
      timeOneDescriptors theta q5 =
        { x := xAt q4 * zAt q5
          y := -(xAt q4 * yAt q5)
          z := xAt q5 } :=
  ⟨Teleportation.equation30_q4 theta,
    Teleportation.equation30_q5 theta⟩

/-- Equation (31): both descriptors after the Bell operation. -/
theorem equation31 (theta : ℝ) :
    timeTwoDescriptors theta q1 =
        { x := xAt q1
          y := ((theta.cos : ℂ) • yAt q1 -
            (theta.sin : ℂ) • zAt q1) * (zAt q4 * xAt q5)
          z := ((theta.sin : ℂ) • yAt q1 +
            (theta.cos : ℂ) • zAt q1) * (zAt q4 * xAt q5) } ∧
      timeTwoDescriptors theta q4 =
        { x := -(zAt q4 * xAt q5)
          y := xAt q1 * (yAt q4 * xAt q5)
          z := xAt q1 * xAt q4 } :=
  ⟨Teleportation.equation31_q1 theta,
    Teleportation.equation31_q4 theta⟩

/-- Equation (32): the two coherent record descriptors. -/
theorem equation32 (theta : ℝ) :
    timeThreeDescriptors theta q2 =
        { x := xAt q2
          y := (-((theta.sin : ℂ) • yAt q1 +
            (theta.cos : ℂ) • zAt q1)) * yAt q2 *
              (zAt q4 * xAt q5)
          z := (-((theta.sin : ℂ) • yAt q1 +
            (theta.cos : ℂ) • zAt q1)) * zAt q2 *
              (zAt q4 * xAt q5) } ∧
      timeThreeDescriptors theta q3 =
        { x := xAt q3
          y := -(xAt q1 * yAt q3 * xAt q4)
          z := -(xAt q1 * zAt q3 * xAt q4) } :=
  ⟨Teleportation.equation32_q2 theta,
    Teleportation.equation32_q3 theta⟩

/-- Equation (33): all nine generators of the three-wire transformation in any current frame. -/
theorem equation33
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (k l m : Q) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    ((Descriptor.initial k).evolve W).evolve
        (heisenberg W (correctionGate k l m hkl hkm hlm)) =
        { x := -(heisenberg W (xAt k) * heisenberg W (xAt m))
          y := -(heisenberg W (yAt k) * heisenberg W (xAt m))
          z := heisenberg W (zAt k) } ∧
      ((Descriptor.initial l).evolve W).evolve
        (heisenberg W (correctionGate k l m hkl hkm hlm)) =
        { x := heisenberg W (zAt k) * heisenberg W (xAt l) *
              heisenberg W (zAt m)
          y := heisenberg W (zAt k) * heisenberg W (yAt l) *
              heisenberg W (zAt m)
          z := heisenberg W (zAt l) } ∧
      ((Descriptor.initial m).evolve W).evolve
        (heisenberg W (correctionGate k l m hkl hkm hlm)) =
        { x := -(heisenberg W (zAt l) * heisenberg W (xAt m))
          y := heisenberg W (zAt k) * heisenberg W (zAt l) *
              heisenberg W (yAt m)
          z := -(heisenberg W (zAt k) * heisenberg W (zAt m)) } := by
  constructor
  · apply Descriptor.ext_components
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (xAt k)) =
          -(heisenberg W (xAt k) * heisenberg W (xAt m))
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_k_x, Gates.heisenberg_neg,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (yAt k)) =
          -(heisenberg W (yAt k) * heisenberg W (xAt m))
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_k_y, Gates.heisenberg_neg,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (zAt k)) =
          heisenberg W (zAt k)
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_k_z]
  constructor
  · apply Descriptor.ext_components
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (xAt l)) =
          heisenberg W (zAt k) * heisenberg W (xAt l) *
            heisenberg W (zAt m)
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_l_x,
        heisenberg_mul_of_unitary W _ _ hW,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (yAt l)) =
          heisenberg W (zAt k) * heisenberg W (yAt l) *
            heisenberg W (zAt m)
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_l_y,
        heisenberg_mul_of_unitary W _ _ hW,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (zAt l)) =
          heisenberg W (zAt l)
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_l_z]
  · apply Descriptor.ext_components
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (xAt m)) =
          -(heisenberg W (zAt l) * heisenberg W (xAt m))
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_m_x, Gates.heisenberg_neg,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (yAt m)) =
          heisenberg W (zAt k) * heisenberg W (zAt l) *
            heisenberg W (yAt m)
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_m_y,
        heisenberg_mul_of_unitary W _ _ hW,
        heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        heisenberg (heisenberg W (correctionGate k l m hkl hkm hlm))
            (heisenberg W (zAt m)) =
          -(heisenberg W (zAt k) * heisenberg W (zAt m))
      rw [heisenberg_covariance _ _ _ hW,
        Teleportation.equation33_m_z, Gates.heisenberg_neg,
        heisenberg_mul_of_unitary W _ _ hW]

/-- Equation (34): the receiver descriptor after the three-wire transformation. -/
theorem equation34 (theta : ℝ) :
    timeFourDescriptors theta q5 =
      { x := xAt q1 * zAt q3 * zAt q5
        y := ((theta.cos : ℂ) • yAt q1 -
          (theta.sin : ℂ) • zAt q1) *
            zAt q2 * zAt q3 * zAt q4 * zAt q5
        z := ((theta.sin : ℂ) • yAt q1 +
          (theta.cos : ℂ) • zAt q1) * zAt q2 * zAt q4 } :=
  Teleportation.equation34_q5 theta

/-- The rank-one receiver effect used in Equation (35). -/
def equation35Effect (theta : ℝ) : Effect ReceiverQubit :=
  (parameterizedReceiverDensity theta).toEffect

private theorem embed_receiver_operator (A : QubitMatrix) :
    Register.embedSubsystem ({q5} : Finset TeleportQubit)
        (embedQubit receiverCoordinate A) =
      embedQubit q5 A := by
  ext i j
  rw [embedSubsystem_apply_ite, embedQubit_apply_ite,
    embedQubit_apply_ite]
  have hinner :
      ∀ q : ReceiverQubit, q ≠ receiverCoordinate →
        (fun r : ReceiverQubit => i r.1) q =
          (fun r : ReceiverQubit => j r.1) q := by
    intro q hq
    exfalso
    apply hq
    apply Subtype.ext
    exact Finset.mem_singleton.mp q.2
  rw [if_pos hinner]
  have hconditions :
      (∀ q, q ∉ ({q5} : Finset TeleportQubit) → i q = j q) ↔
        (∀ q, q ≠ q5 → i q = j q) := by
    simp
  by_cases houtside :
      ∀ q, q ∉ ({q5} : Finset TeleportQubit) → i q = j q
  · rw [if_pos houtside, if_pos (hconditions.mp houtside)]
    rfl
  · rw [if_neg houtside,
      if_neg (fun h => houtside (hconditions.mpr h))]

private theorem equation35Effect_embedded_op (theta : ℝ) :
    ((equation35Effect theta).embedSubsystem
        ({q5} : Finset TeleportQubit)).op =
      ((2 : ℂ)⁻¹) •
        (1 + (Real.sin theta : ℂ) • yAt q5 -
          (Real.cos theta : ℂ) • zAt q5) := by
  rw [Effect.embedSubsystem_op, equation35Effect,
    Density.toEffect_op, equation36_receiver_bloch_operator,
    embedSubsystem_smul, embedSubsystem_sub, embedSubsystem_add,
    embedSubsystem_one, embedSubsystem_smul, embedSubsystem_smul,
    yAt, zAt, embed_receiver_operator, embed_receiver_operator]
  rfl

/-- The literal current-observable expression displayed in Equation (35). -/
def equation35Observable (theta : ℝ) : Operator TeleportQubit :=
  ((2 : ℂ)⁻¹) •
    (1 + (Real.sin theta : ℂ) • (timeFourDescriptors theta q5).y -
      (Real.cos theta : ℂ) • (timeFourDescriptors theta q5).z)

private theorem equation35Observable_heisenberg (theta : ℝ) :
    equation35Observable theta =
      heisenberg (timeFourUnitary theta)
        ((equation35Effect theta).embedSubsystem
          ({q5} : Finset TeleportQubit)).op := by
  rw [equation35Observable, equation35Effect_embedded_op]
  rw [heisenberg_smul, heisenberg_sub, heisenberg_add,
    heisenberg_one_of_unitary _ (timeFourUnitary_unitary theta),
    heisenberg_smul, heisenberg_smul]
  rfl

/-- Equation (35): the displayed Boolean observable has fixed-reference expectation one. -/
theorem equation35 (theta : ℝ) :
    expectation (referenceKet TeleportQubit)
        (equation35Observable theta) = 1 := by
  rw [equation35Observable_heisenberg]
  rw [← fixed_reference_prediction]
  have hket :
      act (timeFourUnitary theta) (referenceKet TeleportQubit) =
        (teleportedPureState (inputAlpha theta) (inputBeta theta)
          (inputAmplitudes_normalized theta)).ket := by
    rw [timeFour_act_reference_factorizes]
    exact (coherentProtocol_factorizes
      (inputAlpha theta) (inputBeta theta)).symm
  rw [hket, ← densityExpectation_pureDensity]
  change
    densityExpectation (parameterizedTeleportedDensity theta)
      ((equation35Effect theta).embedSubsystem
        ({q5} : Finset TeleportQubit)).op = 1
  change
    bornWeight (parameterizedTeleportedDensity theta)
      ((equation35Effect theta).embedSubsystem
        ({q5} : Finset TeleportQubit)) = 1
  have hprob :
      bornProbability (parameterizedTeleportedDensity theta)
        ((equation35Effect theta).embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 := by
    exact Teleportation.equation35_teleported_probability_one theta
  rw [bornWeight_eq_probability]
  rw [hprob]
  rfl

private theorem timeFour_receiver_expectation
    (theta : ℝ) (A : QubitMatrix) :
    expectation (referenceKet TeleportQubit)
        (heisenberg (timeFourUnitary theta) (embedQubit q5 A)) =
      densityExpectation (parameterizedReceiverDensity theta)
        (embedQubit receiverCoordinate A) := by
  rw [← fixed_reference_prediction]
  have hket :
      act (timeFourUnitary theta) (referenceKet TeleportQubit) =
        (teleportedPureState (inputAlpha theta) (inputBeta theta)
          (inputAmplitudes_normalized theta)).ket := by
    rw [timeFour_act_reference_factorizes]
    exact (coherentProtocol_factorizes
      (inputAlpha theta) (inputBeta theta)).symm
  rw [hket, ← densityExpectation_pureDensity]
  change
    densityExpectation (parameterizedTeleportedDensity theta)
        (embedQubit q5 A) =
      densityExpectation (parameterizedReceiverDensity theta)
        (embedQubit receiverCoordinate A)
  rw [← embed_receiver_operator A]
  unfold densityExpectation
  rw [← partialTrace_trace_mul]
  change
    Matrix.trace
        (((parameterizedTeleportedDensity theta).reduce
            ({q5} : Finset TeleportQubit)).op *
          embedQubit receiverCoordinate A) = _
  rw [equation36_receiver_density]

private theorem timeFour_bloch_vector (theta : ℝ) :
    expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).x = 0 ∧
      expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).y = (Real.sin theta : ℂ) ∧
      expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).z = -(Real.cos theta : ℂ) := by
  have h := equation36_receiver_bloch_vector theta
  constructor
  · change
      expectation (referenceKet TeleportQubit)
        (heisenberg (timeFourUnitary theta) (embedQubit q5 pauliX)) = 0
    rw [timeFour_receiver_expectation]
    exact h.1
  constructor
  · change
      expectation (referenceKet TeleportQubit)
        (heisenberg (timeFourUnitary theta) (embedQubit q5 pauliY)) = _
    rw [timeFour_receiver_expectation]
    exact h.2.1
  · change
      expectation (referenceKet TeleportQubit)
        (heisenberg (timeFourUnitary theta) (embedQubit q5 pauliZ)) = _
    rw [timeFour_receiver_expectation]
    exact h.2.2

@[simp] private theorem expectation_add
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : Ket Q) (A B : Operator Q) :
    expectation psi (A + B) = expectation psi A + expectation psi B := by
  simp [expectation, act, inner_add_right]

@[simp] private theorem expectation_sub
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : Ket Q) (A B : Operator Q) :
    expectation psi (A - B) = expectation psi A - expectation psi B := by
  simp [expectation, act, inner_sub_right]

@[simp] private theorem expectation_smul
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : Ket Q) (c : ℂ) (A : Operator Q) :
    expectation psi (c • A) = c * expectation psi A := by
  simp [expectation, act, inner_smul_right]

private theorem referenceExpectation_xAt (q : TeleportQubit) :
    expectation (referenceKet TeleportQubit) (xAt q) = 0 := by
  rw [referenceKet, basisKet_expectation, xAt, embedQubit_apply_ite, if_pos]
  · simp [paperZeroAssignment, pauliX]
  · intro r hr
    rfl

private theorem referenceExpectation_yAt (q : TeleportQubit) :
    expectation (referenceKet TeleportQubit) (yAt q) = 0 := by
  rw [referenceKet, basisKet_expectation, yAt, embedQubit_apply_ite, if_pos]
  · simp [paperZeroAssignment, pauliY]
  · intro r hr
    rfl

private theorem referenceExpectation_zAt (q : TeleportQubit) :
    expectation (referenceKet TeleportQubit) (zAt q) = -1 := by
  rw [referenceKet, basisKet_expectation, zAt, embedQubit_apply_ite, if_pos]
  · simp [paperZeroAssignment, pauliZ]
  · intro r hr
    rfl

private theorem timeOne_bloch_vector (theta : ℝ) :
    expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).x = 0 ∧
      expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).y = (Real.sin theta : ℂ) ∧
      expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).z = -(Real.cos theta : ℂ) := by
  constructor
  · rw [timeOne_q1_x, referenceExpectation_xAt]
  constructor
  · rw [timeOne_q1_y, expectation_sub, expectation_smul,
      expectation_smul, referenceExpectation_yAt,
      referenceExpectation_zAt]
    ring
  · rw [timeOne_q1_z, expectation_add, expectation_smul,
      expectation_smul, referenceExpectation_yAt,
      referenceExpectation_zAt]
    ring

/-- Equation (36): the source and receiver descriptors have the same displayed Bloch vector. -/
theorem equation36 (theta : ℝ) :
    (expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).x = 0 ∧
      expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).y = (Real.sin theta : ℂ) ∧
      expectation (referenceKet TeleportQubit)
          (timeOneDescriptors theta q1).z = -(Real.cos theta : ℂ)) ∧
    (expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).x = 0 ∧
      expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).y = (Real.sin theta : ℂ) ∧
      expectation (referenceKet TeleportQubit)
          (timeFourDescriptors theta q5).z = -(Real.cos theta : ℂ)) :=
  ⟨timeOne_bloch_vector theta, timeFour_bloch_vector theta⟩

/-- Receiver-density form of Equation (36). -/
theorem equation36_receiver (theta : ℝ) :
    densityExpectation (parameterizedReceiverDensity theta)
          (xAt receiverCoordinate) = 0 ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (yAt receiverCoordinate) = (Real.sin theta : ℂ) ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (zAt receiverCoordinate) = -(Real.cos theta : ℂ) :=
  Teleportation.equation36_receiver_bloch_vector theta

/-- Equation (37): the final receiver `Z` observable. -/
theorem equation37 (theta : ℝ) :
    (timeFiveDescriptors theta q5).z =
      ((theta.cos : ℂ) * theta.cos) •
          (zAt q1 * zAt q2 * zAt q4) -
        ((theta.cos : ℂ) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
        ((theta.sin : ℂ) * theta.sin) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) :=
  Teleportation.timeFive_q5_z theta

/-- The receiver paper-zero effect embedded on the initial five-wire register. -/
private theorem receiverPaperZeroEffect_embedded_op :
    (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)).op =
      ((2 : ℂ)⁻¹) • (1 - zAt q5) := by
  rw [Effect.embedSubsystem_op, receiverPaperZeroEffect_op,
    embedSubsystem_smul, embedSubsystem_sub, embedSubsystem_one,
    zAt, embed_receiver_operator]
  rfl

private theorem timeFive_paperZero_heisenberg (theta : ℝ) :
    heisenberg (timeFiveUnitary theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)).op =
      ((2 : ℂ)⁻¹) •
        (1 - (timeFiveDescriptors theta q5).z) := by
  rw [receiverPaperZeroEffect_embedded_op, heisenberg_smul,
    heisenberg_sub,
    heisenberg_one_of_unitary _ (timeFiveUnitary_unitary theta)]
  rfl

/-- The literal fixed-reference certainty display immediately following Equation (37). -/
theorem equation37_fixed_reference_probability (theta : ℝ) :
    ((2 : ℂ)⁻¹) *
        expectation (referenceKet TeleportQubit)
          (1 - (timeFiveDescriptors theta q5).z) = 1 := by
  rw [← expectation_smul, ← timeFive_paperZero_heisenberg,
    ← fixed_reference_prediction]
  change
    expectation (timeFiveReferenceOutputPureState theta).ket
      (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)).op = 1
  rw [← densityExpectation_pureDensity]
  change
    bornWeight (timeFiveReferenceOutputDensity theta)
      (receiverPaperZeroEffect.embedSubsystem
        ({q5} : Finset TeleportQubit)) = 1
  rw [bornWeight_eq_probability,
    timeFive_reference_output_paperZero_probability_one]
  rfl

/-- The unnumbered certainty check immediately following Equation (37). -/
theorem equation37_probability (theta : ℝ) :
    bornProbability (timeFiveReferenceOutputDensity theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 :=
  Teleportation.timeFive_reference_output_paperZero_probability_one theta

end
end Paper
end Deutsch
