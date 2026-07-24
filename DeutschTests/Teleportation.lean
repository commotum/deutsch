import Deutsch.Teleportation
import Mathlib.Tactic.NormNum

/-!
# Focused coherent-teleportation verification

These tests pin the five-wire chronology, descriptor components, all nine Equation (33) generator
images, all four record branches, arbitrary-amplitude factorization, receiver-density correctness,
and the operational identity decoder.
-/

namespace DeutschTests
namespace TeleportationVerification

open Deutsch Deutsch.Descriptor Deutsch.Foundations Deutsch.Gates Deutsch.Information
  Deutsch.Register Deutsch.Teleportation
open scoped Matrix

noncomputable section

/-! ## Circuit chronology and descriptors -/

theorem all_five_wire_boundaries_are_unitary (theta : Real) :
    inputRotation theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      resourcePreparation ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      timeOneUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      timeTwoUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      timeThreeUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      timeFourUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex ∧
      timeFiveUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact ⟨inputRotation_unitary theta, resourcePreparation_unitary,
    timeOneUnitary_unitary theta, timeTwoUnitary_unitary theta,
    timeThreeUnitary_unitary theta, timeFourUnitary_unitary theta,
    timeFiveUnitary_unitary theta⟩

theorem all_five_wire_boundaries_have_explicit_finite_support (theta : Real) :
    IsSupportedOn ({q1, q4, q5} : Finset TeleportQubit)
        (timeOneUnitary theta) ∧
      IsSupportedOn ({q1, q4, q5} : Finset TeleportQubit)
        (timeTwoUnitary theta) ∧
      IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
        (timeThreeUnitary theta) ∧
      IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
        (timeFourUnitary theta) ∧
      IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
        (timeFiveUnitary theta) :=
  ⟨timeOneUnitary_isSupportedOn theta,
    timeTwoUnitary_isSupportedOn theta,
    timeThreeUnitary_isSupportedOn theta,
    timeFourUnitary_isSupportedOn theta,
    timeFiveUnitary_isSupportedOn theta⟩

theorem equation29_rotation_components (theta : Real) :
    timeOneDescriptors theta q1 =
      { x := xAt q1
        y := (theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1
        z := (theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1 } :=
  equation29_q1 theta

theorem equation30_resource_descriptor_is_exact (theta : Real) :
    timeOneDescriptors theta q4 =
      { x := xAt q4
        y := -(yAt q4 * xAt q5)
        z := -(zAt q4 * xAt q5) } :=
  equation30_q4 theta

theorem equation31_input_descriptor_components (theta : Real) :
    timeTwoDescriptors theta q1 =
      { x := xAt q1
        y := ((theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1) * (zAt q4 * xAt q5)
        z := ((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * (zAt q4 * xAt q5) } :=
  equation31_q1 theta

theorem equation32_record_descriptor_components (theta : Real) :
    timeThreeDescriptors theta q2 =
      { x := xAt q2
        y := (-((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1)) * yAt q2 *
            (zAt q4 * xAt q5)
        z := (-((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1)) * zAt q2 *
            (zAt q4 * xAt q5) } :=
  equation32_q2 theta

theorem equation34_receiver_descriptor (theta : Real) :
    timeFourDescriptors theta q5 =
      { x := xAt q1 * zAt q3 * zAt q5
        y := ((theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1) *
            zAt q2 * zAt q3 * zAt q4 * zAt q5
        z := ((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * zAt q2 * zAt q4 } :=
  equation34_q5 theta

theorem equation37_final_observable (theta : Real) :
    (timeFiveDescriptors theta q5).z =
      ((theta.cos : Complex) * theta.cos) •
          (zAt q1 * zAt q2 * zAt q4) -
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
        ((theta.sin : Complex) * theta.sin) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) :=
  timeFive_q5_z theta

/-! ## Equation (33), all generators and all branches -/

theorem equation33_checks_all_nine_generators :
    heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (xAt q2) =
        -(xAt q2 * xAt q5) ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (yAt q2) =
        -(yAt q2 * xAt q5) ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (zAt q2) =
        zAt q2 ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (xAt q3) =
        zAt q2 * xAt q3 * zAt q5 ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (yAt q3) =
        zAt q2 * yAt q3 * zAt q5 ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (zAt q3) =
        zAt q3 ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (xAt q5) =
        -(zAt q3 * xAt q5) ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (yAt q5) =
        zAt q2 * zAt q3 * yAt q5 ∧
      heisenberg (correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5) (zAt q5) =
        -(zAt q2 * zAt q5) := by
  exact ⟨equation33_k_x _ _ _ _ _ _, equation33_k_y _ _ _ _ _ _,
    equation33_k_z _ _ _ _ _ _, equation33_l_x _ _ _ _ _ _,
    equation33_l_y _ _ _ _ _ _, equation33_l_z _ _ _ _ _ _,
    equation33_m_x _ _ _ _ _ _, equation33_m_y _ _ _ _ _ _,
    equation33_m_z _ _ _ _ _ _⟩

theorem correction_branch_matrices_are_explicit :
    protocolBranchCorrection (1, 1) = identity₂ ∧
      protocolBranchCorrection (1, 0) = -pauliZ ∧
      protocolBranchCorrection (0, 1) = -pauliX ∧
      protocolBranchCorrection (0, 0) = pauliZ * pauliX :=
  ⟨protocolBranchCorrection_paper00, protocolBranchCorrection_paper01,
    protocolBranchCorrection_paper10, protocolBranchCorrection_paper11⟩

/-! ## Arbitrary-input state and density correctness -/

theorem every_complex_amplitude_pair_factorizes (alpha beta : Complex) :
    act coherentProtocol (initializedInputKet alpha beta) =
      factorizedOutputKet alpha beta :=
  coherentProtocol_factorizes alpha beta

theorem nontrivial_phase_superposition_factorizes :
    act coherentProtocol
        (initializedInputKet invSqrtTwo (Complex.I * invSqrtTwo)) =
      factorizedOutputKet invSqrtTwo (Complex.I * invSqrtTwo) :=
  coherentProtocol_factorizes _ _

theorem nontrivial_real_superposition_factorizes :
    act coherentProtocol
        (initializedInputKet invSqrtTwo invSqrtTwo) =
      factorizedOutputKet invSqrtTwo invSqrtTwo :=
  coherentProtocol_factorizes _ _

theorem arbitrary_normalized_receiver_density (alpha beta : Complex)
    (hnorm : InputAmplitudesNormalized alpha beta) :
    (teleportedDensity alpha beta hnorm).reduce
        ({q5} : Finset TeleportQubit) =
      receiverInputDensity alpha beta hnorm :=
  teleportedDensity_reduce_receiver alpha beta hnorm

/-! ## Literal coherent-circuit channel -/

theorem literal_channel_kraus_is_a_coherentProtocol_matrix_slice
    (junk : Basis JunkQubit) (receiver : Basis ReceiverQubit)
    (input : Basis ProtocolMessage) :
    coherentProtocolChannel.kraus junk receiver input =
      coherentProtocol
        (coherentProtocolOutputBasis junk receiver)
        (coherentProtocolInputBasis input) := rfl

theorem literal_channel_is_reindexed_identity_on_every_operator
    (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A =
      reindexMessageOperator A :=
  coherentProtocolChannel_mapOperator A

theorem literal_channel_is_receiver_reduction_of_five_wire_output
    (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A =
      partialTrace ({q5} : Finset TeleportQubit)
        (coherentProtocolFiveWireOutputOperator A) :=
  coherentProtocolChannel_mapOperator_eq_receiverPartialTrace A

theorem literal_channel_is_reindexed_identity_on_every_density
    (rho : Density ProtocolMessage) :
    coherentProtocolChannel.mapDensity rho =
      reindexMessageDensity rho :=
  coherentProtocolChannel_mapDensity rho

theorem literal_channel_preserves_every_effect_probability
    (rho : Density ProtocolMessage) (effect : Effect ProtocolMessage) :
    bornProbability (coherentProtocolChannel.mapDensity rho)
        (reindexMessageEffect effect) =
      bornProbability rho effect :=
  coherentProtocolChannel_preserves_all_effects rho effect

theorem literal_and_semantic_channels_agree_on_every_operator
    (A : Operator ProtocolMessage) :
    coherentProtocolChannel.mapOperator A =
      reindexMessageOperator
        (protocolDecoder.mapOperator (protocolEncoder.mapOperator A)) :=
  coherentProtocolChannel_eq_protocolDecoder_encoder_mapOperator A

theorem literal_and_semantic_channels_agree_on_every_density
    (rho : Density ProtocolMessage) :
    coherentProtocolChannel.mapDensity rho =
      reindexMessageDensity
        (protocolDecoder.mapDensity (protocolEncoder.mapDensity rho)) :=
  coherentProtocolChannel_eq_protocolDecoder_encoder_mapDensity rho

/-! ## Operational recovery and parameterized-family statistics -/

theorem decoder_after_encoder_is_identity_on_every_operator
    (A : Operator ProtocolMessage) :
    protocolDecoder.mapOperator (protocolEncoder.mapOperator A) = A :=
  protocolDecoder_encoder_mapOperator A

theorem decoder_recovers_every_density :
    Recovers protocolDecoder.mapDensity
      (fun rho : Density ProtocolMessage ↦ protocolEncoder.mapDensity rho)
      (fun rho ↦ rho) :=
  protocolDecoder_recovers

theorem every_encoded_singleton_is_input_independent (q : ProtocolQubit) :
    LocallyStatisticsIndependent ({q} : Finset ProtocolQubit)
      protocolEncodedFamily :=
  protocolEncodedFamily_locallyStatisticsIndependent q

theorem recordK_and_receiver_are_jointly_detectable :
    JointlyDetectable ({0} : Finset ProtocolQubit)
      ({2} : Finset ProtocolQubit) protocolEncodedFamily :=
  protocolEncodedFamily_recordK_receiver_jointlyDetectable

theorem local_inaccessibility_and_global_detection_coexist (q : ProtocolQubit) :
    LocallyStatisticsIndependent ({q} : Finset ProtocolQubit)
        protocolEncodedFamily ∧
      StatisticallyDetectable protocolEncodedFamily :=
  protocolEncodedFamily_singleton_inaccessible_globally_detectable q

theorem both_record_corrections_have_nonidentity_omission_witnesses :
    protocolBranchCorrection (0, 1) ≠ identity₂ ∧
      protocolBranchCorrection (1, 0) ≠ identity₂ :=
  ⟨protocol_omit_recordK_correction_leaves_nonidentity,
    protocol_omit_recordL_correction_leaves_nonidentity⟩

theorem both_record_corrections_have_observable_omission_witnesses :
    heisenberg (protocolBranchCorrection (0, 1)) pauliZ ≠ pauliZ ∧
      heisenberg (protocolBranchCorrection (1, 0)) pauliX ≠ pauliX :=
  ⟨protocol_omit_recordK_changes_receiver_z_observable,
    protocol_omit_recordL_changes_receiver_x_observable⟩

theorem supplied_protocol_history_is_nonconstant :
    protocolPreparation.ProvenanceNonconstant :=
  protocolPreparation_provenanceNonconstant

theorem supplied_protocol_history_names_alice_to_bob (bit : QubitIndex) :
    (protocolPreparation.history bit).recordOrigin = ProtocolSite.alice ∧
      (protocolPreparation.history bit).receiverDestination = ProtocolSite.bob :=
  protocolPreparation_supplied_transport bit

theorem equation36_is_receiver_density_equality (theta : Real) :
    (parameterizedTeleportedDensity theta).reduce
        ({q5} : Finset TeleportQubit) =
      parameterizedReceiverDensity theta :=
  equation36_receiver_density theta

theorem equation36_has_receiver_bloch_vector (theta : Real) :
    densityExpectation (parameterizedReceiverDensity theta)
          (xAt receiverCoordinate) = 0 ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (yAt receiverCoordinate) = (Real.sin theta : Complex) ∧
      densityExpectation (parameterizedReceiverDensity theta)
          (zAt receiverCoordinate) = -(Real.cos theta : Complex) :=
  equation36_receiver_bloch_vector theta

theorem equation36_is_all_effect_prediction_equality (theta : Real)
    (effect : Effect ReceiverQubit) :
    bornProbability (parameterizedTeleportedDensity theta)
        (effect.embedSubsystem ({q5} : Finset TeleportQubit)) =
      bornProbability (parameterizedReceiverDensity theta) effect :=
  equation36_receiver_all_effects theta effect

theorem equation35_rank_one_effect_is_certain (theta : Real) :
    bornProbability (parameterizedTeleportedDensity theta)
        ((equation35Effect theta).embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 :=
  equation35_teleported_probability_one theta

theorem equation35_receiver_is_explicitly_pure (theta : Real) :
    purity (parameterizedReceiverDensity theta) = 1 :=
  equation35_receiver_purity theta

theorem final_inverse_rotation_verifies_paper_zero (theta : Real) :
    bornProbability (u02ReceiverDensity theta) receiverPaperZeroEffect = 1 :=
  u02_paperZero_probability_one theta

theorem final_verification_effect_is_the_paper_zero_projector :
    receiverPaperZeroEffect.op =
      paperBitZeroProjectorAt receiverCoordinate :=
  receiverPaperZeroEffect_op_eq_projector

theorem evolved_five_wire_output_verifies_paper_zero (theta : Real) :
    bornProbability (timeFiveTeleportedDensity theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 :=
  timeFive_teleported_paperZero_probability_one theta

theorem literal_timeFive_circuit_verifies_paper_zero (theta : Real) :
    bornProbability (timeFiveReferenceOutputDensity theta)
        (receiverPaperZeroEffect.embedSubsystem
          ({q5} : Finset TeleportQubit)) = 1 :=
  timeFive_reference_output_paperZero_probability_one theta

end
end TeleportationVerification
end DeutschTests
