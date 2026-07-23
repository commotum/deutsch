import DeutschTests.Foundations.Abstract
import DeutschTests.Foundations.Concrete
import DeutschTests.Foundations.MatrixSemantics
import Deutsch.Descriptor
import Deutsch.EPR
import Deutsch.Gates
import Deutsch.Information
import Deutsch.Locality
import Deutsch.Register
import DeutschTests.Gates
import DeutschTests.EPR
import DeutschTests.Information
import Deutsch.Teleportation
import Deutsch.Decoherence
import Deutsch.Bell
import DeutschTests.Teleportation

/-!
# Representative axiom audit

Keep this list representative rather than exhaustive. `goal-1/check_lean_integrity.py` compiles
this file and rejects `sorryAx` and project-defined axioms in the printed dependency report.
-/

#print axioms DeutschTests.Foundations.pauli_x_mul_y
#print axioms DeutschTests.Foundations.pauli_hermitian
#print axioms DeutschTests.Foundations.pauli_unitary
#print axioms DeutschTests.Foundations.paper_bit_z_eigenvalues
#print axioms DeutschTests.Foundations.x_left_factor_all_basis
#print axioms DeutschTests.Foundations.phase_gate_pins_heisenberg_direction
#print axioms DeutschTests.Foundations.phase_gate_transforms_x_eigenvectors
#print axioms DeutschTests.Foundations.cnot_projector_formula_is_explicit_permutation
#print axioms DeutschTests.Foundations.cnot_conjugates_target_y
#print axioms DeutschTests.Foundations.cnot_conjugates_control_y
#print axioms DeutschTests.Foundations.rx_pi_div_two_pins_heisenberg_y
#print axioms DeutschTests.Foundations.paper_bell_chronology_inverse_left
#print axioms DeutschTests.Foundations.paper_bell_chronology_inverse_right
#print axioms DeutschTests.Foundations.AbstractProbe.pureDensity
#print axioms DeutschTests.Foundations.AbstractProbe.disjoint_binary_operators_commute
#print axioms DeutschTests.Foundations.AbstractProbe.tensor_adjoint
#print axioms DeutschTests.Foundations.AbstractProbe.binary_locality_api_probe
#print axioms DeutschTests.Foundations.AbstractProbe.sum_probability_eq_one
#print axioms DeutschTests.Foundations.AbstractProbe.disjoint_matrix_operators_commute
#print axioms DeutschTests.Foundations.MatrixSemanticsProbe.bornProbabilities_normalize
#print axioms DeutschTests.Foundations.MatrixSemanticsProbe.maximallyMixed_probability_zero
#print axioms DeutschTests.Foundations.MatrixSemanticsProbe.maximallyMixed_probabilities_normalize

/-! ## Stage 3 public register API -/

-- Matrix/endomorphism and adjoint bridge.
#print axioms Deutsch.Register.matrixEndEquiv_apply
#print axioms Deutsch.Register.matrixEndEquiv_conjTranspose
#print axioms Deutsch.Register.heisenberg_chronology

-- Exact subsystem embedding and support.
#print axioms Deutsch.Register.embedSubsystem_mul
#print axioms Deutsch.Register.embedSubsystem_conjTranspose
#print axioms Deutsch.Register.embedSubsystem_injective
#print axioms Deutsch.Register.IsSupportedOn.mono
#print axioms Deutsch.Register.IsSupportedOn.heisenberg
#print axioms Deutsch.Register.embedQubit_commute_of_ne

-- Injection-ordered placement.
#print axioms Deutsch.Register.embedAlong_apply_ite
#print axioms Deutsch.Register.embedAlong_conjTranspose
#print axioms Deutsch.Register.embedAlong_injective
#print axioms Deutsch.Register.embedAlong_heisenberg

-- Embedded Pauli and paper-projector algebra.
#print axioms Deutsch.Register.xAt_mul_yAt
#print axioms Deutsch.Register.xAt_isHermitian
#print axioms Deutsch.Register.xAt_unitary
#print axioms Deutsch.Register.paperBitOneProjectorAt_mul_self
#print axioms Deutsch.Register.paperBitOneProjectorAt_eq
#print axioms Deutsch.Register.paperBitProjectorAt_sum

-- Pure states, preparation, predictions, and transport.
#print axioms Deutsch.Register.norm_basisKet
#print axioms Deutsch.Register.basisKet_expectation
#print axioms Deutsch.Register.norm_act_unitary
#print axioms Deutsch.Register.expectation_after_action
#print axioms Deutsch.Register.fixed_reference_prediction
#print axioms Deutsch.Register.heisenberg_eigenvector
#print axioms Deutsch.Register.exists_unitary_act_reference
#print axioms Deutsch.Register.PureState.exists_unitary_preparation
#print axioms Deutsch.Register.PureState.exists_fixed_reference_representation

/-! ## Stage 4 public locality API -/

-- Exact disjoint-subsystem products and the two commutation interfaces.
#print axioms Deutsch.Locality.embedSubsystem_mul_embedSubsystem_apply_of_disjoint
#print axioms Deutsch.Locality.embedSubsystem_commute_of_disjoint
#print axioms Deutsch.Locality.supportedOperators_commute_of_disjoint

-- Gram-factor bookkeeping and the isometry/unitarity cancellation boundary.
#print axioms Deutsch.Locality.heisenberg_eq_gram_mul_of_commute
#print axioms Deutsch.Locality.heisenberg_eq_self_of_commute_of_isometry
#print axioms Deutsch.Locality.heisenberg_eq_self_of_disjoint_support_of_isometry
#print axioms Deutsch.Locality.heisenberg_eq_self_of_disjoint_support

-- Arbitrary-ket Heisenberg and Schrödinger expectation invariance.
#print axioms Deutsch.Locality.expectation_heisenberg_eq_of_disjoint_support
#print axioms Deutsch.Locality.expectation_after_local_unitary_eq

/-! ## Stage 5 public descriptor API -/

-- Minimal validity, derived Pauli laws, and simultaneous evolution.
#print axioms Deutsch.Descriptor.Valid.component_unitary
#print axioms Deutsch.Descriptor.Valid.mul_yx
#print axioms Deutsch.Descriptor.Valid.anticommutes_next
#print axioms Deutsch.Descriptor.initial_component_isSupportedOn
#print axioms Deutsch.Descriptor.initial_valid
#print axioms Deutsch.Descriptor.Valid.evolve

-- Family cross relations and their preservation.
#print axioms Deutsch.DescriptorFamily.initial_pairwiseCommutes
#print axioms Deutsch.DescriptorFamily.initial_valid
#print axioms Deutsch.DescriptorFamily.PairwiseCommutes.evolve
#print axioms Deutsch.DescriptorFamily.Valid.evolve

-- Constructive generation and exact initial/evolved reconstruction.
#print axioms Deutsch.DescriptorFamily.Generation.reconstructedMatrixUnit_eq_single
#print axioms Deutsch.DescriptorFamily.initial_generates_operator_algebra
#print axioms Deutsch.DescriptorFamily.GeneratesOperatorAlgebra.evolve
#print axioms Deutsch.PauliWord.reconstruction
#print axioms Deutsch.PauliWord.basis_apply
#print axioms Deutsch.PauliWord.evolvedReconstruction
#print axioms Deutsch.PauliWord.evolvedPauliString_single

-- Deliberately distinct comparison levels.
#print axioms Deutsch.DescriptorFamily.isUnitaryConjugate_equivalence
#print axioms Deutsch.DescriptorFamily.referenceExpectationEquivalent_of_eq
#print axioms Deutsch.DescriptorFamily.referenceExpectationEquivalent_evolve_of_fixes_reference

/-! ## Stage 6 public gate API -/

-- Shared-frame algebra and ordered one-qubit placement.
#print axioms Deutsch.Register.heisenberg_smul
#print axioms Deutsch.Register.heisenberg_covariance
#print axioms Deutsch.Register.embedAlong_embedQubit

-- Exact one-qubit gates, phase distinctions, and corrected rotation signs.
#print axioms Deutsch.Gates.not_matrix_entry
#print axioms Deutsch.Gates.paperSqrtNot_square
#print axioms Deutsch.Gates.paperSqrtNot_heisenberg_twice
#print axioms Deutsch.Gates.rotationX_unitary
#print axioms Deutsch.Gates.rotationX_heisenberg_y
#print axioms Deutsch.Gates.rotationX_heisenberg_z
#print axioms Deutsch.Gates.rotationX_heisenberg_y_neg_pi_div_two
#print axioms Deutsch.Gates.rotationX_heisenberg_z_neg_pi_div_two
#print axioms Deutsch.Gates.rotationX_heisenberg_y_pi_div_two_ne_printed
#print axioms Deutsch.Gates.rotationX_heisenberg_z_pi_div_two_ne_printed
#print axioms Deutsch.Gates.diagonalPiRotation_eq_globalPhase_hadamard
#print axioms Deutsch.Gates.diagonalPiRotation_heisenberg
#print axioms Deutsch.Gates.descriptorNot_evolve
#print axioms Deutsch.Gates.rotationXAt_heisenberg_y
#print axioms Deutsch.Gates.hadamardAt_heisenberg_z

-- Static named-register and generic valid-descriptor CNOT.
#print axioms Deutsch.Gates.cnotAt_apply
#print axioms Deutsch.Gates.cnotAt_act_basisKet
#print axioms Deutsch.Gates.cnotAt_unitary
#print axioms Deutsch.Gates.cnotAt_isSupportedOn_pair
#print axioms Deutsch.Gates.cnotAt_eq_global_formula
#print axioms Deutsch.Gates.cnotAt_conjugates_target_y
#print axioms Deutsch.Gates.cnotAt_conjugates_control_x
#print axioms Deutsch.Gates.cnotFromDescriptors_mul_self
#print axioms Deutsch.Gates.cnotFromDescriptors_unitary
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_target_x
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_target_y
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_target_z
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_control_x
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_control_y
#print axioms Deutsch.Gates.cnotFromDescriptors_conjugates_control_z
#print axioms Deutsch.Gates.cnotFromDescriptors_initial_eq_cnotAt
#print axioms Deutsch.Gates.cnotFromDescriptors_evolve

-- Bell/inverse chronology, both inverse products, all generators, support, and amplitudes.
#print axioms Deutsch.Gates.bellAt_unitary
#print axioms Deutsch.Gates.bellInverseAt_unitary
#print axioms Deutsch.Gates.bellAt_inverse_left
#print axioms Deutsch.Gates.bellAt_inverse_right
#print axioms Deutsch.Gates.bellAt_conjugates_target_x
#print axioms Deutsch.Gates.bellAt_conjugates_target_y
#print axioms Deutsch.Gates.bellAt_conjugates_target_z
#print axioms Deutsch.Gates.bellAt_conjugates_control_x
#print axioms Deutsch.Gates.bellAt_conjugates_control_y
#print axioms Deutsch.Gates.bellAt_conjugates_control_z
#print axioms Deutsch.Gates.bellInverseAt_conjugates_target_x
#print axioms Deutsch.Gates.bellInverseAt_conjugates_target_y
#print axioms Deutsch.Gates.bellInverseAt_conjugates_target_z
#print axioms Deutsch.Gates.bellInverseAt_conjugates_control_x
#print axioms Deutsch.Gates.bellInverseAt_conjugates_control_y
#print axioms Deutsch.Gates.bellInverseAt_conjugates_control_z
#print axioms Deutsch.Gates.bellAt_isSupportedOn
#print axioms Deutsch.Gates.bellInverseAt_isSupportedOn
#print axioms Deutsch.Gates.bellAt_apply
#print axioms Deutsch.Gates.bellInverseAt_apply

/-! ## Stage 7 public information API -/

-- Density/effect/POVM semantics, Born bounds, and unitary expectation transport.
#print axioms Deutsch.Information.density_le_one
#print axioms Deutsch.Information.Density.toEffect_op
#print axioms Deutsch.Information.trace_mul_nonneg_of_posSemidef
#print axioms Deutsch.Information.bornWeight_eq_probability
#print axioms Deutsch.Information.bornProbability_nonneg
#print axioms Deutsch.Information.bornProbability_le_one
#print axioms Deutsch.Information.density_eq_iff_effect_probabilities
#print axioms Deutsch.Information.bornProbabilities_normalize
#print axioms Deutsch.Information.Effect.binaryPOVM_true
#print axioms Deutsch.Information.densityExpectation_pureDensity
#print axioms Deutsch.Information.basisDensity_basisEffect_probability
#print axioms Deutsch.Information.densityExpectation_evolve
#print axioms Deutsch.Information.purity_evolve
#print axioms Deutsch.Information.pureDensity_basisState
#print axioms Deutsch.Information.basisDensity_expectation
#print axioms Deutsch.Information.referenceDensity_expectation
#print axioms Deutsch.Information.pureDensity_evolve

-- Selected-subsystem reduction, computational bases, and local/global Born duality.
#print axioms Deutsch.Information.partialTrace_add
#print axioms Deutsch.Information.partialTrace_smul
#print axioms Deutsch.Information.partialTrace_basisDensity
#print axioms Deutsch.Information.partialTrace_posSemidef
#print axioms Deutsch.Information.partialTrace_trace
#print axioms Deutsch.Information.partialTrace_trace_mul
#print axioms Deutsch.Information.bornProbability_reduce
#print axioms Deutsch.Information.reduced_density_eq_iff_embedded_effect_probabilities
#print axioms Deutsch.Information.Effect.embedAlong_op
#print axioms Deutsch.Information.referenceDensity_expectation_embedAlong

-- Finite Kraus channels, dual effects, and composition.
#print axioms Deutsch.Information.KrausChannel.mapOperator_add
#print axioms Deutsch.Information.KrausChannel.mapOperator_smul
#print axioms Deutsch.Information.KrausChannel.mapOperator_zero
#print axioms Deutsch.Information.KrausChannel.mapOperator_posSemidef
#print axioms Deutsch.Information.KrausChannel.trace_mapOperator
#print axioms Deutsch.Information.KrausChannel.trace_duality
#print axioms Deutsch.Information.KrausChannel.bornProbability_mapDensity
#print axioms Deutsch.Information.identityChannel_mapDensity
#print axioms Deutsch.Information.unitaryChannel_mapDensity
#print axioms Deutsch.Information.KrausChannel.comp_mapDensity

-- Selected-subsystem channels and exact disjoint no-signalling.
#print axioms Deutsch.Information.KrausChannel.onSubsystem_dualOperator_embedSubsystem_of_disjoint
#print axioms Deutsch.Information.KrausChannel.onSubsystem_dualEffect_embedSubsystem_of_disjoint
#print axioms Deutsch.Information.KrausChannel.onSubsystem_bornProbability_disjoint
#print axioms Deutsch.Information.KrausChannel.onSubsystem_reduce_disjoint

-- Semantic equivalence, detectability, data processing, recovery, and provenance.
#print axioms Deutsch.Information.weaklyDistinguishable_iff_not_effectStatisticallyEquivalent
#print axioms Deutsch.Information.effectStatisticallyEquivalent_iff_eq
#print axioms Deutsch.Information.weaklyDistinguishable_iff_ne
#print axioms Deutsch.Information.reducedStateEquivalent_iff_localEffectStatisticallyEquivalent
#print axioms Deutsch.Information.localEffectStatisticallyEquivalent_iff_embedded
#print axioms Deutsch.Information.statisticallyDetectable_iff_not_statisticsIndependent
#print axioms Deutsch.Information.statisticsIndependent_iff_constant
#print axioms Deutsch.Information.statisticallyDetectable_iff_exists_ne
#print axioms Deutsch.Information.LocallyDetectable.statisticallyDetectable
#print axioms Deutsch.Information.StatisticsIndependent.locallyStatisticsIndependent
#print axioms Deutsch.Information.KrausChannel.effectStatisticallyEquivalent_mapDensity
#print axioms Deutsch.Information.KrausChannel.weaklyDistinguishable_input_of_output
#print axioms Deutsch.Information.KrausChannel.statisticsIndependent_mapDensity
#print axioms Deutsch.Information.Recovers.encoded_ne_of_target_ne
#print axioms Deutsch.Information.StatisticallyDetectable.of_recovers_channel
#print axioms Deutsch.Information.DescriptorNonconstant.not_constant
#print axioms Deutsch.Information.constantPreparation_provenanceNonconstant
#print axioms Deutsch.Information.constantPreparations_same_final_family

-- One-qubit effects, Pauli tomography, and the mixed-state fixed-reference boundary.
#print axioms Deutsch.Information.maximallyMixedQubit_purity
#print axioms Deutsch.Information.basisDensity_purity
#print axioms Deutsch.Information.maximallyMixedQubit_cannot_evolve_to_reference
#print axioms Deutsch.Information.xPlusEffect_op
#print axioms Deutsch.Information.yPlusEffect_op
#print axioms Deutsch.Information.zPlusEffect_op
#print axioms Deutsch.Information.zPlusEffect_op_eq_paperBitOneProjectorAt
#print axioms Deutsch.Information.qubitMatrix_eq_of_pauli_traces_eq
#print axioms Deutsch.Information.density_eq_of_pauliPlus_probabilities
#print axioms Deutsch.Information.reduce_eq_iff_embedded_pauliPlus_probabilities
#print axioms Deutsch.Information.reduce_singleton_eq_iff_embedded_effect_probabilities

-- Classical one-time-pad separation of local statistics, recovery, and provenance.
#print axioms Deutsch.Information.oneTimePadDensity_op
#print axioms Deutsch.Information.swappedOneTimePadDensity_eq
#print axioms Deutsch.Information.oneTimePadDensity_reduce_singleton
#print axioms Deutsch.Information.oneTimePad_locallyStatisticsIndependent
#print axioms Deutsch.Information.oneTimePadBasis_parity
#print axioms Deutsch.Information.parityEffect_op
#print axioms Deutsch.Information.oneTimePadDensity_parity_probability
#print axioms Deutsch.Information.oneTimePadDensity_weaklyDistinguishable
#print axioms Deutsch.Information.oneTimePad_statisticallyDetectable
#print axioms Deutsch.Information.parityDecoder_recovers_density
#print axioms Deutsch.Information.parityDecoder_recovers
#print axioms Deutsch.Information.oneTimePad_preparation_histories_distinct
#print axioms Deutsch.Information.oneTimePad_preparations_same_final_density
#print axioms Deutsch.Information.oneTimePadPreparationLeft_provenanceNonconstant

/-! ## Stage 8 public EPR API -/

-- Pair preparation, Equation (22)'s phase, and Equation (39)'s state identity.
#print axioms Deutsch.EPR.pairPreparation_unitary
#print axioms Deutsch.EPR.pairCircuit_unitary
#print axioms Deutsch.EPR.pairKet_eq
#print axioms Deutsch.EPR.equation22Ket_eq_globalPhase
#print axioms Deutsch.EPR.pairCircuit_referenceKet_eq_four_coordinates
#print axioms Deutsch.EPR.equation39_route_kets_eq

-- Named four-wire chronology, finite support, and corrected descriptor equations.
#print axioms Deutsch.EPR.timeFourUnitary_unitary
#print axioms Deutsch.EPR.timeOneUnitary_isSupportedOn
#print axioms Deutsch.EPR.timeTwoUnitary_isSupportedOn
#print axioms Deutsch.EPR.equation23_q2
#print axioms Deutsch.EPR.equation23_q3
#print axioms Deutsch.EPR.equation24_q1
#print axioms Deutsch.EPR.equation24_q4
#print axioms Deutsch.EPR.equation25_q2
#print axioms Deutsch.EPR.equation25_q3
#print axioms Deutsch.EPR.equation27_q1
#print axioms Deutsch.EPR.equation27_q2
#print axioms Deutsch.EPR.equation27_q3
#print axioms Deutsch.EPR.equation27_q4

-- Reduced states, corrected joint statistics, boundary counterexamples, and detectability.
#print axioms Deutsch.EPR.sameCoefficient_eq_cos_sub_half
#print axioms Deutsch.EPR.crossCoefficient_eq_I_mul_sin_sub_half
#print axioms Deutsch.EPR.equation38Ket_eq_globalPhase_pairPureState
#print axioms Deutsch.EPR.pairDensity_reduce_singleton
#print axioms Deutsch.EPR.pairDensity_locallyStatisticsIndependent
#print axioms Deutsch.EPR.pairDensity_different_probability
#print axioms Deutsch.EPR.pairDensity_jointPaperOne_probability
#print axioms Deutsch.EPR.pairDensity_paperOne_marginal_probability
#print axioms Deutsch.EPR.pairDensity_different_equal_settings
#print axioms Deutsch.EPR.pairDensity_jointPaperOne_equal_settings
#print axioms Deutsch.EPR.pairDensity_different_pi_zero
#print axioms Deutsch.EPR.equation28_printed_equal_angle_counterexample
#print axioms Deutsch.EPR.equation41_printed_equal_angle_counterexample
#print axioms Deutsch.EPR.pairSettingFamily_locallyStatisticsIndependent
#print axioms Deutsch.EPR.pairSettingFamily_statisticallyDetectable
#print axioms Deutsch.EPR.pairDensity_z_expectation
#print axioms Deutsch.EPR.pairDensity_equal_settings_zz_expectation
#print axioms Deutsch.EPR.pairDensity_zero_resource_correlation

-- Literal Figure 2 state evolution, record effects, and pair-statistics bridges.
#print axioms Deutsch.EPR.timeTwoUnitary_eq_embedAlong_pairCircuit
#print axioms Deutsch.EPR.timeTwoPureKet_eq_liftPair
#print axioms Deutsch.EPR.recordingLayer_liftPairKet
#print axioms Deutsch.EPR.fourWireTimeThreeDensity_eq_referenceDensity_evolve
#print axioms Deutsch.EPR.fourWireTimeFourDensity_eq_referenceDensity_evolve
#print axioms Deutsch.EPR.fourWireTimeThreePureState_ket
#print axioms Deutsch.EPR.recordOutcomeEffect_eq_embedAlong
#print axioms Deutsch.EPR.fourWireTimeThree_recordOutcome_probability
#print axioms Deutsch.EPR.fourWireTimeThree_recordOutcome_probability_eq_pairDensity
#print axioms Deutsch.EPR.fourWireTimeThree_leftRecord_probability
#print axioms Deutsch.EPR.fourWireTimeThree_rightRecord_probability
#print axioms Deutsch.EPR.fourWireTimeThree_leftRecord_probability_eq_pairDensity
#print axioms Deutsch.EPR.fourWireTimeThree_rightRecord_probability_eq_pairDensity
#print axioms Deutsch.EPR.fourWireTimeThree_jointRecord_probability_eq_pairDensity
#print axioms Deutsch.EPR.fourWireTimeThree_jointRecord_probability
#print axioms Deutsch.EPR.fourWireTimeFourPureState_ket
#print axioms Deutsch.EPR.fourWireTimeFour_comparison_probability
#print axioms Deutsch.EPR.fourWireTimeFour_comparison_probability_eq_pairDensity
#print axioms Deutsch.EPR.fourWireTimeFour_comparison_equal_settings
#print axioms Deutsch.EPR.fourWireTimeFour_comparison_relative_pi

-- Same final density with distinct supplied preparation histories.
#print axioms Deutsch.EPR.equation39_route_densities_eq
#print axioms Deutsch.EPR.leftRouteDensity_eq_pairDensity
#print axioms Deutsch.EPR.rightRouteDensity_eq_pairDensity
#print axioms Deutsch.EPR.routePreparation_histories_distinct
#print axioms Deutsch.EPR.routePreparations_same_final_density

/-! ## Stage 9 public teleportation API -/

-- Five-wire chronology, support, and corrected source descriptors.
#print axioms Deutsch.Teleportation.inputRotation_unitary
#print axioms Deutsch.Teleportation.timeThreeUnitary_unitary
#print axioms Deutsch.Teleportation.inputRotation_isSupportedOn
#print axioms Deutsch.Teleportation.timeOneUnitary_isSupportedOn
#print axioms Deutsch.Teleportation.timeTwoUnitary_isSupportedOn
#print axioms Deutsch.Teleportation.timeThreeUnitary_isSupportedOn
#print axioms Deutsch.Teleportation.recordingGates_commute
#print axioms Deutsch.Teleportation.equation29_q1
#print axioms Deutsch.Teleportation.equation29_q1_y_pi_div_two_ne_printed
#print axioms Deutsch.Teleportation.equation30_q4
#print axioms Deutsch.Teleportation.equation30_q5
#print axioms Deutsch.Teleportation.equation31_q1
#print axioms Deutsch.Teleportation.equation31_q1_y_pi_div_two_ne_printed
#print axioms Deutsch.Teleportation.equation31_q4
#print axioms Deutsch.Teleportation.equation32_q2
#print axioms Deutsch.Teleportation.equation32_q2_y_pi_div_two_ne_printed
#print axioms Deutsch.Teleportation.equation32_q3

-- Explicit Equation (33) circuit, nine Pauli images, and four branch actions.
#print axioms Deutsch.Teleportation.controlledZAt_isSupportedOn_pair
#print axioms Deutsch.Teleportation.correctionGate_isSupportedOn_triple
#print axioms Deutsch.Teleportation.correctionGate_unitary
#print axioms Deutsch.Teleportation.equation33_k_x
#print axioms Deutsch.Teleportation.equation33_k_y
#print axioms Deutsch.Teleportation.equation33_k_z
#print axioms Deutsch.Teleportation.equation33_l_x
#print axioms Deutsch.Teleportation.equation33_l_y
#print axioms Deutsch.Teleportation.equation33_l_z
#print axioms Deutsch.Teleportation.equation33_m_x
#print axioms Deutsch.Teleportation.equation33_m_y
#print axioms Deutsch.Teleportation.equation33_m_z
#print axioms Deutsch.Teleportation.correctionGate_branch_paper00
#print axioms Deutsch.Teleportation.correctionGate_branch_paper01
#print axioms Deutsch.Teleportation.correctionGate_branch_paper10
#print axioms Deutsch.Teleportation.correctionGate_branch_paper11

-- Corrected receiver descriptors and exact arbitrary-input circuit correctness.
#print axioms Deutsch.Teleportation.equation34_q5
#print axioms Deutsch.Teleportation.equation34_q5_y_pi_div_two_ne_printed
#print axioms Deutsch.Teleportation.teleportCorrectionGate_isSupportedOn
#print axioms Deutsch.Teleportation.timeFourUnitary_isSupportedOn
#print axioms Deutsch.Teleportation.timeFive_q5_z
#print axioms Deutsch.Teleportation.equation37_q5_z_pi_div_four_ne_printed
#print axioms Deutsch.Teleportation.verificationRotation_isSupportedOn
#print axioms Deutsch.Teleportation.timeFiveUnitary_isSupportedOn
#print axioms Deutsch.Teleportation.coherentProtocol_unitary
#print axioms Deutsch.Teleportation.coherentPreCorrection_exact
#print axioms Deutsch.Teleportation.coherentProtocol_factorizes
#print axioms Deutsch.Teleportation.teleportedDensity_reduce_receiver

-- Branch-derived operational encoder/decoder and source-family receiver statistics.
#print axioms Deutsch.Teleportation.protocolCorrectionGate_eq_branch_on_basis
#print axioms Deutsch.Teleportation.protocolBranchCorrection_paper00
#print axioms Deutsch.Teleportation.protocolBranchCorrection_paper01
#print axioms Deutsch.Teleportation.protocolBranchCorrection_paper10
#print axioms Deutsch.Teleportation.protocolBranchCorrection_paper11
#print axioms Deutsch.Teleportation.protocolBranchCorrection_unitary
#print axioms Deutsch.Teleportation.protocolDecoder_encoder_mapOperator
#print axioms Deutsch.Teleportation.protocolDecoder_encoder_mapDensity
#print axioms Deutsch.Teleportation.protocolDecoder_recovers
#print axioms Deutsch.Teleportation.protocolEncodedFamily_reduce_singleton
#print axioms Deutsch.Teleportation.protocolEncodedFamily_locallyStatisticsIndependent
#print axioms Deutsch.Teleportation.protocolDecoder_recovers_inputFamily
#print axioms Deutsch.Teleportation.protocolEncodedFamily_jointRegister_statisticallyDetectable
#print axioms Deutsch.Teleportation.protocolEncodedFamily_recordK_receiver_jointlyDetectable
#print axioms Deutsch.Teleportation.protocolEncodedFamily_singleton_inaccessible_globally_detectable
#print axioms Deutsch.Teleportation.protocol_omit_recordK_correction_leaves_nonidentity
#print axioms Deutsch.Teleportation.protocol_omit_recordL_correction_leaves_nonidentity
#print axioms Deutsch.Teleportation.protocol_omit_recordK_changes_receiver_z_observable
#print axioms Deutsch.Teleportation.protocol_omit_recordL_changes_receiver_x_observable
#print axioms Deutsch.Teleportation.protocolPreparation_supplied_transport
#print axioms Deutsch.Teleportation.protocolPreparation_provenanceNonconstant
#print axioms Deutsch.Teleportation.inputRotation_act_reference
#print axioms Deutsch.Teleportation.timeFourUnitary_eq_coherentProtocol_mul_inputRotation
#print axioms Deutsch.Teleportation.timeFour_act_reference_factorizes
#print axioms Deutsch.Teleportation.equation36_receiver_bloch_operator
#print axioms Deutsch.Teleportation.equation36_receiver_bloch_vector
#print axioms Deutsch.Teleportation.equation36_receiver_density
#print axioms Deutsch.Teleportation.equation36_receiver_all_effects
#print axioms Deutsch.Teleportation.equation35_corrected_effect_op
#print axioms Deutsch.Teleportation.equation35_receiver_purity
#print axioms Deutsch.Teleportation.equation35_teleported_probability_one
#print axioms Deutsch.Teleportation.equation35_printed_minus_sine_probability_zero_at_pi_div_two
#print axioms Deutsch.Teleportation.receiverPaperZeroEffect_op_eq_projector
#print axioms Deutsch.Teleportation.u02_paperZero_heisenberg
#print axioms Deutsch.Teleportation.u02_paperZero_probability_one
#print axioms Deutsch.Teleportation.timeFive_teleported_paperZero_probability_one
#print axioms Deutsch.Teleportation.timeFive_reference_output_paperZero_probability_one

/-! ## Stage 10 public explicit-decoherence API -/

-- Coordinate dephasing, basis boundaries, and the named CNOT environment.
#print axioms Deutsch.Information.coordinateDephasing_mapOperator_apply
#print axioms Deutsch.Information.coordinateDephasing_trace
#print axioms Deutsch.Information.coordinateDephasing_fixes_operator_iff
#print axioms Deutsch.Information.coordinateDephasing_map_basisDensity
#print axioms Deutsch.Information.coordinateDephasing_mapDensity_idempotent
#print axioms Deutsch.Information.coordinateDephasing_dual_zPlusEffect
#print axioms Deutsch.Information.coordinateDephasing_preserves_zPlusProbability_iterate
#print axioms Deutsch.Information.coordinateDephasing_changes_xPlusEffect
#print axioms Deutsch.Information.classicalBitFlip_changes_zPlusProbability
#print axioms Deutsch.Information.cnotEnvironmentState_eq_basisDensity
#print axioms Deutsch.Information.cnotEnvironmentCoupling_unitary
#print axioms Deutsch.Information.cnotEnvironmentKraus_eq_coordinateDephasingKraus
#print axioms Deutsch.Information.cnotEnvironmentDephasing_mapDensity

-- Teleportation record stability and a genuine record-bit error channel.
#print axioms Deutsch.Decoherence.protocolRecordDephasing_mapOperator_apply
#print axioms Deutsch.Decoherence.protocolRecordDephasing_encoder_mapOperator
#print axioms Deutsch.Decoherence.protocolRecordDephasing_encoder_mapDensity
#print axioms Deutsch.Decoherence.protocolDecoder_after_recordDephasing
#print axioms Deutsch.Decoherence.protocolRecordKBitFlip_encodedFamily
#print axioms Deutsch.Decoherence.protocolDecoder_after_recordKBitFlip
#print axioms Deutsch.Decoherence.protocolDecoder_after_recordKBitFlip_fails

-- Bounded EPR comparison stability under repeated record dephasing.
#print axioms Deutsch.Decoherence.comparisonGate_heisenberg_q1_z
#print axioms Deutsch.Decoherence.eprComparisonPaperOneEffect_op
#print axioms Deutsch.Decoherence.coordinateDephasing_q4_fixes_eprComparisonPaperOneEffect
#print axioms Deutsch.Decoherence.coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability_iterate
#print axioms Deutsch.Decoherence.epr_c34_q4_dephasing_before_comparison
#print axioms Deutsch.Decoherence.epr_c34_q4_dephasing_before_comparison_iterate

-- Constructive classical-correlation counterexample to an entanglement-witness overclaim.
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_op
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_left_z_expectation
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_right_z_expectation
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_zz_expectation
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_matches_pairDensity_zero_z_moments
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_correlation
#print axioms Deutsch.Decoherence.classicallyCorrelatedDensity_ne_pairDensity_zero

/-! ## Stage 11 public corrected-Bell API -/

-- Printed Equation (45) counterexample and corrected complementary partition.
#print axioms Deutsch.Bell.SourceCorrection.numericOr_eq_boolValue_or
#print axioms Deutsch.Bell.SourceCorrection.equation45_printed_counterexample_values
#print axioms Deutsch.Bell.SourceCorrection.equation45_printed_fails_at_one_zero_one
#print axioms Deutsch.Bell.SourceCorrection.equation45_corrected_complementary_partition
#print axioms Deutsch.Bell.SourceCorrection.equation45_corrected_partition_for_assignment

-- Common-assignment pigeonhole bound and explicit two-party local reduction.
#print axioms Deutsch.Bell.commonAssignment_has_agreeing_pair
#print axioms Deutsch.Bell.commonAssignment_indicator_sum_ge_one
#print axioms Deutsch.Bell.three_setting_bell_inequality
#print axioms Deutsch.Bell.quarter_agreements_contradict_common_assignment
#print axioms Deutsch.Bell.no_common_assignment_has_three_quarter_agreements
#print axioms Deutsch.Bell.perfectEqualSettingSupport_of_agreementProbability_one
#print axioms Deutsch.Bell.local_three_setting_bell_inequality
#print axioms Deutsch.Bell.local_three_setting_bell_inequality_of_equal_setting_probability_one
#print axioms Deutsch.Bell.quarter_agreements_contradict_local_assignments
#print axioms Deutsch.Bell.quarter_agreements_contradict_local_assignments_of_equal_setting_probability_one
#print axioms Deutsch.Bell.no_local_assignment_has_three_quarter_agreements

-- Corrected EPR same-outcome probabilities and exact three-setting angles.
#print axioms Deutsch.Bell.paperBits_equal_iff_rawBits_equal
#print axioms Deutsch.Bell.sameOutcomeProbability_eq_cos_sq
#print axioms Deutsch.Bell.sameOutcomeProbability_comm
#print axioms Deutsch.Bell.sameOutcomeProbability_equal_setting
#print axioms Deutsch.Bell.cos_half_settingZero_sub_settingOne
#print axioms Deutsch.Bell.cos_half_settingZero_sub_settingTwo
#print axioms Deutsch.Bell.cos_half_settingOne_sub_settingTwo
#print axioms Deutsch.Bell.sameOutcomeProbability_settingZero_settingOne
#print axioms Deutsch.Bell.sameOutcomeProbability_settingZero_settingTwo
#print axioms Deutsch.Bell.sameOutcomeProbability_settingOne_settingTwo
#print axioms Deutsch.Bell.threeSetting_sameOutcomeProbability_of_ne
#print axioms Deutsch.Bell.threeSetting_sameOutcomeProbability_self

-- Explicit quantum/classical bridge and strongest normalized-local-model contradiction.
#print axioms Deutsch.Bell.reproducesThreeSettingQuantumAgreements_quarters
#print axioms Deutsch.Bell.reproducesThreeSettingQuantumAgreements_equal_setting
#print axioms Deutsch.Bell.corrected_epr_three_settings_refute_local_assignments
#print axioms Deutsch.Bell.no_local_assignments_reproduce_corrected_epr_three_settings
#print axioms Deutsch.Bell.corrected_epr_three_settings_refute_normalized_local_model
#print axioms Deutsch.Bell.no_normalized_local_model_reproduces_corrected_epr_three_settings
