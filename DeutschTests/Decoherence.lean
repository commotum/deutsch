import Deutsch.Decoherence

/-!
# Focused explicit-decoherence verification

These checks pin the selected computational basis, exact matrix action, repetition boundary,
wrong-basis and bit-error failures, the named CNOT environment, and record-channel recovery.
-/

namespace DeutschTests
namespace DecoherenceVerification

open Deutsch Deutsch.Decoherence Deutsch.EPR Deutsch.Foundations Deutsch.Gates
  Deutsch.Information Deutsch.Register Deutsch.Teleportation
open scoped Matrix

noncomputable section

/-! ## Generic coordinate channel -/

theorem dephasing_keeps_exactly_one_coordinate_block
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (A : Operator Q) (x y : Basis Q) :
    (coordinateDephasing q).mapOperator A x y =
      if x q = y q then A x y else 0 :=
  coordinateDephasing_mapOperator_apply q A x y

theorem dephasing_fixed_points_are_exactly_block_diagonal
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (A : Operator Q) :
    (coordinateDephasing q).mapOperator A = A ↔
      ∀ x y : Basis Q, x q ≠ y q → A x y = 0 :=
  coordinateDephasing_fixes_operator_iff q A

theorem dephasing_fixes_every_computational_basis_density
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (bits : Basis Q) :
    (coordinateDephasing q).mapDensity (basisDensity bits) =
      basisDensity bits :=
  coordinateDephasing_map_basisDensity q bits

theorem repeated_dephasing_is_idempotent
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (rho : Density Q) :
    (coordinateDephasing q).mapDensity
        ((coordinateDephasing q).mapDensity rho) =
      (coordinateDephasing q).mapDensity rho :=
  coordinateDephasing_mapDensity_idempotent q rho

theorem every_finite_repetition_preserves_the_selected_z_statistic
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : Q) (rho : Density Q) (n : Nat) :
    bornProbability (((coordinateDephasing q).mapDensity)^[n] rho)
        (zPlusEffect q) =
      bornProbability rho (zPlusEffect q) :=
  coordinateDephasing_preserves_zPlusProbability_iterate q rho n

theorem wrong_basis_x_effect_is_not_stable
    {Q : Type*} [Fintype Q] [DecidableEq Q] (q : Q) :
    (coordinateDephasing q).dualEffect (xPlusEffect q) ≠ xPlusEffect q :=
  coordinateDephasing_changes_xPlusEffect q

theorem classical_bit_error_changes_z_probability :
    bornProbability (basisDensity (oneQubitRawAssignment 0))
          (zPlusEffect (0 : Fin 1)) = 1 ∧
      bornProbability
          (basisDensity (oneQubitRawAssignment (flipRaw 0)))
          (zPlusEffect (0 : Fin 1)) = 0 :=
  classicalBitFlip_changes_zPlusProbability

/-! ## Explicit environment realization -/

theorem supplied_environment_is_paper_zero :
    cnotEnvironmentState =
      basisDensity (fun _ : Fin 1 ↦ cnotEnvironmentInputBit) :=
  cnotEnvironmentState_eq_basisDensity

theorem supplied_cnot_environment_coupling_is_unitary :
    cnotEnvironmentCoupling ∈
      Matrix.unitaryGroup (Basis (Fin 2)) Complex :=
  cnotEnvironmentCoupling_unitary

theorem discarded_cnot_environment_realizes_dephasing
    (rho : Density (Fin 1)) :
    cnotEnvironmentDephasing.mapDensity rho =
      (coordinateDephasing (0 : Fin 1)).mapDensity rho :=
  cnotEnvironmentDephasing_mapDensity rho

/-! ## Teleportation record channel -/

theorem record_dephasing_keeps_exactly_equal_record_blocks
    (A : Operator ProtocolQubit) (x y : Basis ProtocolQubit) :
    protocolRecordDephasing.mapOperator A x y =
      if x 0 = y 0 ∧ x 1 = y 1 then A x y else 0 :=
  protocolRecordDephasing_mapOperator_apply A x y

theorem every_semantic_encoder_operator_is_record_classical
    (A : Operator ProtocolMessage) :
    protocolRecordDephasing.mapOperator (protocolEncoder.mapOperator A) =
      protocolEncoder.mapOperator A :=
  protocolRecordDephasing_encoder_mapOperator A

theorem decoder_recovers_after_record_dephasing
    (rho : Density ProtocolMessage) :
    protocolDecoder.mapDensity
        (protocolRecordDephasing.mapDensity (protocolEncoder.mapDensity rho)) =
      rho :=
  protocolDecoder_after_recordDephasing rho

theorem real_record_bit_flip_changes_the_encoded_family
    (bit : QubitIndex) :
    protocolRecordKBitFlip.mapDensity (protocolEncodedFamily bit) =
      protocolEncodedFamily (flipRaw bit) :=
  protocolRecordKBitFlip_encodedFamily bit

theorem record_bit_flip_makes_exact_recovery_fail :
    protocolDecoder.mapDensity
        (protocolRecordKBitFlip.mapDensity (protocolEncodedFamily 0)) ≠
      protocolInputFamily 0 :=
  protocolDecoder_after_recordKBitFlip_fails

/-! ## Bounded EPR record stability and correlation boundary -/

theorem repeated_q4_dephasing_preserves_the_final_comparison
    (rho : Density EPRQubit) (n : Nat) :
    bornProbability
        (eprComparisonChannel.mapDensity
          (((coordinateDephasing q4).mapDensity)^[n] rho))
        (zPlusEffect q1) =
      bornProbability (eprComparisonChannel.mapDensity rho)
        (zPlusEffect q1) :=
  epr_c34_q4_dephasing_before_comparison_iterate rho n

theorem classical_mixture_has_the_same_three_z_moments_as_the_bell_resource :
    densityExpectation classicallyCorrelatedDensity (zAt (0 : Fin 2)) =
        densityExpectation (pairDensity 0 0) (zAt (0 : Fin 2)) ∧
      densityExpectation classicallyCorrelatedDensity (zAt (1 : Fin 2)) =
        densityExpectation (pairDensity 0 0) (zAt (1 : Fin 2)) ∧
      densityExpectation classicallyCorrelatedDensity
          (zAt (0 : Fin 2) * zAt (1 : Fin 2)) =
        densityExpectation (pairDensity 0 0)
          (zAt (0 : Fin 2) * zAt (1 : Fin 2)) :=
  classicallyCorrelatedDensity_matches_pairDensity_zero_z_moments

theorem nonproduct_z_correlation_does_not_identify_the_bell_density :
    densityExpectation classicallyCorrelatedDensity
          (zAt (0 : Fin 2) * zAt (1 : Fin 2)) ≠
        densityExpectation classicallyCorrelatedDensity (zAt (0 : Fin 2)) *
          densityExpectation classicallyCorrelatedDensity (zAt (1 : Fin 2)) ∧
      classicallyCorrelatedDensity ≠ pairDensity 0 0 :=
  ⟨classicallyCorrelatedDensity_correlation,
    classicallyCorrelatedDensity_ne_pairDensity_zero⟩

end
end DecoherenceVerification
end DeutschTests
