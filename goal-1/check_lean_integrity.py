#!/usr/bin/env python3
"""Audit the pinned Lean project, forbidden declarations, and representative axioms."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
EXPECTED_MATHLIB_TAG = "v4.32.0"
EXPECTED_MATHLIB_COMMIT = "81a5d257c8e410db227a6665ed08f64fea08e997"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_DEFAULT_TARGETS = (
    "Deutsch",
    "DeutschErrata",
    "DeutschTests",
    "DeutschErrataTests",
)
EXPECTED_LAKE_LIBRARIES = (
    "Deutsch",
    "DeutschTests",
    "DeutschErrata",
    "DeutschErrataTests",
)

REQUIRED_PUBLIC_ROOT_IMPORTS = (
    "Deutsch.Foundations",
    "Deutsch.Register",
    "Deutsch.Locality",
    "Deutsch.Descriptor",
    "Deutsch.Gates",
    "Deutsch.Information",
    "Deutsch.EPR",
    "Deutsch.Teleportation",
    "Deutsch.Decoherence",
    "Deutsch.Bell",
    "Deutsch.Paper",
)

REQUIRED_PRODUCTION_IMPORT_CLOSURE = {
    "Deutsch.lean": REQUIRED_PUBLIC_ROOT_IMPORTS,
    "Deutsch/Foundations.lean": (
        "Deutsch.Foundations.Concrete",
    ),
    "Deutsch/Register.lean": (
        "Deutsch.Register.Basic",
        "Deutsch.Register.Embedding",
        "Deutsch.Register.Pauli",
        "Deutsch.Register.State",
    ),
    "Deutsch/Locality.lean": (
        "Deutsch.Locality.Basic",
        "Deutsch.Locality.Heisenberg",
    ),
    "Deutsch/Descriptor.lean": (
        "Deutsch.Descriptor.Basic",
        "Deutsch.Descriptor.Comparison",
        "Deutsch.Descriptor.Generation",
        "Deutsch.Descriptor.PauliBasis",
    ),
    "Deutsch/Gates.lean": (
        "Deutsch.Gates.AxisRotation",
        "Deutsch.Gates.AxisRotationRegister",
        "Deutsch.Gates.Bell",
        "Deutsch.Gates.CNOT",
        "Deutsch.Gates.OneQubit",
    ),
    "Deutsch/Information.lean": (
        "Deutsch.Information.State",
        "Deutsch.Information.Reduction",
        "Deutsch.Information.Channel",
        "Deutsch.Information.LocalChannel",
        "Deutsch.Information.Dependence",
        "Deutsch.Information.Qubit",
        "Deutsch.Information.Dephasing",
        "Deutsch.Information.OneTimePad",
    ),
    "Deutsch/EPR.lean": (
        "Deutsch.EPR.Pair",
        "Deutsch.EPR.Circuit",
        "Deutsch.EPR.Statistics",
        "Deutsch.EPR.RecordStatistics",
        "Deutsch.EPR.Provenance",
    ),
    "Deutsch/Teleportation.lean": (
        "Deutsch.Teleportation.Circuit",
        "Deutsch.Teleportation.Correction",
        "Deutsch.Teleportation.Correctness",
        "Deutsch.Teleportation.Descriptors",
        "Deutsch.Teleportation.Protocol",
        "Deutsch.Teleportation.Statistics",
    ),
    "Deutsch/Decoherence.lean": (
        "Deutsch.Decoherence.Protocol",
        "Deutsch.Decoherence.EPR",
        "Deutsch.Decoherence.Correlation",
    ),
    "Deutsch/Bell.lean": (
        "Deutsch.Bell.Finite",
        "Deutsch.Bell.Quantum",
        "Deutsch.Bell.Moments",
        "Deutsch.Bell.AngleMoments",
        "Deutsch.Bell.Contradiction",
    ),
    "Deutsch/Bell/AngleMoments.lean": (
        "Deutsch.Bell.Moments",
    ),
    "Deutsch/Paper.lean": (
        "Deutsch.Paper.QuantumTheory",
        "Deutsch.Paper.Gates",
        "Deutsch.Paper.EPRExperiment",
        "Deutsch.Paper.EPRComparison",
        "Deutsch.Paper.Teleportation",
        "Deutsch.Paper.LocallyInaccessible",
        "Deutsch.Paper.Bell",
    ),
    "Deutsch/Paper/QuantumTheory.lean": (
        "Deutsch.Descriptor.Basic",
        "Deutsch.Information.State",
        "Deutsch.Register.State",
    ),
    "Deutsch/Paper/Gates.lean": (
        "Deutsch.Gates.Bell",
        "Deutsch.Gates.AxisRotationRegister",
        "Mathlib.Tactic.Module",
    ),
    "Deutsch/Paper/EPRExperiment.lean": (
        "Deutsch.EPR.Circuit",
        "Deutsch.EPR.Statistics",
        "Deutsch.Information.Qubit",
    ),
    "Deutsch/Paper/EPRComparison.lean": (
        "Deutsch.EPR.RecordStatistics",
    ),
    "Deutsch/Paper/Teleportation.lean": (
        "Deutsch.Teleportation.Statistics",
    ),
    "Deutsch/Paper/LocallyInaccessible.lean": (
        "Deutsch.EPR.Provenance",
    ),
    "Deutsch/Paper/Bell.lean": (
        "Deutsch.Bell.AngleMoments",
        "Deutsch.EPR.RecordStatistics",
    ),
}

REQUIRED_TEST_ROOT_IMPORTS = (
    "Deutsch",
    "DeutschTests.Audit",
    "DeutschTests.Bell",
    "DeutschTests.Descriptor",
    "DeutschTests.Decoherence",
    "DeutschTests.EPR",
    "DeutschTests.Examples",
    "DeutschTests.Foundations.Abstract",
    "DeutschTests.Foundations.Concrete",
    "DeutschTests.Foundations.MatrixSemantics",
    "DeutschTests.Gates",
    "DeutschTests.Information",
    "DeutschTests.Locality",
    "DeutschTests.Paper",
    "DeutschTests.Register",
    "DeutschTests.Teleportation",
)

REQUIRED_EXAMPLE_DECLARATIONS = (
    "named_pauli_is_embedded",
    "named_rotation_preserves_its_x_axis",
    "named_cnot_uses_target_control_placement",
    "local_x_fixes_remote_z",
    "one_time_pad_hides_secret_locally",
    "three_setting_quantum_probability",
    "quantum_table_refutes_normalized_local_model",
)

REQUIRED_PAPER_EQUATIONS = tuple(f"equation{index:02d}" for index in range(1, 47))

REQUIRED_PAPER_CHECK_TARGETS = tuple(
    f"Deutsch.Paper.{name}" for name in REQUIRED_PAPER_EQUATIONS
)

REQUIRED_PAPER_ORACLES = (
    "equation09_uses_current_frame",
    "equation17_uses_true_exp_and_transport",
    "equation28_has_structural_fourWire_bridge",
    "equation40_uses_literal_fourWire_records",
    "equation41_uses_literal_fourWire_joint_record",
    "equation43_requires_positive_support",
    "equation44_is_all_real_angles",
    "equation46_uses_direct_moment_chain",
)

REQUIRED_PAPER_PUBLIC_DECLARATIONS = {
    "Deutsch/Paper/QuantumTheory.lean": tuple(
        f"equation{index:02d}" for index in range(1, 9)
    ),
    "Deutsch/Paper/Gates.lean": tuple(
        f"equation{index:02d}" for index in range(9, 22)
    ),
    "Deutsch/Paper/EPRExperiment.lean": tuple(
        f"equation{index:02d}" for index in range(22, 28)
    ),
    "Deutsch/Paper/EPRComparison.lean": ("equation28",),
    "Deutsch/Paper/Teleportation.lean": tuple(
        f"equation{index:02d}" for index in range(29, 38)
    ),
    "Deutsch/Paper/LocallyInaccessible.lean": ("equation38", "equation39"),
    "Deutsch/Paper/Bell.lean": tuple(
        f"equation{index:02d}" for index in range(40, 47)
    ),
}

REQUIRED_PAPER_AUDIT_TARGETS = tuple(
    f"Deutsch.Paper.{name}" for name in REQUIRED_PAPER_EQUATIONS
)

REQUIRED_FILES = (
    "README.md",
    "Deutsch.lean",
    "Deutsch/Foundations.lean",
    "Deutsch/Foundations/Concrete.lean",
    "Deutsch/Register.lean",
    "Deutsch/Register/Basic.lean",
    "Deutsch/Register/Embedding.lean",
    "Deutsch/Register/Pauli.lean",
    "Deutsch/Register/State.lean",
    "Deutsch/Locality.lean",
    "Deutsch/Locality/Basic.lean",
    "Deutsch/Locality/Heisenberg.lean",
    "Deutsch/Descriptor.lean",
    "Deutsch/Descriptor/Basic.lean",
    "Deutsch/Descriptor/Comparison.lean",
    "Deutsch/Descriptor/Generation.lean",
    "Deutsch/Descriptor/PauliBasis.lean",
    "Deutsch/Gates.lean",
    "Deutsch/Gates/AxisRotation.lean",
    "Deutsch/Gates/AxisRotationRegister.lean",
    "Deutsch/Gates/Bell.lean",
    "Deutsch/Gates/CNOT.lean",
    "Deutsch/Gates/OneQubit.lean",
    "Deutsch/Information.lean",
    "Deutsch/Information/Channel.lean",
    "Deutsch/Information/Dephasing.lean",
    "Deutsch/Information/Dependence.lean",
    "Deutsch/Information/LocalChannel.lean",
    "Deutsch/Information/OneTimePad.lean",
    "Deutsch/Information/Qubit.lean",
    "Deutsch/Information/Reduction.lean",
    "Deutsch/Information/State.lean",
    "Deutsch/EPR.lean",
    "Deutsch/EPR/Pair.lean",
    "Deutsch/EPR/Circuit.lean",
    "Deutsch/EPR/Statistics.lean",
    "Deutsch/EPR/RecordStatistics.lean",
    "Deutsch/EPR/Provenance.lean",
    "Deutsch/Teleportation.lean",
    "Deutsch/Teleportation/Circuit.lean",
    "Deutsch/Teleportation/Correction.lean",
    "Deutsch/Teleportation/Correctness.lean",
    "Deutsch/Teleportation/Descriptors.lean",
    "Deutsch/Teleportation/Protocol.lean",
    "Deutsch/Teleportation/Statistics.lean",
    "Deutsch/Decoherence.lean",
    "Deutsch/Decoherence/Protocol.lean",
    "Deutsch/Decoherence/EPR.lean",
    "Deutsch/Decoherence/Correlation.lean",
    "Deutsch/Bell.lean",
    "Deutsch/Bell/Finite.lean",
    "Deutsch/Bell/Quantum.lean",
    "Deutsch/Bell/Moments.lean",
    "Deutsch/Bell/AngleMoments.lean",
    "Deutsch/Bell/Contradiction.lean",
    "Deutsch/Paper.lean",
    "Deutsch/Paper/QuantumTheory.lean",
    "Deutsch/Paper/Gates.lean",
    "Deutsch/Paper/EPRExperiment.lean",
    "Deutsch/Paper/EPRComparison.lean",
    "Deutsch/Paper/Teleportation.lean",
    "Deutsch/Paper/LocallyInaccessible.lean",
    "Deutsch/Paper/Bell.lean",
    "DeutschTests.lean",
    "DeutschTests/Audit.lean",
    "DeutschTests/Foundations/Abstract.lean",
    "DeutschTests/Foundations/Concrete.lean",
    "DeutschTests/Foundations/MatrixSemantics.lean",
    "DeutschTests/Gates.lean",
    "DeutschTests/Information.lean",
    "DeutschTests/Locality.lean",
    "DeutschTests/Paper.lean",
    "DeutschTests/Descriptor.lean",
    "DeutschTests/Register.lean",
    "DeutschTests/EPR.lean",
    "DeutschTests/Teleportation.lean",
    "DeutschTests/Decoherence.lean",
    "DeutschTests/Bell.lean",
    "DeutschTests/Examples.lean",
    "DeutschErrata.lean",
    "DeutschErrata/Rotation.lean",
    "DeutschErrata/EPR.lean",
    "DeutschErrata/Teleportation.lean",
    "DeutschErrata/Equation45.lean",
    "DeutschErrata/Bell.lean",
    "DeutschErrataTests.lean",
    "DeutschErrataTests/Comparisons.lean",
    "DeutschErrataTests/Audit.lean",
    "docs/conventions.md",
    "docs/registers.md",
    "docs/locality.md",
    "docs/descriptors.md",
    "docs/gates.md",
    "docs/information.md",
    "docs/epr.md",
    "docs/teleportation.md",
    "docs/decoherence.md",
    "docs/bell.md",
    "docs/paper.md",
    "docs/errata.md",
    "docs/reuse.md",
    "docs/project-report.md",
    "docs/representation.md",
    "goal-1/12-LIBRARY-AUDIT.md",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)

REQUIRED_FOUNDATION_ORACLES = (
    "pauli_x_mul_y",
    "pauli_y_mul_x",
    "pauli_squares",
    "pauli_hermitian",
    "pauli_traces",
    "pauli_unitary",
    "paper_bit_projectors",
    "paper_bit_z_eigenvalues",
    "fin_pair_basis_order",
    "x_left_factor_all_basis",
    "x_right_factor_all_basis",
    "phase_gate_pins_heisenberg_direction",
    "opposite_phase_conjugation_differs",
    "phase_gate_transforms_x_eigenvectors",
    "cnot_basis_00",
    "cnot_basis_10",
    "cnot_basis_01",
    "cnot_basis_11",
    "cnot_projector_formula_is_explicit_permutation",
    "cnot_conjugates_target_x",
    "cnot_conjugates_target_y",
    "cnot_conjugates_target_z",
    "cnot_conjugates_control_x",
    "cnot_conjugates_control_y",
    "cnot_conjugates_control_z",
    "rx_pi_div_two_pins_heisenberg_y",
    "rx_pi_div_two_pins_heisenberg_z",
    "paper_bell_chronology_inverse_left",
    "paper_bell_chronology_inverse_right",
    "disjoint_binary_operators_commute",
    "tensor_adjoint",
    "binary_locality_api_probe",
    "sum_probability_eq_one",
    "disjoint_matrix_operators_commute",
    "bornProbabilities_normalize",
    "maximallyMixed_probability_zero",
    "maximallyMixed_probabilities_normalize",
)

REQUIRED_REGISTER_ORACLES = (
    "card_basis_three",
    "paper_zero_is_raw_one_on_three_qubits",
    "paper_zero_is_not_raw_zero",
    "referenceKet_three_qubits_normalized",
    "every_pure_three_qubit_state_has_a_unitary_preparation",
    "coordinate_zero_is_left_kronecker_factor",
    "coordinate_one_is_right_kronecker_factor",
    "xAt_zero_all_three_qubit_entries",
    "xAt_two_all_three_qubit_entries",
    "nonadjacent_three_qubit_coordinates_commute",
    "ordered_placement_swaps_the_local_first_coordinate",
    "opposite_order_does_not_swap_the_local_first_coordinate",
    "the_two_ordered_placements_are_distinct",
    "supported_pauli_polynomial",
    "supported_heisenberg_conjugate",
    "zero_operator_does_not_preserve_reference_norm",
    "zero_operator_does_not_preserve_the_identity_in_heisenberg_form",
    "eigenvector_transport_by_xAt",
)

REQUIRED_REGISTER_PUBLIC_DECLARATIONS = {
    "Deutsch/Register/Basic.lean": (
        "matrixEndEquiv_apply",
        "matrixEndEquiv_conjTranspose",
        "heisenberg_chronology",
    ),
    "Deutsch/Register/Embedding.lean": (
        "embedSubsystem_mul",
        "embedSubsystem_conjTranspose",
        "embedSubsystem_injective",
        "IsSupportedOn.mono",
        "IsSupportedOn.heisenberg",
        "embedAlong_apply_ite",
        "embedAlong_conjTranspose",
        "embedAlong_injective",
        "embedAlong_heisenberg",
    ),
    "Deutsch/Register/Pauli.lean": (
        "embedQubit_commute_of_ne",
        "xAt_mul_yAt",
        "xAt_isHermitian",
        "xAt_unitary",
        "paperBitOneProjectorAt_mul_self",
        "paperBitOneProjectorAt_eq",
        "paperBitProjectorAt_sum",
    ),
    "Deutsch/Register/State.lean": (
        "norm_basisKet",
        "basisKet_expectation",
        "norm_act_unitary",
        "expectation_after_action",
        "fixed_reference_prediction",
        "heisenberg_eigenvector",
        "exists_unitary_act_reference",
        "PureState.exists_unitary_preparation",
        "PureState.exists_fixed_reference_representation",
    ),
}

REQUIRED_REGISTER_AUDIT_TARGETS = tuple(
    f"Deutsch.Register.{name}"
    for declarations in REQUIRED_REGISTER_PUBLIC_DECLARATIONS.values()
    for name in declarations
)

REQUIRED_LOCALITY_ORACLES = (
    "evenSites_disjoint_remoteSites",
    "nonadjacent_multi_label_embeddings_commute",
    "semantic_nonadjacent_supported_operators_commute",
    "singleton_local_x_fixes_remote_z",
    "arbitrary_ket_remote_z_expectation_is_invariant",
    "arbitrary_ket_heisenberg_expectation_is_invariant",
    "bellKet_not_product",
    "norm_bellKet",
    "bellKet_remote_z_expectation_is_invariant",
    "bellKet_remote_z_heisenberg_expectation_is_invariant",
    "empty_support_commutes_with_any_supported_operator",
    "embedded_empty_subsystem_commutes",
    "same_coordinate_x_and_z_do_not_commute",
    "overlapping_x_changes_z",
    "overlapping_supported_unitary_does_not_fix_z",
    "xAt_zero_not_supported_on_one",
    "zero_has_disjoint_support_but_does_not_fix_remote_z",
)

REQUIRED_LOCALITY_PUBLIC_DECLARATIONS = {
    "Deutsch/Locality/Basic.lean": (
        "embedSubsystem_mul_embedSubsystem_apply_of_disjoint",
        "embedSubsystem_commute_of_disjoint",
        "supportedOperators_commute_of_disjoint",
    ),
    "Deutsch/Locality/Heisenberg.lean": (
        "heisenberg_eq_gram_mul_of_commute",
        "heisenberg_eq_self_of_commute_of_isometry",
        "heisenberg_eq_self_of_disjoint_support_of_isometry",
        "heisenberg_eq_self_of_disjoint_support",
        "expectation_heisenberg_eq_of_disjoint_support",
        "expectation_after_local_unitary_eq",
    ),
}

REQUIRED_LOCALITY_AUDIT_TARGETS = tuple(
    f"Deutsch.Locality.{name}"
    for declarations in REQUIRED_LOCALITY_PUBLIC_DECLARATIONS.values()
    for name in declarations
)

REQUIRED_DESCRIPTOR_ORACLES = (
    "initial_descriptor_one_valid",
    "initial_family_two_valid",
    "initial_family_three_valid",
    "initial_family_three_all_cross_relations",
    "x_evolved_three_family_valid",
    "x_evolved_three_family_preserves_every_cross_relation",
    "initial_empty_family_generates_operator_algebra",
    "initial_three_family_generates_operator_algebra",
    "x_evolved_three_family_generates_operator_algebra",
    "every_empty_register_operator_reconstructs",
    "every_three_qubit_operator_reconstructs",
    "every_x_evolved_three_qubit_operator_reconstructs",
    "one_site_pauli_word_is_initial_descriptor",
    "one_site_evolved_word_is_evolved_descriptor",
    "pauli_basis_is_exact_on_three_qubits",
    "zero_descriptor_not_valid",
    "identity_descriptor_not_valid",
    "zero_nonunitary_evolution_not_valid",
    "repeated_family_not_pairwise_commuting",
    "empty_initial_family_valid",
    "every_singleton_family_cross_condition_is_vacuous",
    "reference_stabilizer_fixes_reference",
    "conjugated_initial_is_unitarily_conjugate",
    "conjugated_initial_is_reference_expectation_equivalent",
    "conjugated_initial_is_not_operator_equal",
)

REQUIRED_DESCRIPTOR_PUBLIC_DECLARATIONS = {
    "Deutsch/Descriptor/Basic.lean": (
        "component_unitary",
        "mul_yx",
        "anticommutes_next",
        "initial_component_isSupportedOn",
        "initial_valid",
        "Valid.evolve",
        "initial_pairwiseCommutes",
        "PairwiseCommutes.evolve",
    ),
    "Deutsch/Descriptor/Generation.lean": (
        "reconstructedMatrixUnit_eq_single",
        "initial_generates_operator_algebra",
        "GeneratesOperatorAlgebra.evolve",
    ),
    "Deutsch/Descriptor/PauliBasis.lean": (
        "reconstruction",
        "basis_apply",
        "evolvedReconstruction",
        "evolvedPauliString_single",
    ),
    "Deutsch/Descriptor/Comparison.lean": (
        "isUnitaryConjugate_equivalence",
        "referenceExpectationEquivalent_of_eq",
        "referenceExpectationEquivalent_evolve_of_fixes_reference",
    ),
}

REQUIRED_GATE_ORACLES = (
    "not_swaps_paper_one_to_zero",
    "not_swaps_paper_zero_to_one",
    "paper_sqrt_not_squares_exactly_to_not",
    "paper_sqrt_not_is_not_positive_pi_half_rotation",
    "rotation_y_at_negative_pi_half_maps_to_positive_z",
    "rotation_z_at_negative_pi_half_maps_to_negative_y",
    "diagonal_rotation_phase_cancels_on_y",
    "arbitrary_valid_descriptor_not_has_paper_map",
    "non_coordinate_axis_has_rodrigues_action",
    "non_coordinate_axis_uses_matrix_exponential",
    "non_coordinate_axis_rotation_is_unitary",
    "arbitrary_axis_x_specialization_is_rotationX",
    "arbitrary_axis_x_pi_half_maps_y_to_negative_z",
    "named_non_coordinate_axis_uses_global_matrix_exponential",
    "current_non_coordinate_axis_is_transported_named_gate",
    "transported_named_gate_has_current_exponential_action",
    "current_non_coordinate_axis_has_rodrigues_action",
    "current_x_axis_has_correct_y_sign",
    "rotation_on_zero_fixes_remote_z",
    "named_cnot_inactive_on_paper_zero_control",
    "named_cnot_active_on_paper_one_control",
    "named_cnot_second_inactive_case",
    "named_cnot_second_active_case",
    "reversing_cnot_target_control_changes_the_gate",
    "named_cnot_on_zero_two_fixes_middle_z",
    "initial_descriptor_cnot_is_typed_global_formula",
    "every_valid_descriptor_cnot_is_unitary",
    "every_valid_descriptor_cnot_has_target_y_map",
    "every_valid_descriptor_cnot_has_control_x_map",
    "bell_named_inverse_left",
    "bell_named_inverse_right",
    "bell_equation20_control_y_sign",
    "bell_inverse_equation21_target_z_sign",
    "bell_forward_has_direct_basis_amplitude",
    "reversing_bell_chronology_changes_the_gate",
    "bell_on_zero_two_fixes_middle_z",
    "bell_inverse_on_zero_two_fixes_middle_z",
)

REQUIRED_GATE_PUBLIC_DECLARATIONS = {
    "Deutsch/Register/Basic.lean": (
        "heisenberg_smul",
        "heisenberg_covariance",
    ),
    "Deutsch/Register/Embedding.lean": (
        "embedAlong_embedQubit",
    ),
    "Deutsch/Gates/OneQubit.lean": (
        "not_matrix_entry",
        "paperSqrtNot_square",
        "paperSqrtNot_heisenberg_twice",
        "rotationX_unitary",
        "rotationX_heisenberg_y",
        "rotationX_heisenberg_z",
        "rotationX_heisenberg_y_neg_pi_div_two",
        "rotationX_heisenberg_z_neg_pi_div_two",
        "diagonalPiRotation_eq_globalPhase_hadamard",
        "diagonalPiRotation_heisenberg",
        "descriptorNot_evolve",
        "rotationXAt_heisenberg_y",
        "hadamardAt_heisenberg_z",
    ),
    "Deutsch/Gates/AxisRotation.lean": (
        "pauliVector_mul_pauliVector",
        "axisPauli_sq",
        "axisPauli_isHermitian",
        "axisPauli_unitary",
        "axisPauli_xAxis",
        "exp_axisRotationGenerator",
        "exp_positive_axisGenerator",
        "axisRotation_isUnitary",
        "axisRotation_conjTranspose",
        "axisRotation_heisenberg_eq_exponential_conjugation",
        "axisRotation_heisenberg",
        "axisRotation_xAxis",
    ),
    "Deutsch/Gates/AxisRotationRegister.lean": (
        "exp_axisRotationGeneratorAt",
        "axisRotationAt_unitary",
        "currentAxisPauli_eq_heisenberg",
        "currentAxisRotation_eq_heisenberg",
        "axisRotationAt_heisenberg_current_component_exp",
        "currentAxisRotation_heisenberg",
    ),
    "Deutsch/Gates/CNOT.lean": (
        "cnotAt_apply",
        "cnotAt_act_basisKet",
        "cnotAt_unitary",
        "cnotAt_isSupportedOn_pair",
        "cnotAt_eq_global_formula",
        "cnotAt_conjugates_target_y",
        "cnotAt_conjugates_control_x",
        "cnotFromDescriptors_mul_self",
        "cnotFromDescriptors_unitary",
        "cnotFromDescriptors_conjugates_target_x",
        "cnotFromDescriptors_conjugates_target_y",
        "cnotFromDescriptors_conjugates_target_z",
        "cnotFromDescriptors_conjugates_control_x",
        "cnotFromDescriptors_conjugates_control_y",
        "cnotFromDescriptors_conjugates_control_z",
        "cnotFromDescriptors_initial_eq_cnotAt",
        "cnotFromDescriptors_evolve",
    ),
    "Deutsch/Gates/Bell.lean": (
        "bellAt_unitary",
        "bellInverseAt_unitary",
        "bellAt_inverse_left",
        "bellAt_inverse_right",
        "bellAt_conjugates_target_x",
        "bellAt_conjugates_target_y",
        "bellAt_conjugates_target_z",
        "bellAt_conjugates_control_x",
        "bellAt_conjugates_control_y",
        "bellAt_conjugates_control_z",
        "bellInverseAt_conjugates_target_x",
        "bellInverseAt_conjugates_target_y",
        "bellInverseAt_conjugates_target_z",
        "bellInverseAt_conjugates_control_x",
        "bellInverseAt_conjugates_control_y",
        "bellInverseAt_conjugates_control_z",
        "bellAt_isSupportedOn",
        "bellInverseAt_isSupportedOn",
        "bellAt_apply",
        "bellInverseAt_apply",
    ),
}

REQUIRED_GATE_AUDIT_TARGETS = tuple(
    f"Deutsch.Register.{name}"
    for name in REQUIRED_GATE_PUBLIC_DECLARATIONS["Deutsch/Register/Basic.lean"]
) + (
    "Deutsch.Register.embedAlong_embedQubit",
) + tuple(
    f"Deutsch.Gates.{name}"
    for path, declarations in REQUIRED_GATE_PUBLIC_DECLARATIONS.items()
    if path.startswith("Deutsch/Gates/")
    for name in declarations
)

REQUIRED_DESCRIPTOR_AUDIT_TARGETS = (
    "Deutsch.Descriptor.Valid.component_unitary",
    "Deutsch.Descriptor.Valid.mul_yx",
    "Deutsch.Descriptor.Valid.anticommutes_next",
    "Deutsch.Descriptor.initial_component_isSupportedOn",
    "Deutsch.Descriptor.initial_valid",
    "Deutsch.Descriptor.Valid.evolve",
    "Deutsch.DescriptorFamily.initial_pairwiseCommutes",
    "Deutsch.DescriptorFamily.initial_valid",
    "Deutsch.DescriptorFamily.PairwiseCommutes.evolve",
    "Deutsch.DescriptorFamily.Valid.evolve",
    "Deutsch.DescriptorFamily.Generation.reconstructedMatrixUnit_eq_single",
    "Deutsch.DescriptorFamily.initial_generates_operator_algebra",
    "Deutsch.DescriptorFamily.GeneratesOperatorAlgebra.evolve",
    "Deutsch.PauliWord.reconstruction",
    "Deutsch.PauliWord.basis_apply",
    "Deutsch.PauliWord.evolvedReconstruction",
    "Deutsch.PauliWord.evolvedPauliString_single",
    "Deutsch.DescriptorFamily.isUnitaryConjugate_equivalence",
    "Deutsch.DescriptorFamily.referenceExpectationEquivalent_of_eq",
    "Deutsch.DescriptorFamily.referenceExpectationEquivalent_evolve_of_fixes_reference",
)

REQUIRED_INFORMATION_ORACLES = (
    "arbitrary_born_probability_is_bounded",
    "computational_basis_hit_is_certain",
    "computational_basis_miss_is_impossible",
    "computational_basis_measurement_normalizes",
    "binary_effect_measurement_normalizes",
    "paper_bit_one_is_the_z_plus_effect",
    "pure_density_uses_existing_expectation",
    "partial_trace_preserves_trace",
    "partial_trace_preserves_positivity",
    "reduced_local_effect_has_global_probability",
    "one_qubit_all_effects_determine_density",
    "arbitrary_register_all_effects_determine_density",
    "one_qubit_pauli_statistics_determine_density",
    "singleton_reduction_is_exactly_all_local_statistics",
    "arbitrary_reduction_is_exactly_all_local_statistics",
    "maximally_mixed_not_fixed_pure_reference",
    "identity_channel_fixes_every_density",
    "channel_duality_preserves_born_probability",
    "channel_composition_has_expected_density_action",
    "fixed_channel_preserves_parameter_independence",
    "local_channel_preserves_every_disjoint_reduced_state",
    "different_basis_states_are_weakly_distinguishable",
    "all_effect_statistics_equal_iff_density_equal",
    "basis_bit_family_is_detectable",
    "constant_family_is_statistically_independent",
    "identity_channel_recovers_exactly",
    "constant_final_family_can_have_nonconstant_provenance",
    "one_time_pad_each_singleton_is_secret_independent",
    "one_time_pad_parity_reads_secret_with_certainty",
    "one_time_pad_encodings_are_jointly_detectable",
    "one_time_pad_physical_decoder_recovers",
    "one_time_pad_histories_are_pointwise_distinct",
    "one_time_pad_distinct_histories_have_same_final_density",
)

REQUIRED_INFORMATION_PUBLIC_DECLARATIONS = {
    "Deutsch/Information/State.lean": (
        "density_le_one",
        "Density.toEffect_op",
        "trace_mul_nonneg_of_posSemidef",
        "bornWeight_eq_probability",
        "bornProbability_nonneg",
        "bornProbability_le_one",
        "density_eq_iff_effect_probabilities",
        "bornProbabilities_normalize",
        "Effect.binaryPOVM_true",
        "densityExpectation_pureDensity",
        "basisDensity_basisEffect_probability",
        "densityExpectation_evolve",
        "purity_evolve",
        "pureDensity_basisState",
        "basisDensity_expectation",
        "referenceDensity_expectation",
        "pureDensity_evolve",
    ),
    "Deutsch/Information/Reduction.lean": (
        "partialTrace_add",
        "partialTrace_smul",
        "partialTrace_basisDensity",
        "partialTrace_posSemidef",
        "partialTrace_trace",
        "partialTrace_trace_mul",
        "bornProbability_reduce",
        "reduced_density_eq_iff_embedded_effect_probabilities",
        "Effect.embedAlong_op",
        "referenceDensity_expectation_embedAlong",
    ),
    "Deutsch/Information/Channel.lean": (
        "KrausChannel.mapOperator_add",
        "KrausChannel.mapOperator_smul",
        "KrausChannel.mapOperator_zero",
        "KrausChannel.mapOperator_posSemidef",
        "KrausChannel.trace_mapOperator",
        "KrausChannel.trace_duality",
        "KrausChannel.bornProbability_mapDensity",
        "identityChannel_mapDensity",
        "unitaryChannel_mapDensity",
        "KrausChannel.comp_mapDensity",
    ),
    "Deutsch/Information/LocalChannel.lean": (
        "KrausChannel.onSubsystem_dualOperator_embedSubsystem_of_disjoint",
        "KrausChannel.onSubsystem_dualEffect_embedSubsystem_of_disjoint",
        "KrausChannel.onSubsystem_bornProbability_disjoint",
        "KrausChannel.onSubsystem_reduce_disjoint",
    ),
    "Deutsch/Information/Dependence.lean": (
        "weaklyDistinguishable_iff_not_effectStatisticallyEquivalent",
        "effectStatisticallyEquivalent_iff_eq",
        "weaklyDistinguishable_iff_ne",
        "reducedStateEquivalent_iff_localEffectStatisticallyEquivalent",
        "localEffectStatisticallyEquivalent_iff_embedded",
        "statisticallyDetectable_iff_not_statisticsIndependent",
        "statisticsIndependent_iff_constant",
        "statisticallyDetectable_iff_exists_ne",
        "LocallyDetectable.statisticallyDetectable",
        "StatisticsIndependent.locallyStatisticsIndependent",
        "KrausChannel.effectStatisticallyEquivalent_mapDensity",
        "KrausChannel.weaklyDistinguishable_input_of_output",
        "KrausChannel.statisticsIndependent_mapDensity",
        "Recovers.encoded_ne_of_target_ne",
        "StatisticallyDetectable.of_recovers_channel",
        "DescriptorNonconstant.not_constant",
        "constantPreparation_provenanceNonconstant",
        "constantPreparations_same_final_family",
    ),
    "Deutsch/Information/Qubit.lean": (
        "maximallyMixedQubit_purity",
        "basisDensity_purity",
        "maximallyMixedQubit_cannot_evolve_to_reference",
        "xPlusEffect_op",
        "yPlusEffect_op",
        "zPlusEffect_op",
        "zPlusEffect_op_eq_paperBitOneProjectorAt",
        "qubitMatrix_eq_of_pauli_traces_eq",
        "density_eq_of_pauliPlus_probabilities",
        "reduce_eq_iff_embedded_pauliPlus_probabilities",
        "reduce_singleton_eq_iff_embedded_effect_probabilities",
    ),
    "Deutsch/Information/OneTimePad.lean": (
        "oneTimePadDensity_op",
        "swappedOneTimePadDensity_eq",
        "oneTimePadDensity_reduce_singleton",
        "oneTimePad_locallyStatisticsIndependent",
        "oneTimePadBasis_parity",
        "parityEffect_op",
        "oneTimePadDensity_parity_probability",
        "oneTimePadDensity_weaklyDistinguishable",
        "oneTimePad_statisticallyDetectable",
        "parityDecoder_recovers_density",
        "parityDecoder_recovers",
        "oneTimePad_preparation_histories_distinct",
        "oneTimePad_preparations_same_final_density",
        "oneTimePadPreparationLeft_provenanceNonconstant",
    ),
}

REQUIRED_INFORMATION_AUDIT_TARGETS = tuple(
    f"Deutsch.Information.{name}"
    for declarations in REQUIRED_INFORMATION_PUBLIC_DECLARATIONS.values()
    for name in declarations
)

REQUIRED_EPR_ORACLES = (
    "equation22_has_explicit_global_phase",
    "equation22_library_ket_has_correct_relative_sign",
    "pair_and_time_boundaries_are_unitary",
    "equation23_q2_descriptor_is_exact",
    "equation23_q3_descriptor_is_exact",
    "equation24_remote_descriptors_are_untouched",
    "equation25_q2_sine_components",
    "equation25_q3_sine_components",
    "equation27_q1_record_is_factored_through_time_two",
    "equation27_q2_record_is_factored_through_time_two",
    "equation27_q3_record_is_factored_through_time_two",
    "equation27_q4_record_is_factored_through_time_two",
    "equation38_has_explicit_global_phase",
    "equation39_routes_prepare_the_same_ket",
    "four_wire_record_effects_pin_paper_one_as_raw_zero",
    "equation40_is_derived_on_the_four_wire_records",
    "equation41_is_derived_on_the_four_wire_records",
    "equation28_is_derived_after_the_four_wire_comparison",
    "every_four_wire_record_outcome_matches_the_pair_density",
    "four_wire_record_and_comparison_statistics_match_the_pair_density",
    "equal_settings_are_a_four_wire_boundary",
    "relative_pi_is_a_four_wire_boundary",
    "both_pair_marginals_are_maximally_mixed",
    "every_singleton_effect_is_setting_independent",
    "equation28_has_sine_square_probability",
    "equation40_marginals_are_one_half",
    "equation41_has_cosine_square_probability",
    "pi_separated_settings_force_different_outcomes",
    "epr_resource_zz_correlation_is_nonproduct",
    "finite_setting_family_is_local_but_jointly_detectable",
    "equation39_routes_have_equal_density_but_distinct_histories",
)

REQUIRED_EPR_PUBLIC_DECLARATIONS = {
    "Deutsch/EPR/Pair.lean": (
        "pairPreparation_unitary",
        "pairCircuit_unitary",
        "pairKet_eq",
        "equation22Ket_eq_globalPhase",
        "pairCircuit_referenceKet_eq_four_coordinates",
        "equation39_route_kets_eq",
    ),
    "Deutsch/EPR/Circuit.lean": (
        "timeFourUnitary_unitary",
        "timeOneUnitary_isSupportedOn",
        "timeTwoUnitary_isSupportedOn",
        "equation23_q2",
        "equation23_q3",
        "equation24_q1",
        "equation24_q4",
        "equation25_q2",
        "equation25_q3",
        "equation27_q1",
        "equation27_q2",
        "equation27_q3",
        "equation27_q4",
    ),
    "Deutsch/EPR/Statistics.lean": (
        "sameCoefficient_eq_cos_sub_half",
        "crossCoefficient_eq_I_mul_sin_sub_half",
        "equation38Ket_eq_globalPhase_pairPureState",
        "pairDensity_reduce_singleton",
        "pairDensity_locallyStatisticsIndependent",
        "pairDensity_different_probability",
        "pairDensity_jointPaperOne_probability",
        "pairDensity_paperOne_marginal_probability",
        "differentEffect_op_eq_unequal_basis_sum",
        "pairDensity_different_equal_settings",
        "pairDensity_jointPaperOne_equal_settings",
        "pairDensity_different_pi_zero",
        "pairSettingFamily_locallyStatisticsIndependent",
        "pairSettingFamily_statisticallyDetectable",
        "pairDensity_z_expectation",
        "pairDensity_equal_settings_zz_expectation",
        "pairDensity_zero_resource_correlation",
    ),
    "Deutsch/EPR/RecordStatistics.lean": (
        "timeTwoUnitary_eq_embedAlong_pairCircuit",
        "timeTwoPureKet_eq_liftPair",
        "recordingLayer_liftPairKet",
        "fourWireTimeThreeDensity_eq_referenceDensity_evolve",
        "fourWireTimeFourDensity_eq_referenceDensity_evolve",
        "fourWireTimeThreePureState_ket",
        "recordOutcomeEffect_eq_embedAlong",
        "fourWireTimeThree_recordOutcome_probability",
        "fourWireTimeThree_recordOutcome_probability_eq_pairDensity",
        "fourWireTimeThree_leftRecord_probability",
        "fourWireTimeThree_rightRecord_probability",
        "fourWireTimeThree_leftRecord_probability_eq_pairDensity",
        "fourWireTimeThree_rightRecord_probability_eq_pairDensity",
        "fourWireTimeThree_jointRecord_probability_eq_pairDensity",
        "fourWireTimeThree_jointRecord_probability",
        "fourWireTimeFourPureState_ket",
        "fourWireTimeFour_comparison_probability_eq_unequal_pair_sum",
        "fourWireTimeFour_comparison_probability",
        "fourWireTimeFour_comparison_probability_eq_pairDensity",
        "fourWireTimeFour_comparison_equal_settings",
        "fourWireTimeFour_comparison_relative_pi",
    ),
    "Deutsch/EPR/Provenance.lean": (
        "equation39_route_densities_eq",
        "leftRouteDensity_eq_pairDensity",
        "rightRouteDensity_eq_pairDensity",
        "routePreparation_histories_distinct",
        "routePreparations_same_final_density",
    ),
}

REQUIRED_EPR_AUDIT_TARGETS = tuple(
    f"Deutsch.EPR.{name}"
    for declarations in REQUIRED_EPR_PUBLIC_DECLARATIONS.values()
    for name in declarations
)

REQUIRED_TELEPORTATION_ORACLES = (
    "all_five_wire_boundaries_are_unitary",
    "all_five_wire_boundaries_have_explicit_finite_support",
    "equation29_rotation_components",
    "equation30_resource_descriptor_is_exact",
    "equation31_input_descriptor_components",
    "equation32_record_descriptor_components",
    "equation34_receiver_descriptor",
    "equation37_final_observable",
    "equation33_checks_all_nine_generators",
    "correction_branch_matrices_are_explicit",
    "every_complex_amplitude_pair_factorizes",
    "nontrivial_phase_superposition_factorizes",
    "nontrivial_real_superposition_factorizes",
    "arbitrary_normalized_receiver_density",
    "decoder_after_encoder_is_identity_on_every_operator",
    "decoder_recovers_every_density",
    "every_encoded_singleton_is_input_independent",
    "recordK_and_receiver_are_jointly_detectable",
    "local_inaccessibility_and_global_detection_coexist",
    "both_record_corrections_have_nonidentity_omission_witnesses",
    "both_record_corrections_have_observable_omission_witnesses",
    "supplied_protocol_history_is_nonconstant",
    "supplied_protocol_history_names_alice_to_bob",
    "equation36_is_receiver_density_equality",
    "equation36_has_receiver_bloch_vector",
    "equation36_is_all_effect_prediction_equality",
    "equation35_rank_one_effect_is_certain",
    "equation35_receiver_is_explicitly_pure",
    "final_inverse_rotation_verifies_paper_zero",
    "final_verification_effect_is_the_paper_zero_projector",
    "evolved_five_wire_output_verifies_paper_zero",
    "literal_timeFive_circuit_verifies_paper_zero",
)

REQUIRED_TELEPORTATION_PUBLIC_DECLARATIONS = {
    "Deutsch/Teleportation/Circuit.lean": (
        "inputRotation_unitary",
        "timeThreeUnitary_unitary",
        "inputRotation_isSupportedOn",
        "timeOneUnitary_isSupportedOn",
        "timeTwoUnitary_isSupportedOn",
        "timeThreeUnitary_isSupportedOn",
        "recordingGates_commute",
        "equation29_q1",
        "equation30_q4",
        "equation30_q5",
        "equation31_q1",
        "equation31_q4",
        "equation32_q2",
        "equation32_q3",
    ),
    "Deutsch/Teleportation/Correction.lean": (
        "controlledZAt_isSupportedOn_pair",
        "correctionGate_isSupportedOn_triple",
        "correctionGate_unitary",
        "equation33_k_x",
        "equation33_k_y",
        "equation33_k_z",
        "equation33_l_x",
        "equation33_l_y",
        "equation33_l_z",
        "equation33_m_x",
        "equation33_m_y",
        "equation33_m_z",
        "correctionGate_branch_paper00",
        "correctionGate_branch_paper01",
        "correctionGate_branch_paper10",
        "correctionGate_branch_paper11",
    ),
    "Deutsch/Teleportation/Descriptors.lean": (
        "equation34_q5",
        "teleportCorrectionGate_isSupportedOn",
        "timeFourUnitary_isSupportedOn",
        "timeFive_q5_z",
        "verificationRotation_isSupportedOn",
        "timeFiveUnitary_isSupportedOn",
    ),
    "Deutsch/Teleportation/Correctness.lean": (
        "coherentProtocol_unitary",
        "coherentPreCorrection_exact",
        "coherentProtocol_factorizes",
        "teleportedDensity_reduce_receiver",
    ),
    "Deutsch/Teleportation/Protocol.lean": (
        "protocolCorrectionGate_eq_branch_on_basis",
        "protocolBranchCorrection_paper00",
        "protocolBranchCorrection_paper01",
        "protocolBranchCorrection_paper10",
        "protocolBranchCorrection_paper11",
        "protocolBranchCorrection_unitary",
        "protocolDecoder_encoder_mapOperator",
        "protocolDecoder_encoder_mapDensity",
        "protocolDecoder_recovers",
        "protocolEncodedFamily_reduce_singleton",
        "protocolEncodedFamily_locallyStatisticsIndependent",
        "protocolDecoder_recovers_inputFamily",
        "protocolEncodedFamily_jointRegister_statisticallyDetectable",
        "protocolEncodedFamily_recordK_receiver_jointlyDetectable",
        "protocolEncodedFamily_singleton_inaccessible_globally_detectable",
        "protocol_omit_recordK_correction_leaves_nonidentity",
        "protocol_omit_recordL_correction_leaves_nonidentity",
        "protocol_omit_recordK_changes_receiver_z_observable",
        "protocol_omit_recordL_changes_receiver_x_observable",
        "protocolPreparation_supplied_transport",
        "protocolPreparation_provenanceNonconstant",
    ),
    "Deutsch/Teleportation/Statistics.lean": (
        "inputRotation_act_reference",
        "timeFourUnitary_eq_coherentProtocol_mul_inputRotation",
        "timeFour_act_reference_factorizes",
        "equation36_receiver_bloch_operator",
        "equation36_receiver_bloch_vector",
        "equation36_receiver_density",
        "equation36_receiver_all_effects",
        "equation35Effect",
        "equation35_effect_op",
        "equation35_receiver_purity",
        "equation35_teleported_probability_one",
        "receiverPaperZeroEffect_op_eq_projector",
        "u02_paperZero_heisenberg",
        "u02_paperZero_probability_one",
        "timeFive_teleported_paperZero_probability_one",
        "timeFive_reference_output_paperZero_probability_one",
    ),
}

REQUIRED_TELEPORTATION_AUDIT_TARGETS = tuple(
    f"Deutsch.Teleportation.{name}"
    for declarations in REQUIRED_TELEPORTATION_PUBLIC_DECLARATIONS.values()
    for name in declarations
)

REQUIRED_DECOHERENCE_ORACLES = (
    "dephasing_keeps_exactly_one_coordinate_block",
    "dephasing_fixed_points_are_exactly_block_diagonal",
    "dephasing_fixes_every_computational_basis_density",
    "repeated_dephasing_is_idempotent",
    "every_finite_repetition_preserves_the_selected_z_statistic",
    "wrong_basis_x_effect_is_not_stable",
    "classical_bit_error_changes_z_probability",
    "supplied_environment_is_paper_zero",
    "supplied_cnot_environment_coupling_is_unitary",
    "discarded_cnot_environment_realizes_dephasing",
    "record_dephasing_keeps_exactly_equal_record_blocks",
    "every_semantic_encoder_operator_is_record_classical",
    "decoder_recovers_after_record_dephasing",
    "real_record_bit_flip_changes_the_encoded_family",
    "record_bit_flip_makes_exact_recovery_fail",
    "repeated_q4_dephasing_preserves_the_final_comparison",
    "classical_mixture_has_the_same_three_z_moments_as_the_bell_resource",
    "nonproduct_z_correlation_does_not_identify_the_bell_density",
)

REQUIRED_DECOHERENCE_PUBLIC_DECLARATIONS = {
    "Deutsch/Information/Dephasing.lean": (
        "coordinateDephasing_mapOperator_apply",
        "coordinateDephasing_trace",
        "coordinateDephasing_fixes_operator_iff",
        "coordinateDephasing_map_basisDensity",
        "coordinateDephasing_mapDensity_idempotent",
        "coordinateDephasing_dual_zPlusEffect",
        "coordinateDephasing_preserves_zPlusProbability_iterate",
        "coordinateDephasing_changes_xPlusEffect",
        "classicalBitFlip_changes_zPlusProbability",
        "cnotEnvironmentState_eq_basisDensity",
        "cnotEnvironmentCoupling_unitary",
        "cnotEnvironmentKraus_eq_coordinateDephasingKraus",
        "cnotEnvironmentDephasing_mapDensity",
    ),
    "Deutsch/Decoherence/Protocol.lean": (
        "protocolRecordDephasing_mapOperator_apply",
        "protocolRecordDephasing_encoder_mapOperator",
        "protocolRecordDephasing_encoder_mapDensity",
        "protocolDecoder_after_recordDephasing",
        "protocolRecordKBitFlip_encodedFamily",
        "protocolDecoder_after_recordKBitFlip",
        "protocolDecoder_after_recordKBitFlip_fails",
    ),
    "Deutsch/Decoherence/EPR.lean": (
        "comparisonGate_heisenberg_q1_z",
        "eprComparisonPaperOneEffect_op",
        "coordinateDephasing_q4_fixes_eprComparisonPaperOneEffect",
        "coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability_iterate",
        "epr_c34_q4_dephasing_before_comparison",
        "epr_c34_q4_dephasing_before_comparison_iterate",
    ),
    "Deutsch/Decoherence/Correlation.lean": (
        "classicallyCorrelatedDensity_op",
        "classicallyCorrelatedDensity_left_z_expectation",
        "classicallyCorrelatedDensity_right_z_expectation",
        "classicallyCorrelatedDensity_zz_expectation",
        "classicallyCorrelatedDensity_matches_pairDensity_zero_z_moments",
        "classicallyCorrelatedDensity_correlation",
        "classicallyCorrelatedDensity_ne_pairDensity_zero",
    ),
}

REQUIRED_DECOHERENCE_AUDIT_TARGETS = tuple(
    ("Deutsch.Information." if path.startswith("Deutsch/Information/")
      else "Deutsch.Decoherence.") + name
    for path, declarations in REQUIRED_DECOHERENCE_PUBLIC_DECLARATIONS.items()
    for name in declarations
)

REQUIRED_BELL_ORACLES = (
    "direct_equation42_mean_square",
    "direct_equation43_positive_support",
    "direct_equation44_alice_joint_moment",
    "direct_equation45_true_complementary_partition",
    "direct_equation46_all_displayed_comparisons",
    "direct_equation46_reaches_the_impossible_bound",
    "zero_weight_sample_can_disagree_despite_zero_mean_square",
    "every_three_bit_assignment_has_an_agreeing_pair",
    "every_common_assignment_distribution_obeys_the_bell_bound",
    "every_explicit_two_party_local_model_obeys_the_bell_bound",
    "probability_one_equal_settings_force_positive_support_agreement",
    "three_quarter_agreements_are_impossible_for_the_local_model",
    "raw_to_paper_relabeling_preserves_outcome_agreement",
    "same_outcome_probability_is_cosine_squared",
    "all_distinct_three_setting_pairs_have_probability_one_quarter",
    "all_equal_three_setting_pairs_agree_certainly",
    "epr_predictions_refute_the_explicit_local_model",
    "no_explicit_local_model_reproduces_the_epr_family",
    "epr_probabilities_alone_refute_the_normalized_local_model",
    "no_normalized_local_model_reproduces_the_epr_family",
    "both_finite_bell_routes_reject_their_named_contracts",
)

REQUIRED_BELL_PUBLIC_DECLARATIONS = {
    "Deutsch/Bell/Finite.lean": (
        "commonAssignment_has_agreeing_pair",
        "commonAssignment_indicator_sum_ge_one",
        "three_setting_bell_inequality",
        "quarter_agreements_contradict_common_assignment",
        "no_common_assignment_has_three_quarter_agreements",
        "perfectEqualSettingSupport_of_agreementProbability_one",
        "local_three_setting_bell_inequality",
        "local_three_setting_bell_inequality_of_equal_setting_probability_one",
        "quarter_agreements_contradict_local_assignments",
        "quarter_agreements_contradict_local_assignments_of_equal_setting_probability_one",
        "no_local_assignment_has_three_quarter_agreements",
    ),
    "Deutsch/Bell/Quantum.lean": (
        "paperBits_equal_iff_rawBits_equal",
        "sameOutcomeProbability_eq_cos_sq",
        "sameOutcomeProbability_comm",
        "sameOutcomeProbability_equal_setting",
        "cos_half_settingZero_sub_settingOne",
        "cos_half_settingZero_sub_settingTwo",
        "cos_half_settingOne_sub_settingTwo",
        "sameOutcomeProbability_settingZero_settingOne",
        "sameOutcomeProbability_settingZero_settingTwo",
        "sameOutcomeProbability_settingOne_settingTwo",
        "threeSetting_sameOutcomeProbability_of_ne",
        "threeSetting_sameOutcomeProbability_self",
    ),
    "Deutsch/Bell/Moments.lean": (
        "disjunctionIndicator_eq",
        "complementaryDisjunctionIndicator_eq",
        "disjunction_complement_partition",
        "equation42_mean_square_zero",
        "equation43_equal_on_positive_support",
        "equation44_alice_joint_moment",
        "boolean_disjunction_complement_partition",
        "equation45_complementary_partition",
        "equation45_expectation_partition",
        "equation46_first_equality",
        "equation46_first_inequality",
        "equation46_expanded_mean",
        "equation46_second_inequality",
        "equation46_triple_mean_nonnegative",
        "equation46_third_inequality",
        "equation46_chain",
        "equation46_impossible_bound",
        "equation46_contradiction",
    ),
    "Deutsch/Bell/Contradiction.lean": (
        "reproducesThreeSettingQuantumAgreements_quarters",
        "reproducesThreeSettingQuantumAgreements_equal_setting",
        "epr_three_settings_refute_local_assignments",
        "no_local_assignments_reproduce_epr_three_settings",
        "epr_three_settings_refute_normalized_local_model",
        "no_normalized_local_model_reproduces_epr_three_settings",
    ),
    "Deutsch/Bell/AngleMoments.lean": (
        "angleEquation42_mean_square_zero",
        "angleEquation43_equal_on_positive_support",
        "angleEquation44_alice_joint_moment",
        "restrictRealAngleMomentsToThreeSettings",
    ),
}

REQUIRED_BELL_AUDIT_TARGETS = tuple(
    "Deutsch.Bell." + name
    for path, declarations in REQUIRED_BELL_PUBLIC_DECLARATIONS.items()
    for name in declarations
)

FORBIDDEN = {
    "proof hole `sorry`": re.compile(r"\bsorry\b"),
    "proof hole `admit`": re.compile(r"\badmit\b"),
    "concealing tactic `by_contra!`": re.compile(r"\bby_contra!"),
    "unsafe declaration": re.compile(r"(?m)^\s*(?:private\s+)?unsafe\b"),
    "opaque declaration": re.compile(r"(?m)^\s*(?:private\s+)?opaque\b"),
    "project axiom declaration": re.compile(r"(?m)^\s*(?:private\s+)?axiom\b"),
}

EDITORIAL_HISTORY_PATTERNS = {
    "editorial token `printed`": re.compile(r"\bprinted\b", re.IGNORECASE),
    "editorial token `corrected`": re.compile(r"\bcorrected\b", re.IGNORECASE),
    "editorial token `errata`": re.compile(r"\berrata\b", re.IGNORECASE),
    "editorial name `SourceCorrection`": re.compile(
        r"\bsource(?:[ _-]?correction)\b", re.IGNORECASE
    ),
    "editorial source-error language": re.compile(
        r"\bsource(?:[- ](?:defect|discrepancy|error|mistake))\b",
        re.IGNORECASE,
    ),
    "editorial sign-correction language": re.compile(
        r"\b(?:rotation[- ]?)?sign correction\b", re.IGNORECASE
    ),
    "editorial bookkeeping-error language": re.compile(
        r"\bbookkeeping (?:error|mistake|slip)\b", re.IGNORECASE
    ),
    "editorial misprint/typo language": re.compile(
        r"\b(?:misprint|typo(?:graphical)?(?: error)?)\b", re.IGNORECASE
    ),
}

SUPERSEDED_DECLARATION_NAMES = (
    "rotationX_heisenberg_y_pi_div_two_ne_printed",
    "rotationX_heisenberg_z_pi_div_two_ne_printed",
    "equation28_printed_equal_angle_counterexample",
    "equation41_printed_equal_angle_counterexample",
    "equation29_q1_y_pi_div_two",
    "equation29_q1_y_pi_div_two_ne_printed",
    "equation31_q1_y_pi_div_two_ne_printed",
    "equation32_q2_y_pi_div_two_ne_printed",
    "equation34_q5_y_pi_div_two_ne_printed",
    "equation37_q5_z_pi_div_four_ne_printed",
    "equation35CorrectedEffect",
    "equation35_corrected_effect_op",
    "equation35PrintedMinusSineAtPiOverTwo",
    "equation35_printed_minus_sine_at_pi_div_two_op",
    "equation35_printed_minus_sine_probability_zero_at_pi_div_two",
    "corrected_epr_three_settings_refute_local_assignments",
    "no_local_assignments_reproduce_corrected_epr_three_settings",
    "corrected_epr_three_settings_refute_normalized_local_model",
    "no_normalized_local_model_reproduces_corrected_epr_three_settings",
)

NEUTRAL_RENAME_TARGETS = {
    "Deutsch/Teleportation/Statistics.lean": (
        "equation35Effect",
        "equation35_effect_op",
    ),
    "Deutsch/Bell/Contradiction.lean": (
        "epr_three_settings_refute_local_assignments",
        "no_local_assignments_reproduce_epr_three_settings",
        "epr_three_settings_refute_normalized_local_model",
        "no_normalized_local_model_reproduces_epr_three_settings",
    ),
}


def fail(message: str) -> None:
    print(f"Lean integrity audit FAILED: {message}", file=sys.stderr)
    raise SystemExit(1)


def lean_code_only(source: str) -> str:
    """Blank Lean comments and strings while preserving newlines and token spacing."""
    result = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                result[index] = result[index + 1] = " "
                block_depth += 1
                index += 2
                continue
            if pair == "-/":
                result[index] = result[index + 1] = " "
                block_depth -= 1
                index += 2
                continue
            if char != "\n":
                result[index] = " "
            index += 1
            continue
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
            else:
                result[index] = " "
            index += 1
            continue
        if in_string:
            if char != "\n":
                result[index] = " "
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            result[index] = result[index + 1] = " "
            block_depth = 1
            index += 2
            continue
        if pair == "--":
            result[index] = result[index + 1] = " "
            in_line_comment = True
            index += 2
            continue
        if char == '"':
            result[index] = " "
            in_string = True
        index += 1
    if block_depth or in_string:
        fail("unterminated block comment or string while scanning Lean sources")
    return "".join(result)


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def declared_names(path: Path) -> set[str]:
    """Return declaration names from Lean code, excluding comments and strings."""
    code = lean_code_only(path.read_text(encoding="utf-8"))
    return set(
        re.findall(
            r"(?m)^\s*(?:abbrev|def|structure|theorem)\s+"
            r"([A-Za-z_][A-Za-z0-9_'.]*)\b",
            code,
        )
    )


def imported_modules(path: Path) -> tuple[str, ...]:
    """Return modules from immediate source-level `import` commands in file order."""
    code = lean_code_only(path.read_text(encoding="utf-8"))
    import_groups = re.findall(
        r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.' \t]*)\s*$",
        code,
    )
    return tuple(
        module
        for group in import_groups
        for module in group.split()
    )


def axiom_audit_targets(path: Path) -> list[str]:
    """Read exact `#print axioms` targets, ignoring commented-out commands."""
    code = lean_code_only(path.read_text(encoding="utf-8"))
    return re.findall(
        r"(?m)^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
        code,
    )


def check_targets(path: Path) -> tuple[str, ...]:
    """Read exact `#check` targets, ignoring commented-out commands."""
    code = lean_code_only(path.read_text(encoding="utf-8"))
    return tuple(
        re.findall(
            r"(?m)^\s*#check\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
            code,
        )
    )


def bare_paper_equation_declarations(path: Path) -> list[str]:
    """Return only bare two-digit `equationNN` declarations, excluding suffixed helpers."""
    code = lean_code_only(path.read_text(encoding="utf-8"))
    return re.findall(
        r"(?m)^\s*(?:abbrev|def|structure|theorem)\s+"
        r"(equation[0-9]{2})(?=\s|\{|\(|:)",
        code,
    )


def main() -> None:
    missing = [path for path in REQUIRED_FILES if not (ROOT / path).is_file()]
    if missing:
        fail(f"missing required files: {', '.join(missing)}")
    superseded_module = ROOT / "Deutsch/Bell/SourceCorrection.lean"
    if superseded_module.exists():
        fail("superseded production module remains: Deutsch/Bell/SourceCorrection.lean")

    for relative_path, expected_imports in REQUIRED_PRODUCTION_IMPORT_CLOSURE.items():
        observed_imports = imported_modules(ROOT / relative_path)
        if observed_imports != expected_imports:
            fail(
                f"{relative_path} immediate imports differ from the production closure: "
                f"expected {expected_imports!r}, found {observed_imports!r}"
            )

    test_root_imports = imported_modules(ROOT / "DeutschTests.lean")
    if test_root_imports != REQUIRED_TEST_ROOT_IMPORTS:
        fail(
            "DeutschTests.lean immediate imports differ from the focused-test closure: "
            f"expected {REQUIRED_TEST_ROOT_IMPORTS!r}, found {test_root_imports!r}"
        )
    separate_root_prefixes = {
        "DeutschErrata.lean": "DeutschErrata.",
        "DeutschErrataTests.lean": "DeutschErrataTests.",
    }
    for relative_path, expected_prefix in separate_root_prefixes.items():
        observed_imports = imported_modules(ROOT / relative_path)
        if not observed_imports or any(
            not module.startswith(expected_prefix) for module in observed_imports
        ):
            fail(
                f"{relative_path} is not a separate {expected_prefix[:-1]} root: "
                f"found {observed_imports!r}"
            )

    paper_equation_locations: dict[str, list[str]] = {}
    for path in sorted((ROOT / "Deutsch/Paper").glob("*.lean")):
        relative_path = str(path.relative_to(ROOT))
        for name in bare_paper_equation_declarations(path):
            paper_equation_locations.setdefault(name, []).append(relative_path)
    missing_paper_equations = [
        name for name in REQUIRED_PAPER_EQUATIONS
        if name not in paper_equation_locations
    ]
    duplicate_paper_equations = {
        name: locations
        for name, locations in paper_equation_locations.items()
        if len(locations) != 1
    }
    unexpected_paper_equations = sorted(
        set(paper_equation_locations) - set(REQUIRED_PAPER_EQUATIONS)
    )
    if missing_paper_equations or duplicate_paper_equations or unexpected_paper_equations:
        details: list[str] = []
        if missing_paper_equations:
            details.append("missing " + ", ".join(missing_paper_equations))
        if duplicate_paper_equations:
            details.append(
                "duplicates "
                + ", ".join(
                    f"{name} in {locations!r}"
                    for name, locations in sorted(duplicate_paper_equations.items())
                )
            )
        if unexpected_paper_equations:
            details.append("unexpected " + ", ".join(unexpected_paper_equations))
        fail(
            "bare Deutsch.Paper equation registry is not exactly E01--E46: "
            + "; ".join(details)
        )

    paper_check_targets = check_targets(ROOT / "DeutschTests/Paper.lean")
    if paper_check_targets != REQUIRED_PAPER_CHECK_TARGETS:
        fail(
            "DeutschTests/Paper.lean #check registry differs from exact E01--E46: "
            f"expected {REQUIRED_PAPER_CHECK_TARGETS!r}, "
            f"found {paper_check_targets!r}"
        )
    paper_oracles = declared_names(ROOT / "DeutschTests/Paper.lean")
    required_paper_oracles = set(REQUIRED_PAPER_ORACLES)
    if paper_oracles != required_paper_oracles:
        missing_oracles = sorted(required_paper_oracles - paper_oracles)
        unexpected_oracles = sorted(paper_oracles - required_paper_oracles)
        details = []
        if missing_oracles:
            details.append("missing " + ", ".join(missing_oracles))
        if unexpected_oracles:
            details.append("unexpected " + ", ".join(unexpected_oracles))
        fail(
            "paper no-cheating wrappers differ from the required set: "
            + "; ".join(details)
        )

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        fail(f"lean-toolchain is {toolchain!r}, expected {EXPECTED_TOOLCHAIN!r}")

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    if f'rev = "{EXPECTED_MATHLIB_TAG}"' not in lakefile:
        fail(f"lakefile.toml does not pin mathlib {EXPECTED_MATHLIB_TAG}")
    default_targets_match = re.search(
        r'(?m)^defaultTargets = \[([^]]*)\]$', lakefile
    )
    if default_targets_match is None:
        fail("lakefile.toml has no literal defaultTargets list")
    observed_default_targets = tuple(
        re.findall(r'"([^"]+)"', default_targets_match.group(1))
    )
    if observed_default_targets != EXPECTED_DEFAULT_TARGETS:
        fail(
            "lakefile.toml default targets differ from the four-library cutover: "
            f"expected {EXPECTED_DEFAULT_TARGETS!r}, "
            f"found {observed_default_targets!r}"
        )
    observed_lake_libraries = tuple(
        re.findall(
            r'(?m)^\[\[lean_lib\]\]\s*\nname = "([^"]+)"$',
            lakefile,
        )
    )
    if observed_lake_libraries != EXPECTED_LAKE_LIBRARIES:
        fail(
            "lakefile.toml Lean libraries differ from the four separate roots: "
            f"expected {EXPECTED_LAKE_LIBRARIES!r}, "
            f"found {observed_lake_libraries!r}"
        )

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next((package for package in manifest["packages"] if package["name"] == "mathlib"), None)
    if mathlib is None:
        fail("lake-manifest.json has no mathlib package")
    if mathlib.get("inputRev") != EXPECTED_MATHLIB_TAG:
        fail(f"manifest mathlib inputRev is {mathlib.get('inputRev')!r}")
    if mathlib.get("rev") != EXPECTED_MATHLIB_COMMIT:
        fail(f"manifest mathlib commit is {mathlib.get('rev')!r}")

    lean_files = sorted(
        path
        for path in ROOT.rglob("*.lean")
        if not any(part in {".git", ".lake"} for part in path.relative_to(ROOT).parts)
    )
    violations: list[str] = []
    for path in lean_files:
        code = lean_code_only(path.read_text(encoding="utf-8"))
        for label, pattern in FORBIDDEN.items():
            for match in pattern.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                violations.append(f"{path.relative_to(ROOT)}:{line}: {label}")
    if violations:
        fail("forbidden Lean constructs:\n  " + "\n  ".join(violations))

    main_production_files = [
        ROOT / "Deutsch.lean",
        *sorted((ROOT / "Deutsch").rglob("*.lean")),
    ]
    main_test_files = [
        ROOT / "DeutschTests.lean",
        *sorted((ROOT / "DeutschTests").rglob("*.lean")),
    ]
    errata_production_files = [
        ROOT / "DeutschErrata.lean",
        *sorted((ROOT / "DeutschErrata").rglob("*.lean")),
    ]
    errata_test_files = [
        ROOT / "DeutschErrataTests.lean",
        *sorted((ROOT / "DeutschErrataTests").rglob("*.lean")),
    ]
    public_files = main_production_files + errata_production_files
    tactic_imports = [
        str(path.relative_to(ROOT))
        for path in public_files
        if re.search(
            r"(?m)^\s*import\s+Mathlib\.Tactic\s*$",
            lean_code_only(path.read_text(encoding="utf-8")),
        )
    ]
    if tactic_imports:
        fail(f"public modules import Mathlib.Tactic: {', '.join(tactic_imports)}")

    production_test_imports = [
        f"{path.relative_to(ROOT)}:{module}"
        for path in public_files
        for module in imported_modules(path)
        if module in {"DeutschTests", "DeutschErrataTests"}
        or module.startswith(("DeutschTests.", "DeutschErrataTests."))
    ]
    if production_test_imports:
        fail(
            "production modules import verification modules: "
            + ", ".join(production_test_imports)
        )
    main_errata_imports = [
        f"{path.relative_to(ROOT)}:{module}"
        for path in main_production_files + main_test_files
        for module in imported_modules(path)
        if module in {"DeutschErrata", "DeutschErrataTests"}
        or module.startswith(("DeutschErrata.", "DeutschErrataTests."))
    ]
    if main_errata_imports:
        fail(
            "Deutsch or DeutschTests imports the Errata layer: "
            + ", ".join(main_errata_imports)
        )
    errata_main_test_imports = [
        f"{path.relative_to(ROOT)}:{module}"
        for path in errata_test_files
        for module in imported_modules(path)
        if module == "DeutschTests" or module.startswith("DeutschTests.")
    ]
    if errata_main_test_imports:
        fail(
            "DeutschErrataTests imports the main test library: "
            + ", ".join(errata_main_test_imports)
        )

    historical_violations: list[str] = []
    for path in main_production_files + main_test_files:
        source = path.read_text(encoding="utf-8")
        for label, pattern in EDITORIAL_HISTORY_PATTERNS.items():
            for match in pattern.finditer(source):
                line = source.count("\n", 0, match.start()) + 1
                historical_violations.append(
                    f"{path.relative_to(ROOT)}:{line}: {label}"
                )
    if historical_violations:
        fail(
            "editorial-history language remains in Deutsch/DeutschTests:\n  "
            + "\n  ".join(historical_violations)
        )

    superseded_declarations = [
        f"{path.relative_to(ROOT)}:{name}"
        for path in lean_files
        for name in sorted(
            declared_names(path).intersection(SUPERSEDED_DECLARATION_NAMES)
        )
    ]
    if superseded_declarations:
        fail(
            "superseded declarations or compatibility aliases remain: "
            + ", ".join(superseded_declarations)
        )

    absent_neutral_renames = [
        f"{relative_path}:{name}"
        for relative_path, required_names in NEUTRAL_RENAME_TARGETS.items()
        for name in required_names
        if name not in declared_names(ROOT / relative_path)
    ]
    if absent_neutral_renames:
        fail(
            "missing neutral cutover declarations: "
            + ", ".join(absent_neutral_renames)
        )

    foundation_oracles = set().union(
        *(declared_names(ROOT / path) for path in (
            "DeutschTests/Foundations/Concrete.lean",
            "DeutschTests/Foundations/Abstract.lean",
            "DeutschTests/Foundations/MatrixSemantics.lean",
        ))
    )
    absent_foundation_oracles = [
        name for name in REQUIRED_FOUNDATION_ORACLES if name not in foundation_oracles
    ]
    if absent_foundation_oracles:
        fail(f"missing foundation convention/API oracles: {', '.join(absent_foundation_oracles)}")

    register_oracles = declared_names(ROOT / "DeutschTests/Register.lean")
    absent_register_oracles = [
        name for name in REQUIRED_REGISTER_ORACLES if name not in register_oracles
    ]
    if absent_register_oracles:
        fail(f"missing register verification oracles: {', '.join(absent_register_oracles)}")

    locality_oracles = declared_names(ROOT / "DeutschTests/Locality.lean")
    absent_locality_oracles = [
        name for name in REQUIRED_LOCALITY_ORACLES if name not in locality_oracles
    ]
    if absent_locality_oracles:
        fail(f"missing locality verification oracles: {', '.join(absent_locality_oracles)}")

    descriptor_oracles = declared_names(ROOT / "DeutschTests/Descriptor.lean")
    absent_descriptor_oracles = [
        name for name in REQUIRED_DESCRIPTOR_ORACLES if name not in descriptor_oracles
    ]
    if absent_descriptor_oracles:
        fail(f"missing descriptor verification oracles: {', '.join(absent_descriptor_oracles)}")

    gate_oracles = declared_names(ROOT / "DeutschTests/Gates.lean")
    absent_gate_oracles = [name for name in REQUIRED_GATE_ORACLES if name not in gate_oracles]
    if absent_gate_oracles:
        fail(f"missing gate verification oracles: {', '.join(absent_gate_oracles)}")

    information_oracles = declared_names(ROOT / "DeutschTests/Information.lean")
    absent_information_oracles = [
        name for name in REQUIRED_INFORMATION_ORACLES if name not in information_oracles
    ]
    if absent_information_oracles:
        fail(f"missing information verification oracles: {', '.join(absent_information_oracles)}")

    epr_oracles = declared_names(ROOT / "DeutschTests/EPR.lean")
    absent_epr_oracles = [name for name in REQUIRED_EPR_ORACLES if name not in epr_oracles]
    if absent_epr_oracles:
        fail(f"missing EPR verification oracles: {', '.join(absent_epr_oracles)}")

    teleportation_oracles = declared_names(ROOT / "DeutschTests/Teleportation.lean")
    absent_teleportation_oracles = [
        name for name in REQUIRED_TELEPORTATION_ORACLES
        if name not in teleportation_oracles
    ]
    if absent_teleportation_oracles:
        fail(
            "missing teleportation verification oracles: "
            + ", ".join(absent_teleportation_oracles)
        )

    decoherence_oracles = declared_names(ROOT / "DeutschTests/Decoherence.lean")
    absent_decoherence_oracles = [
        name for name in REQUIRED_DECOHERENCE_ORACLES
        if name not in decoherence_oracles
    ]
    if absent_decoherence_oracles:
        fail(
            "missing decoherence verification oracles: "
            + ", ".join(absent_decoherence_oracles)
        )

    bell_oracles = declared_names(ROOT / "DeutschTests/Bell.lean")
    absent_bell_oracles = [
        name for name in REQUIRED_BELL_ORACLES
        if name not in bell_oracles
    ]
    if absent_bell_oracles:
        fail(
            "missing Bell verification oracles: "
            + ", ".join(absent_bell_oracles)
        )

    example_declarations = declared_names(ROOT / "DeutschTests/Examples.lean")
    required_example_declarations = set(REQUIRED_EXAMPLE_DECLARATIONS)
    if example_declarations != required_example_declarations:
        missing_examples = sorted(required_example_declarations - example_declarations)
        unexpected_examples = sorted(example_declarations - required_example_declarations)
        details: list[str] = []
        if missing_examples:
            details.append("missing " + ", ".join(missing_examples))
        if unexpected_examples:
            details.append("unexpected " + ", ".join(unexpected_examples))
        fail(
            "Stage 12 example declarations differ from the required set: "
            + "; ".join(details)
        )

    absent_public_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_REGISTER_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_public_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_public_declarations:
        fail("missing Stage 3 public declarations: " + ", ".join(absent_public_declarations))

    absent_locality_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_LOCALITY_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_locality_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_locality_declarations:
        fail("missing Stage 4 public declarations: " + ", ".join(absent_locality_declarations))

    absent_descriptor_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_DESCRIPTOR_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_descriptor_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_descriptor_declarations:
        fail("missing Stage 5 public declarations: " + ", ".join(absent_descriptor_declarations))

    absent_gate_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_GATE_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_gate_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_gate_declarations:
        fail("missing Stage 6 public declarations: " + ", ".join(absent_gate_declarations))

    absent_information_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_INFORMATION_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_information_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_information_declarations:
        fail(
            "missing Stage 7 public declarations: "
            + ", ".join(absent_information_declarations)
        )

    absent_epr_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_EPR_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_epr_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_epr_declarations:
        fail("missing Stage 8 public declarations: " + ", ".join(absent_epr_declarations))

    absent_teleportation_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_TELEPORTATION_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_teleportation_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_teleportation_declarations:
        fail(
            "missing Stage 9 public declarations: "
            + ", ".join(absent_teleportation_declarations)
        )

    absent_decoherence_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_DECOHERENCE_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_decoherence_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_decoherence_declarations:
        fail(
            "missing Stage 10 public declarations: "
            + ", ".join(absent_decoherence_declarations)
        )

    absent_bell_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_BELL_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_bell_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_bell_declarations:
        fail(
            "missing Stage 11 public declarations: "
            + ", ".join(absent_bell_declarations)
        )

    absent_paper_declarations: list[str] = []
    for relative_path, required_names in REQUIRED_PAPER_PUBLIC_DECLARATIONS.items():
        present = declared_names(ROOT / relative_path)
        absent_paper_declarations.extend(
            f"{relative_path}:{name}" for name in required_names if name not in present
        )
    if absent_paper_declarations:
        fail(
            "missing exact paper-equation declarations: "
            + ", ".join(absent_paper_declarations)
        )

    audit_targets = axiom_audit_targets(ROOT / "DeutschTests/Audit.lean")
    audit_commands = len(audit_targets)
    if audit_commands < 10:
        fail("DeutschTests/Audit.lean has fewer than ten representative axiom checks")
    duplicate_audit_targets = sorted(
        target for target in set(audit_targets) if audit_targets.count(target) > 1
    )
    if duplicate_audit_targets:
        fail(f"duplicate axiom-audit targets: {', '.join(duplicate_audit_targets)}")
    absent_audit_targets = [
        target for target in REQUIRED_REGISTER_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_audit_targets:
        fail(f"missing Stage 3 axiom-audit targets: {', '.join(absent_audit_targets)}")

    absent_locality_audit_targets = [
        target for target in REQUIRED_LOCALITY_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_locality_audit_targets:
        fail(f"missing Stage 4 axiom-audit targets: {', '.join(absent_locality_audit_targets)}")

    absent_descriptor_audit_targets = [
        target for target in REQUIRED_DESCRIPTOR_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_descriptor_audit_targets:
        fail(f"missing Stage 5 axiom-audit targets: {', '.join(absent_descriptor_audit_targets)}")

    absent_gate_audit_targets = [
        target for target in REQUIRED_GATE_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_gate_audit_targets:
        fail(f"missing Stage 6 axiom-audit targets: {', '.join(absent_gate_audit_targets)}")

    absent_information_audit_targets = [
        target for target in REQUIRED_INFORMATION_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_information_audit_targets:
        fail(
            "missing Stage 7 axiom-audit targets: "
            + ", ".join(absent_information_audit_targets)
        )

    absent_epr_audit_targets = [
        target for target in REQUIRED_EPR_AUDIT_TARGETS if target not in audit_targets
    ]
    if absent_epr_audit_targets:
        fail(
            "missing Stage 8 axiom-audit targets: "
            + ", ".join(absent_epr_audit_targets)
        )
    observed_epr_audit_targets = tuple(
        target for target in audit_targets if target.startswith("Deutsch.EPR.")
    )
    if observed_epr_audit_targets != REQUIRED_EPR_AUDIT_TARGETS:
        fail(
            "Stage 8 axiom-audit targets differ from source-mapped declarations: "
            f"expected {REQUIRED_EPR_AUDIT_TARGETS!r}, "
            f"found {observed_epr_audit_targets!r}"
        )

    absent_teleportation_audit_targets = [
        target for target in REQUIRED_TELEPORTATION_AUDIT_TARGETS
        if target not in audit_targets
    ]
    if absent_teleportation_audit_targets:
        fail(
            "missing Stage 9 axiom-audit targets: "
            + ", ".join(absent_teleportation_audit_targets)
        )
    observed_teleportation_audit_targets = tuple(
        target for target in audit_targets
        if target.startswith("Deutsch.Teleportation.")
    )
    if observed_teleportation_audit_targets != REQUIRED_TELEPORTATION_AUDIT_TARGETS:
        fail(
            "Stage 9 axiom-audit targets differ from source-mapped declarations: "
            f"expected {REQUIRED_TELEPORTATION_AUDIT_TARGETS!r}, "
            f"found {observed_teleportation_audit_targets!r}"
        )

    absent_decoherence_audit_targets = [
        target for target in REQUIRED_DECOHERENCE_AUDIT_TARGETS
        if target not in audit_targets
    ]
    if absent_decoherence_audit_targets:
        fail(
            "missing Stage 10 axiom-audit targets: "
            + ", ".join(absent_decoherence_audit_targets)
        )
    observed_decoherence_audit_targets = tuple(
        target for target in audit_targets
        if target.startswith("Deutsch.Decoherence.")
    )
    expected_decoherence_namespace_targets = tuple(
        target for target in REQUIRED_DECOHERENCE_AUDIT_TARGETS
        if target.startswith("Deutsch.Decoherence.")
    )
    if observed_decoherence_audit_targets != expected_decoherence_namespace_targets:
        fail(
            "Stage 10 decoherence-namespace axiom targets differ from required declarations: "
            f"expected {expected_decoherence_namespace_targets!r}, "
            f"found {observed_decoherence_audit_targets!r}"
        )

    absent_bell_audit_targets = [
        target for target in REQUIRED_BELL_AUDIT_TARGETS
        if target not in audit_targets
    ]
    if absent_bell_audit_targets:
        fail(
            "missing Stage 11 axiom-audit targets: "
            + ", ".join(absent_bell_audit_targets)
        )
    observed_bell_audit_targets = tuple(
        target for target in audit_targets
        if target.startswith("Deutsch.Bell.")
    )
    if observed_bell_audit_targets != REQUIRED_BELL_AUDIT_TARGETS:
        fail(
            "Stage 11 Bell axiom targets differ from required declarations: "
            f"expected {REQUIRED_BELL_AUDIT_TARGETS!r}, "
            f"found {observed_bell_audit_targets!r}"
        )

    absent_paper_audit_targets = [
        target for target in REQUIRED_PAPER_AUDIT_TARGETS
        if target not in audit_targets
    ]
    if absent_paper_audit_targets:
        fail(
            "missing exact paper-equation axiom targets: "
            + ", ".join(absent_paper_audit_targets)
        )
    observed_paper_audit_targets = tuple(
        target for target in audit_targets
        if target.startswith("Deutsch.Paper.equation")
        and re.fullmatch(r"Deutsch\.Paper\.equation[0-9]{2}", target)
    )
    if observed_paper_audit_targets != REQUIRED_PAPER_AUDIT_TARGETS:
        fail(
            "paper-equation axiom targets differ from exact E01--E46: "
            f"expected {REQUIRED_PAPER_AUDIT_TARGETS!r}, "
            f"found {observed_paper_audit_targets!r}"
        )

    build = run([
        "lake", "build",
        "DeutschTests.Audit",
        "DeutschTests.Register",
        "DeutschTests.Locality",
        "DeutschTests.Descriptor",
        "DeutschTests.Gates",
        "DeutschTests.Information",
        "DeutschTests.EPR",
        "DeutschTests.Teleportation",
        "DeutschTests.Decoherence",
        "DeutschTests.Bell",
        "DeutschTests.Paper",
        "DeutschTests.Examples",
        "DeutschErrata",
        "DeutschErrataTests",
    ])
    if build.returncode:
        fail(f"axiom-audit and focused verification targets did not build:\n{build.stdout}")
    audit = run(["lake", "env", "lean", "DeutschTests/Audit.lean"])
    if audit.returncode:
        fail(f"axiom-audit source did not compile:\n{audit.stdout}")
    if "sorryAx" in audit.stdout:
        fail(f"axiom report contains sorryAx:\n{audit.stdout}")
    reports = re.findall(
        r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|"
        r"(does not depend on any axioms))",
        audit.stdout,
        re.DOTALL,
    )
    report_names = [name for name, _, _ in reports]
    if report_names != audit_targets:
        fail(
            "axiom report targets differ from audit commands: "
            f"expected {audit_targets!r}, found {report_names!r}"
        )
    observed_axioms = {
        name.strip()
        for _, report, _ in reports
        for name in report.replace("\n", " ").split(",")
        if name.strip()
    }
    unexpected = observed_axioms - ALLOWED_AXIOMS
    if unexpected:
        fail(f"unexpected axioms in representative declarations: {sorted(unexpected)}")

    print("Lean integrity audit passed")
    print(f"  Lean sources scanned: {len(lean_files)}")
    print("  Forbidden proof holes/declarations: none")
    print("  Production imports of verification modules: none")
    print("  Deutsch/DeutschTests imports of DeutschErrata: none")
    print("  Editorial-history language in Deutsch/DeutschTests: none")
    print("  Superseded declarations/compatibility aliases: none")
    print(
        "  Lake libraries/default targets: "
        f"{len(observed_lake_libraries)}/{len(observed_default_targets)}"
    )
    print(
        "  Neutral production rename targets: "
        f"{sum(len(names) for names in NEUTRAL_RENAME_TARGETS.values())}"
    )
    print(f"  Toolchain: {EXPECTED_TOOLCHAIN}")
    print(f"  mathlib: {EXPECTED_MATHLIB_TAG} @ {EXPECTED_MATHLIB_COMMIT}")
    print(
        "  Required public-root umbrella imports: "
        f"{len(REQUIRED_PUBLIC_ROOT_IMPORTS)}"
    )
    print(
        "  Required production import-closure files/edges: "
        f"{len(REQUIRED_PRODUCTION_IMPORT_CLOSURE)}/"
        f"{sum(len(imports) for imports in REQUIRED_PRODUCTION_IMPORT_CLOSURE.values())}"
    )
    print(
        "  Required test-root immediate imports: "
        f"{len(REQUIRED_TEST_ROOT_IMPORTS)}"
    )
    print(f"  Required foundation convention/API oracles: {len(REQUIRED_FOUNDATION_ORACLES)}")
    print(f"  Required register verification oracles: {len(REQUIRED_REGISTER_ORACLES)}")
    print(f"  Required Stage 3 public declarations: {len(REQUIRED_REGISTER_AUDIT_TARGETS)}")
    print(f"  Required locality verification oracles: {len(REQUIRED_LOCALITY_ORACLES)}")
    print(f"  Required Stage 4 public declarations: {len(REQUIRED_LOCALITY_AUDIT_TARGETS)}")
    print(f"  Required descriptor verification oracles: {len(REQUIRED_DESCRIPTOR_ORACLES)}")
    print(f"  Required Stage 5 public declarations: {len(REQUIRED_DESCRIPTOR_AUDIT_TARGETS)}")
    print(f"  Required gate verification oracles: {len(REQUIRED_GATE_ORACLES)}")
    print(f"  Required Stage 6 public declarations: {len(REQUIRED_GATE_AUDIT_TARGETS)}")
    print(f"  Required information verification oracles: {len(REQUIRED_INFORMATION_ORACLES)}")
    print(f"  Required Stage 7 public declarations: {len(REQUIRED_INFORMATION_AUDIT_TARGETS)}")
    print(f"  Required EPR verification oracles: {len(REQUIRED_EPR_ORACLES)}")
    print(f"  Required Stage 8 public declarations: {len(REQUIRED_EPR_AUDIT_TARGETS)}")
    print(
        "  Required teleportation verification oracles: "
        f"{len(REQUIRED_TELEPORTATION_ORACLES)}"
    )
    print(
        "  Required Stage 9 public declarations: "
        f"{len(REQUIRED_TELEPORTATION_AUDIT_TARGETS)}"
    )
    print(
        "  Required decoherence verification oracles: "
        f"{len(REQUIRED_DECOHERENCE_ORACLES)}"
    )
    print(
        "  Required Stage 10 public declarations: "
        f"{len(REQUIRED_DECOHERENCE_AUDIT_TARGETS)}"
    )
    print(
        "  Required Bell verification oracles: "
        f"{len(REQUIRED_BELL_ORACLES)}"
    )
    print(
        "  Required Stage 11 public declarations: "
        f"{len(REQUIRED_BELL_AUDIT_TARGETS)}"
    )
    print(
        "  Exact paper-equation declarations/checks/axiom targets: "
        f"{len(REQUIRED_PAPER_EQUATIONS)}/"
        f"{len(REQUIRED_PAPER_CHECK_TARGETS)}/"
        f"{len(REQUIRED_PAPER_AUDIT_TARGETS)}"
    )
    print(
        "  Required paper no-cheating wrappers: "
        f"{len(REQUIRED_PAPER_ORACLES)}"
    )
    print(
        "  Required Stage 12 compiled reuse examples: "
        f"{len(REQUIRED_EXAMPLE_DECLARATIONS)}"
    )
    print(f"  Representative axiom reports: {len(reports)}")
    print(f"  Observed foundational axioms: {', '.join(sorted(observed_axioms))}")


if __name__ == "__main__":
    main()
