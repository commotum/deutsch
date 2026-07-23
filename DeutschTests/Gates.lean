import Deutsch.Gates
import Deutsch.Locality.Heisenberg
import Mathlib.Tactic

/-!
# Gate verification

Focused Stage 6 regressions for exact one-qubit phases and rotation signs, named-register CNOT
basis action and target/control order, Bell chronology and amplitudes, and remote-coordinate
invariance.
-/

namespace DeutschTests
namespace GatesVerification

open Deutsch Deutsch.Foundations Deutsch.Gates Deutsch.Locality Deutsch.Register
open scoped Matrix

noncomputable section

/-! ## One-qubit branches, phases, and source signs -/

theorem not_swaps_paper_one_to_zero : notGate.mulVec ketOne = ketZero :=
  not_mulVec_ketOne

theorem not_swaps_paper_zero_to_one : notGate.mulVec ketZero = ketOne :=
  not_mulVec_ketZero

theorem paper_sqrt_not_squares_exactly_to_not :
    paperSqrtNot * paperSqrtNot = notGate :=
  paperSqrtNot_square

theorem paper_sqrt_not_is_not_positive_pi_half_rotation :
    paperSqrtNot ≠ rotationX (Real.pi / 2) := by
  intro hgate
  have hy : pauliZ = -pauliZ := by
    calc
      pauliZ = Foundations.heisenberg paperSqrtNot pauliY :=
        paperSqrtNot_heisenberg_y.symm
      _ = Foundations.heisenberg (rotationX (Real.pi / 2)) pauliY := by
        rw [hgate]
      _ = -pauliZ := rotationX_heisenberg_y_pi_div_two
  have h00 := congrFun (congrFun hy (0 : QubitIndex)) (0 : QubitIndex)
  norm_num [pauliZ] at h00

theorem equation18_printed_y_sign_fails_at_pi_half :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliY ≠ pauliZ :=
  rotationX_heisenberg_y_pi_div_two_ne_printed

theorem equation18_printed_z_sign_fails_at_pi_half :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliZ ≠ -pauliY :=
  rotationX_heisenberg_z_pi_div_two_ne_printed

theorem rotation_y_at_negative_pi_half_has_correct_sign :
    Foundations.heisenberg (rotationX (-Real.pi / 2)) pauliY = pauliZ :=
  rotationX_heisenberg_y_neg_pi_div_two

theorem rotation_z_at_negative_pi_half_has_correct_sign :
    Foundations.heisenberg (rotationX (-Real.pi / 2)) pauliZ = -pauliY :=
  rotationX_heisenberg_z_neg_pi_div_two

theorem diagonal_rotation_phase_cancels_on_y :
    Foundations.heisenberg diagonalPiRotation pauliY =
      Foundations.heisenberg hadamard pauliY :=
  diagonalPiRotation_heisenberg pauliY

theorem arbitrary_valid_descriptor_not_has_paper_map
    {d : Descriptor (Fin 2)} (hd : d.Valid) :
    d.evolve (descriptorNot d) = { x := d.x, y := -d.y, z := -d.z } :=
  descriptorNot_evolve hd

/-! ## Arbitrary-axis rotations -/

/-- A unit axis with two nonzero coordinates, used to keep these tests off the coordinate axes. -/
def threeFourAxis : UnitAxis :=
  ⟨⟨(3 : ℝ) / 5, (4 : ℝ) / 5, 0⟩, by
    norm_num [Vector3.normSq, Vector3.dot]⟩

theorem non_coordinate_axis_has_rodrigues_action (theta : ℝ) (v : Vector3) :
    Foundations.heisenberg (axisRotation threeFourAxis theta) (pauliVector v) =
      pauliVector (Vector3.heisenbergRotate threeFourAxis.1 theta v) :=
  axisRotation_heisenberg threeFourAxis theta v

theorem non_coordinate_axis_uses_matrix_exponential (theta : ℝ) :
    NormedSpace.exp (axisRotationGenerator threeFourAxis theta) =
      axisRotation threeFourAxis theta :=
  exp_axisRotationGenerator threeFourAxis theta

theorem non_coordinate_axis_rotation_is_unitary (theta : ℝ) :
    axisRotation threeFourAxis theta ∈
      Matrix.unitaryGroup QubitIndex ℂ :=
  axisRotation_isUnitary threeFourAxis theta

theorem arbitrary_axis_x_specialization_is_rotationX (theta : ℝ) :
    axisRotation UnitAxis.xAxis theta = rotationX theta :=
  axisRotation_xAxis theta

theorem arbitrary_axis_x_pi_half_maps_y_to_negative_z :
    Foundations.heisenberg
        (axisRotation UnitAxis.xAxis (Real.pi / 2)) pauliY =
      -pauliZ := by
  rw [axisRotation_xAxis, rotationX_heisenberg_y_pi_div_two]

/-! ## Named-wire and current-frame arbitrary-axis rotations -/

theorem named_non_coordinate_axis_uses_global_matrix_exponential
    (q : Fin 3) (theta : ℝ) :
    NormedSpace.exp (axisRotationGeneratorAt q threeFourAxis theta) =
      axisRotationAt q threeFourAxis theta :=
  exp_axisRotationGeneratorAt q threeFourAxis theta

theorem current_non_coordinate_axis_is_transported_named_gate
    (W : Operator (Fin 3)) (q : Fin 3) (theta : ℝ)
    (hW : W ∈ Matrix.unitaryGroup (Basis (Fin 3)) ℂ) :
    currentAxisRotation W q threeFourAxis theta =
      Register.heisenberg W (axisRotationAt q threeFourAxis theta) :=
  currentAxisRotation_eq_heisenberg W q threeFourAxis theta hW

theorem transported_named_gate_has_current_exponential_action
    (W : Operator (Fin 3)) (q : Fin 3) (theta : ℝ) (a : Axis)
    (hW : W ∈ Matrix.unitaryGroup (Basis (Fin 3)) ℂ) :
    Register.heisenberg
        (Register.heisenberg W (axisRotationAt q threeFourAxis theta))
        (((Descriptor.initial q).evolve W).component a) =
      NormedSpace.exp
          ((Complex.I * (theta / 2 : ℂ)) •
            currentAxisPauli W q threeFourAxis) *
        ((Descriptor.initial q).evolve W).component a *
        NormedSpace.exp
          ((-Complex.I * (theta / 2 : ℂ)) •
            currentAxisPauli W q threeFourAxis) :=
  axisRotationAt_heisenberg_current_component_exp
    W q threeFourAxis theta a hW

theorem current_non_coordinate_axis_has_rodrigues_action
    (W : Operator (Fin 3)) (q : Fin 3) (theta : ℝ) (v : Vector3)
    (hW : W ∈ Matrix.unitaryGroup (Basis (Fin 3)) ℂ) :
    Register.heisenberg (currentAxisRotation W q threeFourAxis theta)
        (descriptorPauliVector ((Descriptor.initial q).evolve W) v) =
      descriptorPauliVector ((Descriptor.initial q).evolve W)
        (Vector3.heisenbergRotate threeFourAxis.1 theta v) :=
  currentAxisRotation_heisenberg W q threeFourAxis theta v hW

theorem current_x_axis_has_correct_y_sign
    (W : Operator (Fin 3)) (q : Fin 3) (theta : ℝ)
    (hW : W ∈ Matrix.unitaryGroup (Basis (Fin 3)) ℂ) :
    Register.heisenberg
        (currentAxisRotation W q UnitAxis.xAxis theta)
        ((Descriptor.initial q).evolve W).y =
      (Real.cos theta : ℂ) • ((Descriptor.initial q).evolve W).y -
        (Real.sin theta : ℂ) • ((Descriptor.initial q).evolve W).z := by
  simpa [sub_eq_add_neg, descriptorPauliVector,
    Vector3.heisenbergRotate, Vector3.dot, Vector3.cross,
    UnitAxis.xAxis] using
    currentAxisRotation_heisenberg W q UnitAxis.xAxis theta
      (⟨0, 1, 0⟩ : Vector3) hW

/-! ## Named-register one-qubit locality -/

theorem rotation_on_zero_fixes_remote_z (theta : Real) :
    Register.heisenberg (rotationXAt (0 : Fin 3) theta) (zAt (2 : Fin 3)) =
      zAt (2 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (rotationXAt_unitary 0 theta)
    (rotationXAt_isSupportedOn 0 theta) (zAt_isSupportedOn 2)

/-! ## CNOT basis action and target/control order -/

def rawPair (target control : QubitIndex) : Basis (Fin 2) :=
  ![target, control]

@[simp] theorem rawPair_zero (target control : QubitIndex) :
    rawPair target control 0 = target := rfl

@[simp] theorem rawPair_one (target control : QubitIndex) :
    rawPair target control 1 = control := rfl

theorem named_cnot_inactive_on_paper_zero_control :
    act (cnotAt (0 : Fin 2) 1 (by decide)) (basisKet (rawPair 0 1)) =
      basisKet (rawPair 0 1) := by
  rw [cnotAt_act_basisKet]
  congr 2
  funext q
  fin_cases q <;> simp [cnotOutput, rawPair]

theorem named_cnot_active_on_paper_one_control :
    act (cnotAt (0 : Fin 2) 1 (by decide)) (basisKet (rawPair 0 0)) =
      basisKet (rawPair 1 0) := by
  rw [cnotAt_act_basisKet]
  congr 2
  funext q
  fin_cases q <;> simp [cnotOutput, rawPair, flipRaw]

theorem named_cnot_second_inactive_case :
    act (cnotAt (0 : Fin 2) 1 (by decide)) (basisKet (rawPair 1 1)) =
      basisKet (rawPair 1 1) := by
  rw [cnotAt_act_basisKet]
  congr 2
  funext q
  fin_cases q <;> simp [cnotOutput, rawPair]

theorem named_cnot_second_active_case :
    act (cnotAt (0 : Fin 2) 1 (by decide)) (basisKet (rawPair 1 0)) =
      basisKet (rawPair 0 0) := by
  rw [cnotAt_act_basisKet]
  congr 2
  funext q
  fin_cases q <;> simp [cnotOutput, rawPair, flipRaw]

theorem reversing_cnot_target_control_changes_the_gate :
    cnotAt (0 : Fin 2) 1 (by decide) ≠ cnotAt (1 : Fin 2) 0 (by decide) := by
  intro hgate
  have hentry := congrFun (congrFun hgate (rawPair 0 0)) (rawPair 0 1)
  rw [cnotAt_apply, cnotAt_apply] at hentry
  have hleft :
      rawPair 0 0 ≠ cnotOutput (0 : Fin 2) 1 (rawPair 0 1) := by
    intro h
    have hcontrol := congrFun h 1
    norm_num [cnotOutput, rawPair] at hcontrol
  have hright :
      rawPair 0 0 = cnotOutput (1 : Fin 2) 0 (rawPair 0 1) := by
    funext q
    fin_cases q <;> simp [cnotOutput, rawPair, flipRaw]
  rw [if_neg hleft, if_pos hright] at hentry
  norm_num at hentry

theorem named_cnot_three_qubit_support :
    IsSupportedOn ({0, 2} : Finset (Fin 3))
      (cnotAt (0 : Fin 3) 2 (by decide)) :=
  cnotAt_isSupportedOn_pair 0 2 (by decide)

theorem named_cnot_on_zero_two_fixes_middle_z :
    Register.heisenberg (cnotAt (0 : Fin 3) 2 (by decide)) (zAt (1 : Fin 3)) =
      zAt (1 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (cnotAt_unitary 0 2 (by decide))
    (cnotAt_isSupportedOn_pair 0 2 (by decide)) (zAt_isSupportedOn 1)

theorem initial_descriptor_cnot_is_typed_global_formula :
    cnotFromDescriptors (DescriptorFamily.initial (Fin 3)) 0 2 =
      cnotAt (0 : Fin 3) 2 (by decide) :=
  cnotFromDescriptors_initial_eq_cnotAt 0 2 (by decide)

theorem every_valid_descriptor_cnot_is_unitary
    {D : DescriptorFamily (Fin 3)} (hD : D.Valid) :
    cnotFromDescriptors D 0 2 ∈ Matrix.unitaryGroup (Basis (Fin 3)) Complex :=
  cnotFromDescriptors_unitary hD (by decide)

theorem every_valid_descriptor_cnot_has_target_y_map
    {D : DescriptorFamily (Fin 3)} (hD : D.Valid) :
    Register.heisenberg (cnotFromDescriptors D 0 2) (D 0).y =
      -((D 0).y * (D 2).z) :=
  cnotFromDescriptors_conjugates_target_y hD (by decide)

theorem every_valid_descriptor_cnot_has_control_x_map
    {D : DescriptorFamily (Fin 3)} (hD : D.Valid) :
    Register.heisenberg (cnotFromDescriptors D 0 2) (D 2).x =
      (D 0).x * (D 2).x :=
  cnotFromDescriptors_conjugates_control_x hD (by decide)

/-! ## Bell chronology, amplitudes, and inverse -/

theorem bell_named_inverse_left :
    bellInverseAt (0 : Fin 3) 2 (by decide) *
        bellAt (0 : Fin 3) 2 (by decide) = 1 :=
  bellAt_inverse_left 0 2 (by decide)

theorem bell_named_inverse_right :
    bellAt (0 : Fin 3) 2 (by decide) *
        bellInverseAt (0 : Fin 3) 2 (by decide) = 1 :=
  bellAt_inverse_right 0 2 (by decide)

theorem bell_equation20_control_y_sign :
    Register.heisenberg (bellAt (0 : Fin 2) 1 (by decide)) (yAt 1) =
      -(xAt 0 * yAt 1) :=
  bellAt_conjugates_control_y 0 1 (by decide)

theorem bell_inverse_equation21_target_z_sign :
    Register.heisenberg (bellInverseAt (0 : Fin 2) 1 (by decide)) (zAt 0) =
      -(zAt 0 * xAt 1) :=
  bellInverseAt_conjugates_target_z 0 1 (by decide)

theorem bell_forward_has_direct_basis_amplitude :
    bellAt (0 : Fin 2) 1 (by decide) (rawPair 1 1) (rawPair 0 0) =
      invSqrtTwo := by
  rw [bellAt_apply]
  norm_num [targetControlPlacement, rawPair, flipRaw, hadamard]

theorem reversing_bell_chronology_changes_the_gate :
    bellAt (0 : Fin 2) 1 (by decide) ≠
      bellInverseAt (0 : Fin 2) 1 (by decide) := by
  intro hgate
  have hentry := congrFun (congrFun hgate (rawPair 1 1)) (rawPair 0 0)
  rw [bellAt_apply, bellInverseAt_apply] at hentry
  norm_num [targetControlPlacement, rawPair, flipRaw, hadamard, invSqrtTwo] at hentry

theorem bell_on_zero_two_fixes_middle_z :
    Register.heisenberg (bellAt (0 : Fin 3) 2 (by decide)) (zAt (1 : Fin 3)) =
      zAt (1 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (bellAt_unitary 0 2 (by decide))
    (bellAt_isSupportedOn 0 2 (by decide)) (zAt_isSupportedOn 1)

theorem bell_inverse_on_zero_two_fixes_middle_z :
    Register.heisenberg (bellInverseAt (0 : Fin 3) 2 (by decide))
        (zAt (1 : Fin 3)) = zAt (1 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (bellInverseAt_unitary 0 2 (by decide))
    (bellInverseAt_isSupportedOn 0 2 (by decide)) (zAt_isSupportedOn 1)

end
end GatesVerification
end DeutschTests
