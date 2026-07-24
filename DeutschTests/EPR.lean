import Deutsch.EPR
import Mathlib.Tactic.NormNum

/-!
# Focused EPR verification

These tests pin the phase, chronology, descriptor components, route equivalence, and literal
four-wire statistics used by the EPR development.
-/

namespace DeutschTests
namespace EPRVerification

open Deutsch Deutsch.Descriptor Deutsch.EPR Deutsch.Foundations Deutsch.Gates
  Deutsch.Information Deutsch.Register
open scoped Matrix

noncomputable section

/-! ## Pair preparation and Equation (22) -/

theorem equation22_has_explicit_global_phase :
    equation22Ket = (-Complex.I) • pairKet :=
  equation22Ket_eq_globalPhase

theorem equation22_library_ket_has_correct_relative_sign :
    pairKet = invSqrtTwo •
      (basisKet paperOneOne - basisKet paperZeroZero) :=
  pairKet_eq

theorem pair_and_time_boundaries_are_unitary (theta phi : ℝ) :
    pairCircuit theta phi ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ ∧
      timeOneUnitary ∈ Matrix.unitaryGroup (Basis EPRQubit) ℂ ∧
      timeTwoUnitary theta phi ∈ Matrix.unitaryGroup (Basis EPRQubit) ℂ ∧
      timeThreeUnitary theta phi ∈ Matrix.unitaryGroup (Basis EPRQubit) ℂ ∧
      timeFourUnitary theta phi ∈ Matrix.unitaryGroup (Basis EPRQubit) ℂ :=
  ⟨pairCircuit_unitary theta phi, timeOneUnitary_unitary,
    timeTwoUnitary_unitary theta phi, timeThreeUnitary_unitary theta phi,
    timeFourUnitary_unitary theta phi⟩

/-! ## Equations (23)--(25) -/

theorem equation23_q2_descriptor_is_exact :
    timeOneDescriptors q2 =
      { x := xAt q2
        y := -(yAt q2 * xAt q3)
        z := -(zAt q2 * xAt q3) } :=
  equation23_q2

theorem equation23_q3_descriptor_is_exact :
    timeOneDescriptors q3 =
      { x := xAt q2 * zAt q3
        y := -(xAt q2 * yAt q3)
        z := xAt q3 } :=
  equation23_q3

theorem equation24_remote_descriptors_are_untouched (theta phi : ℝ) :
    timeTwoDescriptors theta phi q1 = Descriptor.initial q1 ∧
      timeTwoDescriptors theta phi q4 = Descriptor.initial q4 :=
  ⟨equation24_q1 theta phi, equation24_q4 theta phi⟩

theorem equation25_q2_sine_components (theta phi : ℝ) :
    timeTwoDescriptors theta phi q2 =
      { x := xAt q2
        y := (theta.cos : ℂ) • (-(yAt q2 * xAt q3)) -
          (theta.sin : ℂ) • (-(zAt q2 * xAt q3))
        z := (theta.sin : ℂ) • (-(yAt q2 * xAt q3)) +
          (theta.cos : ℂ) • (-(zAt q2 * xAt q3)) } :=
  equation25_q2 theta phi

theorem equation25_q3_sine_components (theta phi : ℝ) :
    timeTwoDescriptors theta phi q3 =
      { x := xAt q2 * zAt q3
        y := (phi.cos : ℂ) • (-(xAt q2 * yAt q3)) -
          (phi.sin : ℂ) • xAt q3
        z := (phi.sin : ℂ) • (-(xAt q2 * yAt q3)) +
          (phi.cos : ℂ) • xAt q3 } :=
  equation25_q3 theta phi

/-! ## Equation (27) coherent records -/

theorem equation27_q1_record_is_factored_through_time_two (theta phi : ℝ) :
    timeThreeDescriptors theta phi q1 =
      { x := (timeTwoDescriptors theta phi q1).x
        y := -((timeTwoDescriptors theta phi q1).y *
          (timeTwoDescriptors theta phi q2).z)
        z := -((timeTwoDescriptors theta phi q1).z *
          (timeTwoDescriptors theta phi q2).z) } :=
  equation27_q1 theta phi

theorem equation27_q2_record_is_factored_through_time_two (theta phi : ℝ) :
    timeThreeDescriptors theta phi q2 =
      { x := (timeTwoDescriptors theta phi q1).x *
          (timeTwoDescriptors theta phi q2).x
        y := (timeTwoDescriptors theta phi q1).x *
          (timeTwoDescriptors theta phi q2).y
        z := (timeTwoDescriptors theta phi q2).z } :=
  equation27_q2 theta phi

theorem equation27_q3_record_is_factored_through_time_two (theta phi : ℝ) :
    timeThreeDescriptors theta phi q3 =
      { x := (timeTwoDescriptors theta phi q4).x *
          (timeTwoDescriptors theta phi q3).x
        y := (timeTwoDescriptors theta phi q4).x *
          (timeTwoDescriptors theta phi q3).y
        z := (timeTwoDescriptors theta phi q3).z } :=
  equation27_q3 theta phi

theorem equation27_q4_record_is_factored_through_time_two (theta phi : ℝ) :
    timeThreeDescriptors theta phi q4 =
      { x := (timeTwoDescriptors theta phi q4).x
        y := -((timeTwoDescriptors theta phi q4).y *
          (timeTwoDescriptors theta phi q3).z)
        z := -((timeTwoDescriptors theta phi q4).z *
          (timeTwoDescriptors theta phi q3).z) } :=
  equation27_q4 theta phi

/-! ## Equations (38)--(39) -/

theorem equation38_has_explicit_global_phase (theta : ℝ) :
    equation38Ket theta = (-Complex.I) • (pairPureState theta 0).ket :=
  equation38Ket_eq_globalPhase_pairPureState theta

theorem equation39_routes_prepare_the_same_ket (theta : ℝ) :
    act (leftRotationRoute theta) (referenceKet (Fin 2)) =
      act (rightRotationRoute theta) (referenceKet (Fin 2)) :=
  equation39_route_kets_eq theta

/-! ## Literal four-wire record statistics -/

theorem four_wire_record_effects_pin_paper_one_as_raw_zero :
    recordLeftPaperOneEffect.op = paperBitOneProjectorAt q1 ∧
      recordRightPaperOneEffect.op = paperBitOneProjectorAt q4 ∧
      recordJointPaperOneEffect =
        (basisEffect (pairBits 0 0)).embedAlong recordPlacement ∧
      finalComparisonPaperOneEffect.op = paperBitOneProjectorAt q1 := by
  constructor
  · exact zPlusEffect_op_eq_paperBitOneProjectorAt q1
  constructor
  · exact zPlusEffect_op_eq_paperBitOneProjectorAt q4
  constructor
  · rfl
  · exact zPlusEffect_op_eq_paperBitOneProjectorAt q1

theorem equation40_is_derived_on_the_four_wire_records
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
          recordLeftPaperOneEffect = 1 / 2 ∧
      bornProbability (fourWireTimeThreeDensity theta phi)
          recordRightPaperOneEffect = 1 / 2 :=
  ⟨fourWireTimeThree_leftRecord_probability theta phi,
    fourWireTimeThree_rightRecord_probability theta phi⟩

theorem equation41_is_derived_on_the_four_wire_records
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordJointPaperOneEffect =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 :=
  fourWireTimeThree_jointRecord_probability theta phi

theorem equation28_is_derived_after_the_four_wire_comparison
    (theta phi : ℝ) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect =
      Real.sin ((theta - phi) / 2) ^ 2 :=
  fourWireTimeFour_comparison_probability theta phi

theorem every_four_wire_record_outcome_matches_the_pair_density
    (theta phi : ℝ) (left right : QubitIndex) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        (recordOutcomeEffect left right) =
      bornProbability (pairDensity theta phi)
        (basisEffect (pairBits left right)) :=
  fourWireTimeThree_recordOutcome_probability_eq_pairDensity
    theta phi left right

theorem four_wire_record_and_comparison_statistics_match_the_pair_density
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
          recordLeftPaperOneEffect =
        bornProbability (pairDensity theta phi)
          (paperOneMarginalEffect 0) ∧
      bornProbability (fourWireTimeThreeDensity theta phi)
          recordRightPaperOneEffect =
        bornProbability (pairDensity theta phi)
          (paperOneMarginalEffect 1) ∧
      bornProbability (fourWireTimeThreeDensity theta phi)
          recordJointPaperOneEffect =
        bornProbability (pairDensity theta phi) jointPaperOneEffect ∧
      bornProbability (fourWireTimeFourDensity theta phi)
          finalComparisonPaperOneEffect =
        bornProbability (pairDensity theta phi) differentEffect :=
  ⟨fourWireTimeThree_leftRecord_probability_eq_pairDensity theta phi,
    fourWireTimeThree_rightRecord_probability_eq_pairDensity theta phi,
    fourWireTimeThree_jointRecord_probability_eq_pairDensity theta phi,
    fourWireTimeFour_comparison_probability_eq_pairDensity theta phi⟩

theorem equal_settings_are_a_four_wire_boundary (theta : ℝ) :
    bornProbability (fourWireTimeFourDensity theta theta)
          finalComparisonPaperOneEffect = 0 ∧
      bornProbability (fourWireTimeThreeDensity theta theta)
          recordJointPaperOneEffect = 1 / 2 := by
  constructor
  · exact fourWireTimeFour_comparison_equal_settings theta
  · rw [fourWireTimeThree_jointRecord_probability]
    norm_num

theorem relative_pi_is_a_four_wire_boundary
    (theta phi : ℝ) (hrelative : theta - phi = Real.pi) :
    bornProbability (fourWireTimeFourDensity theta phi)
          finalComparisonPaperOneEffect = 1 ∧
      bornProbability (fourWireTimeThreeDensity theta phi)
          recordJointPaperOneEffect = 0 := by
  constructor
  · exact fourWireTimeFour_comparison_relative_pi theta phi hrelative
  · rw [fourWireTimeThree_jointRecord_probability, hrelative]
    norm_num [Real.cos_pi_div_two]

/-! ## Density statistics and provenance -/

theorem both_pair_marginals_are_maximally_mixed (theta phi : ℝ) :
    (pairDensity theta phi).reduce ({0} : Finset (Fin 2)) =
        singletonMaximallyMixed 0 ∧
      (pairDensity theta phi).reduce ({1} : Finset (Fin 2)) =
        singletonMaximallyMixed 1 :=
  ⟨pairDensity_reduce_singleton theta phi 0,
    pairDensity_reduce_singleton theta phi 1⟩

theorem every_singleton_effect_is_setting_independent (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2))
      (fun settings : ℝ × ℝ ↦ pairDensity settings.1 settings.2) :=
  pairDensity_locallyStatisticsIndependent q

theorem equation28_has_sine_square_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) differentEffect =
      Real.sin ((theta - phi) / 2) ^ 2 :=
  pairDensity_different_probability theta phi

theorem equation40_marginals_are_one_half (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (paperOneMarginalEffect 0) = 1 / 2 ∧
      bornProbability (pairDensity theta phi) (paperOneMarginalEffect 1) = 1 / 2 :=
  ⟨pairDensity_left_paperOne_probability theta phi,
    pairDensity_right_paperOne_probability theta phi⟩

theorem equation41_has_cosine_square_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) jointPaperOneEffect =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 :=
  pairDensity_jointPaperOne_probability theta phi

theorem pi_separated_settings_force_different_outcomes :
    bornProbability (pairDensity Real.pi 0) differentEffect = 1 :=
  pairDensity_different_pi_zero

theorem epr_resource_zz_correlation_is_nonproduct :
    densityExpectation (pairDensity 0 0)
        (zAt (0 : Fin 2) * zAt (1 : Fin 2)) ≠
      densityExpectation (pairDensity 0 0) (zAt (0 : Fin 2)) *
        densityExpectation (pairDensity 0 0) (zAt (1 : Fin 2)) :=
  pairDensity_zero_resource_correlation

theorem finite_setting_family_is_local_but_jointly_detectable :
    LocallyStatisticsIndependent ({0} : Finset (Fin 2)) pairSettingFamily ∧
      LocallyStatisticsIndependent ({1} : Finset (Fin 2)) pairSettingFamily ∧
      StatisticallyDetectable pairSettingFamily :=
  ⟨pairSettingFamily_locallyStatisticsIndependent 0,
    pairSettingFamily_locallyStatisticsIndependent 1,
    pairSettingFamily_statisticallyDetectable⟩

theorem equation39_routes_have_equal_density_but_distinct_histories (theta : ℝ) :
    leftRouteDensity theta = rightRouteDensity theta ∧
      leftRoutePreparation.history theta ≠ rightRoutePreparation.history theta ∧
      leftRoutePreparation.realize (leftRoutePreparation.history theta) =
        rightRoutePreparation.realize (rightRoutePreparation.history theta) :=
  ⟨equation39_route_densities_eq theta,
    routePreparation_histories_distinct theta,
    routePreparations_same_final_density theta⟩

end
end EPRVerification
end DeutschTests
