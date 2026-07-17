import Deutsch.Bell

/-!
# Focused corrected Bell verification

These checks keep the Boolean pigeonhole bound, explicit two-party local assumptions, independently
derived quantum probabilities, and final contradiction as separate verification layers.
-/

namespace DeutschTests
namespace BellVerification

open Deutsch Deutsch.Bell Deutsch.Bell.SourceCorrection
open scoped BigOperators

noncomputable section

/-! ## Printed source defect -/

theorem equation45_printed_identity_is_false_at_the_recorded_counterexample :
    equation45PrintedLeft true ≠ equation45PrintedRight true false true :=
  equation45_printed_fails_at_one_zero_one

theorem equation45_corrected_partition_holds_for_every_assignment
    (assignment : Setting → Bool) :
    equation45PrintedLeft (assignment 0) =
      equation45CorrectedRight (assignment 0) (assignment 1) (assignment 2) :=
  equation45_corrected_partition_for_assignment assignment

/-! ## Finite deterministic-assignment bound -/

theorem every_three_bit_assignment_has_an_agreeing_pair
    (assignment : CommonAssignment) :
    assignment 0 = assignment 1 ∨
      assignment 1 = assignment 2 ∨
        assignment 0 = assignment 2 :=
  commonAssignment_has_agreeing_pair assignment

theorem every_common_assignment_distribution_obeys_the_bell_bound
    (weight : CommonAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    1 ≤ agreementProbability weight 0 1 +
      agreementProbability weight 1 2 +
        agreementProbability weight 0 2 :=
  three_setting_bell_inequality weight weight_nonnegative weight_normalized

theorem every_explicit_two_party_local_model_obeys_the_bell_bound
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    1 ≤ crossPartyAgreementProbability weight 0 1 +
      crossPartyAgreementProbability weight 1 2 +
        crossPartyAgreementProbability weight 0 2 :=
  local_three_setting_bell_inequality
    weight weight_nonnegative weight_normalized perfect_support

theorem probability_one_equal_settings_force_positive_support_agreement
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (equal_setting_probability_one :
      ∀ setting, crossPartyAgreementProbability weight setting setting = 1) :
    HasPerfectEqualSettingSupport weight :=
  perfectEqualSettingSupport_of_agreementProbability_one
    weight weight_nonnegative weight_normalized equal_setting_probability_one

theorem three_quarter_agreements_are_impossible_for_the_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    ¬ (crossPartyAgreementProbability weight 0 1 = (1 / 4 : ℝ) ∧
      crossPartyAgreementProbability weight 1 2 = (1 / 4 : ℝ) ∧
        crossPartyAgreementProbability weight 0 2 = (1 / 4 : ℝ)) :=
  no_local_assignment_has_three_quarter_agreements
    weight weight_nonnegative weight_normalized perfect_support

/-! ## Independently derived corrected quantum input -/

theorem raw_to_paper_relabeling_preserves_outcome_agreement
    (left right : Deutsch.Foundations.QubitIndex) :
    paperBitOfRaw left = paperBitOfRaw right ↔ left = right :=
  paperBits_equal_iff_rawBits_equal left right

theorem corrected_same_outcome_probability_is_cosine_squared
    (theta phi : ℝ) :
    sameOutcomeProbability theta phi =
      Real.cos ((theta - phi) / 2) ^ 2 :=
  sameOutcomeProbability_eq_cos_sq theta phi

theorem all_distinct_three_setting_pairs_have_probability_one_quarter
    (i j : Setting) (hij : i ≠ j) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle j) =
      (1 / 4 : ℝ) :=
  threeSetting_sameOutcomeProbability_of_ne i j hij

theorem all_equal_three_setting_pairs_agree_certainly (i : Setting) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle i) = 1 :=
  threeSetting_sameOutcomeProbability_self i

/-! ## Corrected source-level contradiction -/

theorem corrected_epr_predictions_refute_the_explicit_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False :=
  corrected_epr_three_settings_refute_local_assignments
    weight weight_nonnegative weight_normalized perfect_support reproduces

theorem no_explicit_local_model_reproduces_the_corrected_epr_family
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_local_assignments_reproduce_corrected_epr_three_settings
    weight weight_nonnegative weight_normalized perfect_support

theorem corrected_epr_probabilities_alone_refute_the_normalized_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False :=
  corrected_epr_three_settings_refute_normalized_local_model
    weight weight_nonnegative weight_normalized reproduces

theorem no_normalized_local_model_reproduces_the_corrected_epr_family
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_normalized_local_model_reproduces_corrected_epr_three_settings
    weight weight_nonnegative weight_normalized

end
end BellVerification
end DeutschTests
