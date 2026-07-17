import Deutsch.Bell.Finite
import Deutsch.Bell.Quantum

/-!
# Corrected finite Bell contradiction

This module connects the independently derived three-setting EPR agreement probabilities to the
explicit two-party local-assignment inequality.  The conclusion rejects only the listed finite
model assumptions; it contains no claim about measurement ontology or interpretations of quantum
theory.
-/

namespace Deutsch
namespace Bell

open scoped BigOperators

noncomputable section

/-- A local model reproduces the corrected quantum agreement probability at every pair of the
three named settings. -/
def ReproducesThreeSettingQuantumAgreements
    (weight : LocalAssignment → ℝ) : Prop :=
  ∀ aliceSetting bobSetting : Setting,
    crossPartyAgreementProbability weight aliceSetting bobSetting =
      sameOutcomeProbability
        (threeSettingAngle aliceSetting) (threeSettingAngle bobSetting)

/-- Reproduction of the corrected quantum family gives the three quarter-agreement premises used
by the finite Bell inequality. -/
theorem reproducesThreeSettingQuantumAgreements_quarters
    (weight : LocalAssignment → ℝ)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    crossPartyAgreementProbability weight 0 1 = (1 / 4 : ℝ) ∧
      crossPartyAgreementProbability weight 1 2 = (1 / 4 : ℝ) ∧
        crossPartyAgreementProbability weight 0 2 = (1 / 4 : ℝ) := by
  constructor
  · exact (reproduces 0 1).trans
      (threeSetting_sameOutcomeProbability_of_ne 0 1 (by decide))
  · constructor
    · exact (reproduces 1 2).trans
        (threeSetting_sameOutcomeProbability_of_ne 1 2 (by decide))
    · exact (reproduces 0 2).trans
        (threeSetting_sameOutcomeProbability_of_ne 0 2 (by decide))

/-- Reproducing the corrected family also gives probability-one agreement at every equal-setting
pair. -/
theorem reproducesThreeSettingQuantumAgreements_equal_setting
    (weight : LocalAssignment → ℝ)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    ∀ setting,
      crossPartyAgreementProbability weight setting setting = 1 := by
  intro setting
  exact (reproduces setting setting).trans
    (threeSetting_sameOutcomeProbability_self setting)

/--
Corrected Stage 11 contradiction.  There is no normalized nonnegative, setting-independent
distribution over deterministic local response tables that both has perfect equal-setting
agreement on positive-weight support and reproduces the corrected EPR agreement probabilities at
the three named settings.
-/
theorem corrected_epr_three_settings_refute_local_assignments
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False := by
  rcases reproducesThreeSettingQuantumAgreements_quarters weight reproduces with
    ⟨h01, h12, h02⟩
  exact quarter_agreements_contradict_local_assignments
    weight weight_nonnegative weight_normalized perfect_support h01 h12 h02

/-- Negated packaging of the corrected contradiction, convenient for downstream reuse. -/
theorem no_local_assignments_reproduce_corrected_epr_three_settings
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    ¬ ReproducesThreeSettingQuantumAgreements weight := by
  intro reproduces
  exact corrected_epr_three_settings_refute_local_assignments
    weight weight_nonnegative weight_normalized perfect_support reproduces

/--
Observable-probability form of the corrected contradiction. Perfect equal-setting support is no
longer a premise: it is derived from nonnegativity, normalization, and the reproduced quantum
probability-one predictions. Zero-weight response tables remain irrelevant.
-/
theorem corrected_epr_three_settings_refute_normalized_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False := by
  have perfect_support := perfectEqualSettingSupport_of_agreementProbability_one
    weight weight_nonnegative weight_normalized
      (reproducesThreeSettingQuantumAgreements_equal_setting weight reproduces)
  exact corrected_epr_three_settings_refute_local_assignments
    weight weight_nonnegative weight_normalized perfect_support reproduces

/-- No normalized nonnegative deterministic local-response distribution reproduces the complete
corrected three-setting agreement table. -/
theorem no_normalized_local_model_reproduces_corrected_epr_three_settings
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ ReproducesThreeSettingQuantumAgreements weight := by
  intro reproduces
  exact corrected_epr_three_settings_refute_normalized_local_model
    weight weight_nonnegative weight_normalized reproduces

end

end Bell
end Deutsch
