import Deutsch.Bell

/-!
# Focused Bell verification

These checks keep the Boolean pigeonhole bound, explicit two-party local assumptions, independently
derived quantum probabilities, and final contradiction as separate verification layers.
-/

namespace DeutschTests
namespace BellVerification

open Deutsch Deutsch.Bell
open scoped BigOperators

noncomputable section

/-! ## Genuinely stochastic response witness -/

/-- A Boolean response that assigns equal positive probability to both outcomes. -/
def fairResponseKernel : BoolResponseKernel where
  probability _ := (1 / 2 : ℝ)
  nonnegative := by
    intro
    norm_num
  normalized := by
    norm_num

/--
A one-point hidden space with independent fair responses at every local setting.  The hidden
variable is deterministic, but neither party's response kernel is.
-/
def fairStochasticModel : StochasticLocalModel Unit where
  hiddenWeight _ := 1
  hiddenWeight_nonnegative := by
    intro
    norm_num
  hiddenWeight_normalized := by
    norm_num
  aliceKernel _ _ := fairResponseKernel
  bobKernel _ _ := fairResponseKernel

theorem fair_response_kernel_is_genuinely_nondeterministic :
    fairResponseKernel.probability false = (1 / 2 : ℝ) ∧
      fairResponseKernel.probability true = (1 / 2 : ℝ) := by
  norm_num [fairResponseKernel]

theorem boolean_response_kernel_normalizes (kernel : BoolResponseKernel) :
    ∑ outcome : Bool, kernel.probability outcome = 1 :=
  kernel.normalized

theorem complete_response_table_distribution_normalizes
    (kernel : Setting → BoolResponseKernel) :
    ∑ table : Setting → Bool, responseTableWeight kernel table = 1 :=
  responseTableWeight_normalized kernel

theorem selected_response_table_marginal_is_the_kernel_probability
    (kernel : Setting → BoolResponseKernel)
    (setting : Setting) (outcome : Bool) :
    (∑ table : Setting → Bool,
        responseTableWeight kernel table *
          responseOutcomeIndicator (table setting) outcome) =
      (kernel setting).probability outcome :=
  responseTableWeight_marginal kernel setting outcome

theorem conditional_local_table_distribution_normalizes
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (hidden : Ω) :
    ∑ assignment : LocalAssignment,
      conditionalTableWeight model hidden assignment = 1 :=
  conditionalTableWeight_normalized model hidden

theorem refined_local_table_distribution_is_nonnegative
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (assignment : LocalAssignment) :
    0 ≤ refinedLocalWeight model assignment :=
  refinedLocalWeight_nonnegative model assignment

theorem refined_local_table_distribution_normalizes
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) :
    ∑ assignment : LocalAssignment, refinedLocalWeight model assignment = 1 :=
  refinedLocalWeight_normalized model

theorem fair_refined_table_distribution_normalizes :
    ∑ assignment : LocalAssignment,
      refinedLocalWeight fairStochasticModel assignment = 1 :=
  refinedLocalWeight_normalized fairStochasticModel

theorem fair_stochastic_joint_outcome_is_one_quarter
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    stochasticJointOutcomeProbability fairStochasticModel
      aliceSetting bobSetting aliceOutcome bobOutcome = (1 / 4 : ℝ) := by
  norm_num [stochasticJointOutcomeProbability, fairStochasticModel,
    fairResponseKernel]

theorem stochastic_joint_outcomes_have_the_explicit_factorization
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    stochasticJointOutcomeProbability model
        aliceSetting bobSetting aliceOutcome bobOutcome =
      ∑ hidden,
        model.hiddenWeight hidden *
          ((model.aliceKernel hidden aliceSetting).probability aliceOutcome *
            (model.bobKernel hidden bobSetting).probability bobOutcome) :=
  stochasticJointOutcomeProbability_factorization
    model aliceSetting bobSetting aliceOutcome bobOutcome

theorem refined_table_preserves_alice_marginals
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) :
    tableAliceOutcomeProbability (refinedLocalWeight model) setting outcome =
      stochasticAliceOutcomeProbability model setting outcome :=
  refinedLocalWeight_preserves_alice_outcome model setting outcome

theorem refined_table_preserves_bob_marginals
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) :
    tableBobOutcomeProbability (refinedLocalWeight model) setting outcome =
      stochasticBobOutcomeProbability model setting outcome :=
  refinedLocalWeight_preserves_bob_outcome model setting outcome

theorem refined_table_preserves_every_joint_outcome
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    tableJointOutcomeProbability (refinedLocalWeight model)
        aliceSetting bobSetting aliceOutcome bobOutcome =
      stochasticJointOutcomeProbability model
        aliceSetting bobSetting aliceOutcome bobOutcome :=
  refinedLocalWeight_preserves_joint_outcome
    model aliceSetting bobSetting aliceOutcome bobOutcome

theorem refined_table_preserves_every_agreement_probability
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) :
    crossPartyAgreementProbability (refinedLocalWeight model)
        aliceSetting bobSetting =
      stochasticAgreementProbability model aliceSetting bobSetting :=
  refinedLocalWeight_preserves_agreement model aliceSetting bobSetting

theorem stochastic_reproduction_transfers_to_the_refined_table
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (reproduces : ReproducesThreeSettingStochasticAgreements model) :
    ReproducesThreeSettingQuantumAgreements (refinedLocalWeight model) :=
  refinedLocalWeight_reproduces_three_setting_agreements model reproduces

theorem epr_predictions_refute_every_finite_stochastic_local_model
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (reproduces : ReproducesThreeSettingStochasticAgreements model) :
    False :=
  epr_three_settings_refute_stochastic_local_model model reproduces

theorem no_finite_stochastic_local_model_reproduces_the_epr_family
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) :
    ¬ ReproducesThreeSettingStochasticAgreements model :=
  no_stochastic_local_model_reproduces_epr_three_settings model

theorem fair_refined_table_joint_true_false_is_one_quarter :
    tableJointOutcomeProbability (refinedLocalWeight fairStochasticModel)
      0 1 true false = (1 / 4 : ℝ) := by
  rw [refinedLocalWeight_preserves_joint_outcome]
  exact fair_stochastic_joint_outcome_is_one_quarter 0 1 true false

/-! ## Direct finite-moment route -/

theorem direct_equation42_mean_square
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    (setting : Fin 3) :
    space.expectation (fun sample =>
      (aliceValue alice sample setting - bobValue bob sample setting) ^ 2) = 0 :=
  equation42_mean_square_zero space alice bob reproduces setting

theorem direct_equation43_positive_support
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    {sample : Ω} (sample_positive : 0 < space.weight sample)
    (setting : Fin 3) :
    bob sample setting = alice sample setting :=
  equation43_equal_on_positive_support
    space alice bob reproduces sample_positive setting

theorem direct_equation44_alice_joint_moment
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    (setting₀ setting₁ : Fin 3) :
    space.expectation (fun sample =>
      aliceValue alice sample setting₀ * aliceValue alice sample setting₁) =
        eprJointMoment setting₀ setting₁ :=
  equation44_alice_joint_moment
    space alice bob reproduces setting₀ setting₁

theorem direct_equation45_true_complementary_partition
    (a₀ a₁ a₂ : Bool) :
    booleanIndicator a₀ =
      booleanIndicator a₀ * disjunctionIndicator a₁ a₂ +
        booleanIndicator a₀ * (1 - disjunctionIndicator a₁ a₂) :=
  equation45_complementary_partition a₀ a₁ a₂

theorem direct_equation46_all_displayed_comparisons
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) = equation46PartitionedMean space alice ∧
      equation46PartitionedMean space alice ≤ equation46ExpandedMean space alice ∧
      equation46ExpandedMean space alice ≤
        (3 / 8 : ℝ) - equation46TripleMean space alice ∧
      (3 / 8 : ℝ) - equation46TripleMean space alice ≤ (3 / 8 : ℝ) :=
  equation46_chain space alice bob reproduces

theorem direct_equation46_reaches_the_impossible_bound
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) ≤ (3 / 8 : ℝ) :=
  equation46_impossible_bound space alice bob reproduces

/-! ## The zero-weight boundary in Equation (43) -/

/-- A two-sample space whose `true` sample has zero probability. -/
def supportBoundaryWeight : FiniteProbabilityWeight Bool where
  weight sample := if sample then 0 else 1
  nonnegative := by
    intro sample
    cases sample <;> norm_num
  normalized := by
    norm_num

/-- Alice returns zero at both samples. -/
def supportBoundaryAlice (_sample : Bool) (_setting : Fin 3) : Bool :=
  false

/-- Bob differs from Alice only at the zero-weight sample. -/
def supportBoundaryBob (sample : Bool) (_setting : Fin 3) : Bool :=
  sample

/--
Zero mean square does not force equality at a zero-weight sample.  This is the concrete boundary
behind the strict positive-support premise in Equation (43).
-/
theorem zero_weight_sample_can_disagree_despite_zero_mean_square
    (setting : Fin 3) :
    supportBoundaryWeight.weight true = 0 ∧
      supportBoundaryWeight.expectation (fun sample =>
        (aliceValue supportBoundaryAlice sample setting -
          bobValue supportBoundaryBob sample setting) ^ 2) = 0 ∧
      supportBoundaryBob true setting ≠ supportBoundaryAlice true setting := by
  norm_num [supportBoundaryWeight, FiniteProbabilityWeight.expectation,
    supportBoundaryAlice, supportBoundaryBob, aliceValue, bobValue,
    booleanIndicator]

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

/-! ## Independently derived quantum input -/

theorem raw_to_paper_relabeling_preserves_outcome_agreement
    (left right : Deutsch.Foundations.QubitIndex) :
    paperBitOfRaw left = paperBitOfRaw right ↔ left = right :=
  paperBits_equal_iff_rawBits_equal left right

theorem same_outcome_probability_is_cosine_squared
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

/-! ## Three-setting contradiction -/

theorem epr_predictions_refute_the_explicit_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False :=
  epr_three_settings_refute_local_assignments
    weight weight_nonnegative weight_normalized perfect_support reproduces

theorem no_explicit_local_model_reproduces_the_epr_family
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_local_assignments_reproduce_epr_three_settings
    weight weight_nonnegative weight_normalized perfect_support

theorem epr_probabilities_alone_refute_the_normalized_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (reproduces : ReproducesThreeSettingQuantumAgreements weight) :
    False :=
  epr_three_settings_refute_normalized_local_model
    weight weight_nonnegative weight_normalized reproduces

theorem no_normalized_local_model_reproduces_the_epr_family
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_normalized_local_model_reproduces_epr_three_settings
    weight weight_nonnegative weight_normalized

/-! ## Independent contradiction-route check -/

/--
The expectation-chain and pigeonhole routes each reject their own explicit reproduction contract.
The first component invokes only the direct Equation (46) theorem; the second invokes the
pre-existing deterministic-assignment theorem.
-/
theorem both_finite_bell_routes_reject_their_named_contracts
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    (¬ ReproducesThreeSettingEPRMoments space alice bob) ∧
      (¬ ReproducesThreeSettingQuantumAgreements weight) := by
  constructor
  · intro reproduces
    exact equation46_contradiction space alice bob reproduces
  · exact no_normalized_local_model_reproduces_epr_three_settings
      weight weight_nonnegative weight_normalized

end
end BellVerification
end DeutschTests
