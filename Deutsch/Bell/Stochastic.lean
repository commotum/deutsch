import Deutsch.Bell.Contradiction
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite stochastic local response models

This module gives the constructive finite bridge between factorizable stochastic response
kernels and complete deterministic local response tables.  The hidden-variable weight is
setting-independent, and each party's response kernel receives only that party's setting.

For each hidden value, the six local response probabilities define a product distribution on the
three Alice and three Bob table entries.  Averaging those conditional table distributions over the
hidden variable produces a normalized nonnegative weight on `LocalAssignment`.  The construction
preserves all one-party and joint outcome probabilities, hence also agreement probabilities.
-/

namespace Deutsch
namespace Bell

open scoped BigOperators

noncomputable section

/-- A normalized nonnegative probability kernel on Boolean outcomes. -/
structure BoolResponseKernel where
  probability : Bool → ℝ
  nonnegative : ∀ outcome, 0 ≤ probability outcome
  normalized : ∑ outcome : Bool, probability outcome = 1

/--
A finite setting-independent hidden-variable model with local Boolean response kernels.

The hidden weight has no setting argument.  Alice's kernel receives only Alice's setting, and
Bob's kernel receives only Bob's setting.  Joint response probabilities are defined below as the
product of these two kernels.
-/
structure StochasticLocalModel (Ω : Type*) [Fintype Ω] where
  hiddenWeight : Ω → ℝ
  hiddenWeight_nonnegative : ∀ hidden, 0 ≤ hiddenWeight hidden
  hiddenWeight_normalized : ∑ hidden, hiddenWeight hidden = 1
  aliceKernel : Ω → Setting → BoolResponseKernel
  bobKernel : Ω → Setting → BoolResponseKernel

/-- Product probability of a complete response table for one party and one hidden value. -/
def responseTableWeight
    (kernel : Setting → BoolResponseKernel) (table : Setting → Bool) : ℝ :=
  ∏ setting, (kernel setting).probability (table setting)

/-- Finite distributivity for a product law on complete Boolean response tables. -/
private theorem sum_responseTableProduct
    (probability : Setting → Bool → ℝ) :
    ∑ table : Setting → Bool, ∏ setting, probability setting (table setting) =
      ∏ setting, ∑ outcome : Bool, probability setting outcome := by
  have table_product_sum :=
    Finset.sum_prod_piFinset (R := ℝ) (s := Finset.univ) (g := probability)
  rw [Fintype.piFinset_univ] at table_product_sum
  exact table_product_sum

/-- A response-table product distribution is normalized. -/
theorem responseTableWeight_normalized
    (kernel : Setting → BoolResponseKernel) :
    ∑ table : Setting → Bool, responseTableWeight kernel table = 1 := by
  unfold responseTableWeight
  calc
    ∑ table : Setting → Bool,
        ∏ setting, (kernel setting).probability (table setting) =
      ∏ setting, ∑ outcome : Bool, (kernel setting).probability outcome := by
        exact sum_responseTableProduct fun setting outcome =>
          (kernel setting).probability outcome
    _ = 1 := by
      simp_rw [(kernel _).normalized]
      simp

/-- Real indicator of one specified Boolean outcome. -/
def responseOutcomeIndicator (observed expected : Bool) : ℝ :=
  if observed = expected then 1 else 0

@[simp]
theorem responseOutcomeIndicator_self (outcome : Bool) :
    responseOutcomeIndicator outcome outcome = 1 := by
  simp [responseOutcomeIndicator]

theorem responseOutcomeIndicator_nonnegative (observed expected : Bool) :
    0 ≤ responseOutcomeIndicator observed expected := by
  simp only [responseOutcomeIndicator]
  split <;> norm_num

/--
The selected-coordinate marginal of a product distribution on a complete response table is the
corresponding response-kernel probability.
-/
theorem responseTableWeight_marginal
    (kernel : Setting → BoolResponseKernel)
    (selectedSetting : Setting) (selectedOutcome : Bool) :
    (∑ table : Setting → Bool,
        responseTableWeight kernel table *
          responseOutcomeIndicator (table selectedSetting) selectedOutcome) =
      (kernel selectedSetting).probability selectedOutcome := by
  classical
  let selectedProbability : Setting → Bool → ℝ :=
    fun setting outcome =>
      if setting = selectedSetting then
        if outcome = selectedOutcome then (kernel setting).probability outcome else 0
      else
        (kernel setting).probability outcome
  have summand_eq :
      ∀ table : Setting → Bool,
        responseTableWeight kernel table *
            responseOutcomeIndicator (table selectedSetting) selectedOutcome =
          ∏ setting, selectedProbability setting (table setting) := by
    intro table
    by_cases selected : table selectedSetting = selectedOutcome
    · rw [responseOutcomeIndicator]
      simp only [if_pos selected, mul_one]
      unfold responseTableWeight
      apply Finset.prod_congr rfl
      intro setting _
      by_cases hsetting : setting = selectedSetting
      · subst setting
        simp [selectedProbability, selected]
      · simp [selectedProbability, hsetting]
    · rw [responseOutcomeIndicator]
      simp only [if_neg selected, mul_zero]
      exact (Finset.prod_eq_zero (Finset.mem_univ selectedSetting)
        (by simp [selectedProbability, selected])).symm
  calc
    ∑ table : Setting → Bool,
        responseTableWeight kernel table *
          responseOutcomeIndicator (table selectedSetting) selectedOutcome =
      ∑ table : Setting → Bool,
        ∏ setting, selectedProbability setting (table setting) := by
          apply Finset.sum_congr rfl
          intro table _
          exact summand_eq table
    _ = ∏ setting, ∑ outcome : Bool, selectedProbability setting outcome :=
      sum_responseTableProduct selectedProbability
    _ = ∑ outcome : Bool, selectedProbability selectedSetting outcome := by
      apply Fintype.prod_eq_single selectedSetting
      intro setting hsetting
      rw [show (∑ outcome : Bool, selectedProbability setting outcome) =
          ∑ outcome : Bool, (kernel setting).probability outcome by
        apply Finset.sum_congr rfl
        intro outcome _
        simp [selectedProbability, hsetting]]
      exact (kernel setting).normalized
    _ = (kernel selectedSetting).probability selectedOutcome := by
      cases selectedOutcome <;>
        simp [selectedProbability]

/-- Conditional product weight of a complete Alice--Bob response table at one hidden value. -/
def conditionalTableWeight
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (hidden : Ω) (assignment : LocalAssignment) : ℝ :=
  responseTableWeight (model.aliceKernel hidden) assignment.1 *
    responseTableWeight (model.bobKernel hidden) assignment.2

/-- Every conditional complete-table weight is nonnegative. -/
theorem conditionalTableWeight_nonnegative
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (hidden : Ω) (assignment : LocalAssignment) :
    0 ≤ conditionalTableWeight model hidden assignment := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun setting _ =>
      (model.aliceKernel hidden setting).nonnegative _
  · exact Finset.prod_nonneg fun setting _ =>
      (model.bobKernel hidden setting).nonnegative _

/-- For each hidden value, the conditional product distribution on complete tables normalizes. -/
theorem conditionalTableWeight_normalized
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) (hidden : Ω) :
    ∑ assignment : LocalAssignment, conditionalTableWeight model hidden assignment = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalTableWeight]
  calc
    ∑ aliceTable : Setting → Bool,
        ∑ bobTable : Setting → Bool,
          responseTableWeight (model.aliceKernel hidden) aliceTable *
            responseTableWeight (model.bobKernel hidden) bobTable =
      ∑ aliceTable : Setting → Bool,
        responseTableWeight (model.aliceKernel hidden) aliceTable *
          (∑ bobTable : Setting → Bool,
            responseTableWeight (model.bobKernel hidden) bobTable) := by
              apply Finset.sum_congr rfl
              intro aliceTable _
              rw [Finset.mul_sum]
    _ = 1 := by
      rw [responseTableWeight_normalized]
      simp only [mul_one]
      exact responseTableWeight_normalized _

/--
The explicit setting-independent weight on complete deterministic local response tables obtained
by averaging the conditional product-table distribution over the hidden variable.
-/
def refinedLocalWeight
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (assignment : LocalAssignment) : ℝ :=
  ∑ hidden, model.hiddenWeight hidden * conditionalTableWeight model hidden assignment

/-- The refined complete-table weight is pointwise nonnegative. -/
theorem refinedLocalWeight_nonnegative
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (assignment : LocalAssignment) :
    0 ≤ refinedLocalWeight model assignment := by
  exact Finset.sum_nonneg fun hidden _ =>
    mul_nonneg (model.hiddenWeight_nonnegative hidden)
      (conditionalTableWeight_nonnegative model hidden assignment)

/-- The refined complete-table weight has total mass one. -/
theorem refinedLocalWeight_normalized
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) :
    ∑ assignment : LocalAssignment, refinedLocalWeight model assignment = 1 := by
  unfold refinedLocalWeight
  calc
    ∑ assignment : LocalAssignment,
        ∑ hidden, model.hiddenWeight hidden *
          conditionalTableWeight model hidden assignment =
      ∑ hidden, model.hiddenWeight hidden *
        (∑ assignment : LocalAssignment,
          conditionalTableWeight model hidden assignment) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ = 1 := by
      simp_rw [conditionalTableWeight_normalized]
      simpa using model.hiddenWeight_normalized

/-! ## Observable probabilities -/

/-- Alice's one-party outcome probability under a weight on complete local response tables. -/
def tableAliceOutcomeProbability
    (weight : LocalAssignment → ℝ) (setting : Setting) (outcome : Bool) : ℝ :=
  ∑ assignment : LocalAssignment,
    weight assignment *
      responseOutcomeIndicator (aliceResponse assignment setting) outcome

/-- Bob's one-party outcome probability under a weight on complete local response tables. -/
def tableBobOutcomeProbability
    (weight : LocalAssignment → ℝ) (setting : Setting) (outcome : Bool) : ℝ :=
  ∑ assignment : LocalAssignment,
    weight assignment *
      responseOutcomeIndicator (bobResponse assignment setting) outcome

/-- A specified Alice--Bob joint outcome probability under a complete-table weight. -/
def tableJointOutcomeProbability
    (weight : LocalAssignment → ℝ)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) : ℝ :=
  ∑ assignment : LocalAssignment,
    weight assignment *
      responseOutcomeIndicator (aliceResponse assignment aliceSetting) aliceOutcome *
      responseOutcomeIndicator (bobResponse assignment bobSetting) bobOutcome

/-- Alice's local stochastic outcome probability, averaged over the setting-free hidden weight. -/
def stochasticAliceOutcomeProbability
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) : ℝ :=
  ∑ hidden,
    model.hiddenWeight hidden *
      (model.aliceKernel hidden setting).probability outcome

/-- Bob's local stochastic outcome probability, averaged over the setting-free hidden weight. -/
def stochasticBobOutcomeProbability
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) : ℝ :=
  ∑ hidden,
    model.hiddenWeight hidden *
      (model.bobKernel hidden setting).probability outcome

/--
The factorizable Alice--Bob joint outcome probability.  The same setting-independent hidden weight
is averaged against the product of Alice's setting-local kernel and Bob's setting-local kernel.
-/
def stochasticJointOutcomeProbability
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) : ℝ :=
  ∑ hidden,
    model.hiddenWeight hidden *
      ((model.aliceKernel hidden aliceSetting).probability aliceOutcome *
        (model.bobKernel hidden bobSetting).probability bobOutcome)

/-- Explicit factorization formula for every pair of local settings and outcomes. -/
theorem stochasticJointOutcomeProbability_factorization
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    stochasticJointOutcomeProbability model
        aliceSetting bobSetting aliceOutcome bobOutcome =
      ∑ hidden,
        model.hiddenWeight hidden *
          ((model.aliceKernel hidden aliceSetting).probability aliceOutcome *
            (model.bobKernel hidden bobSetting).probability bobOutcome) :=
  rfl

/--
The stochastic probability that the parties agree, written directly as the hidden-weighted sum of
the two diagonal products.
-/
def stochasticAgreementProbability
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) : ℝ :=
  ∑ hidden,
    model.hiddenWeight hidden *
      (∑ outcome : Bool,
        (model.aliceKernel hidden aliceSetting).probability outcome *
          (model.bobKernel hidden bobSetting).probability outcome)

private theorem refinedLocalWeight_sum_mul
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (value : LocalAssignment → ℝ) :
    (∑ assignment : LocalAssignment,
        refinedLocalWeight model assignment * value assignment) =
      ∑ hidden,
        model.hiddenWeight hidden *
          (∑ assignment : LocalAssignment,
            conditionalTableWeight model hidden assignment * value assignment) := by
  unfold refinedLocalWeight
  calc
    ∑ assignment : LocalAssignment,
        (∑ hidden,
          model.hiddenWeight hidden *
            conditionalTableWeight model hidden assignment) * value assignment =
      ∑ assignment : LocalAssignment,
        ∑ hidden,
          model.hiddenWeight hidden *
            (conditionalTableWeight model hidden assignment * value assignment) := by
              apply Finset.sum_congr rfl
              intro assignment _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro hidden _
              ring
    _ = ∑ hidden,
        ∑ assignment : LocalAssignment,
          model.hiddenWeight hidden *
            (conditionalTableWeight model hidden assignment * value assignment) := by
              rw [Finset.sum_comm]
    _ = ∑ hidden,
        model.hiddenWeight hidden *
          (∑ assignment : LocalAssignment,
            conditionalTableWeight model hidden assignment * value assignment) := by
              apply Finset.sum_congr rfl
              intro hidden _
              rw [Finset.mul_sum]

/-- Conditional table refinement preserves every Alice outcome probability. -/
theorem conditionalTableWeight_alice_marginal
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) (hidden : Ω)
    (setting : Setting) (outcome : Bool) :
    (∑ assignment : LocalAssignment,
        conditionalTableWeight model hidden assignment *
          responseOutcomeIndicator (aliceResponse assignment setting) outcome) =
      (model.aliceKernel hidden setting).probability outcome := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalTableWeight, aliceResponse]
  calc
    ∑ aliceTable : Setting → Bool,
        ∑ bobTable : Setting → Bool,
          (responseTableWeight (model.aliceKernel hidden) aliceTable *
              responseTableWeight (model.bobKernel hidden) bobTable) *
            responseOutcomeIndicator (aliceTable setting) outcome =
      ∑ aliceTable : Setting → Bool,
        (responseTableWeight (model.aliceKernel hidden) aliceTable *
            responseOutcomeIndicator (aliceTable setting) outcome) *
          (∑ bobTable : Setting → Bool,
            responseTableWeight (model.bobKernel hidden) bobTable) := by
              apply Finset.sum_congr rfl
              intro aliceTable _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro bobTable _
              ring
    _ = (model.aliceKernel hidden setting).probability outcome := by
      rw [responseTableWeight_normalized]
      simp only [mul_one]
      exact responseTableWeight_marginal _ setting outcome

/-- Conditional table refinement preserves every Bob outcome probability. -/
theorem conditionalTableWeight_bob_marginal
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) (hidden : Ω)
    (setting : Setting) (outcome : Bool) :
    (∑ assignment : LocalAssignment,
        conditionalTableWeight model hidden assignment *
          responseOutcomeIndicator (bobResponse assignment setting) outcome) =
      (model.bobKernel hidden setting).probability outcome := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalTableWeight, bobResponse]
  calc
    ∑ aliceTable : Setting → Bool,
        ∑ bobTable : Setting → Bool,
          (responseTableWeight (model.aliceKernel hidden) aliceTable *
              responseTableWeight (model.bobKernel hidden) bobTable) *
            responseOutcomeIndicator (bobTable setting) outcome =
      (∑ aliceTable : Setting → Bool,
        responseTableWeight (model.aliceKernel hidden) aliceTable) *
          (∑ bobTable : Setting → Bool,
            responseTableWeight (model.bobKernel hidden) bobTable *
              responseOutcomeIndicator (bobTable setting) outcome) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro aliceTable _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro bobTable _
                ring
    _ = (model.bobKernel hidden setting).probability outcome := by
      rw [responseTableWeight_normalized, one_mul]
      exact responseTableWeight_marginal _ setting outcome

/-- Conditional table refinement preserves every specified pair of outcomes. -/
theorem conditionalTableWeight_joint_marginal
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) (hidden : Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    (∑ assignment : LocalAssignment,
        conditionalTableWeight model hidden assignment *
          responseOutcomeIndicator (aliceResponse assignment aliceSetting) aliceOutcome *
          responseOutcomeIndicator (bobResponse assignment bobSetting) bobOutcome) =
      (model.aliceKernel hidden aliceSetting).probability aliceOutcome *
        (model.bobKernel hidden bobSetting).probability bobOutcome := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalTableWeight, aliceResponse, bobResponse]
  calc
    ∑ aliceTable : Setting → Bool,
        ∑ bobTable : Setting → Bool,
          (responseTableWeight (model.aliceKernel hidden) aliceTable *
              responseTableWeight (model.bobKernel hidden) bobTable) *
            responseOutcomeIndicator (aliceTable aliceSetting) aliceOutcome *
            responseOutcomeIndicator (bobTable bobSetting) bobOutcome =
      (∑ aliceTable : Setting → Bool,
        responseTableWeight (model.aliceKernel hidden) aliceTable *
          responseOutcomeIndicator (aliceTable aliceSetting) aliceOutcome) *
        (∑ bobTable : Setting → Bool,
          responseTableWeight (model.bobKernel hidden) bobTable *
            responseOutcomeIndicator (bobTable bobSetting) bobOutcome) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro aliceTable _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro bobTable _
              ring
    _ = (model.aliceKernel hidden aliceSetting).probability aliceOutcome *
        (model.bobKernel hidden bobSetting).probability bobOutcome := by
          rw [responseTableWeight_marginal, responseTableWeight_marginal]

/-- The refined complete-table model preserves every Alice one-party outcome probability. -/
theorem refinedLocalWeight_preserves_alice_outcome
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) :
    tableAliceOutcomeProbability (refinedLocalWeight model) setting outcome =
      stochasticAliceOutcomeProbability model setting outcome := by
  unfold tableAliceOutcomeProbability stochasticAliceOutcomeProbability
  rw [refinedLocalWeight_sum_mul]
  apply Finset.sum_congr rfl
  intro hidden _
  rw [conditionalTableWeight_alice_marginal]

/-- The refined complete-table model preserves every Bob one-party outcome probability. -/
theorem refinedLocalWeight_preserves_bob_outcome
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (setting : Setting) (outcome : Bool) :
    tableBobOutcomeProbability (refinedLocalWeight model) setting outcome =
      stochasticBobOutcomeProbability model setting outcome := by
  unfold tableBobOutcomeProbability stochasticBobOutcomeProbability
  rw [refinedLocalWeight_sum_mul]
  apply Finset.sum_congr rfl
  intro hidden _
  rw [conditionalTableWeight_bob_marginal]

/-- The refined complete-table model preserves every joint outcome at every settings pair. -/
theorem refinedLocalWeight_preserves_joint_outcome
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) (aliceOutcome bobOutcome : Bool) :
    tableJointOutcomeProbability (refinedLocalWeight model)
        aliceSetting bobSetting aliceOutcome bobOutcome =
      stochasticJointOutcomeProbability model
        aliceSetting bobSetting aliceOutcome bobOutcome := by
  unfold tableJointOutcomeProbability stochasticJointOutcomeProbability
  simp_rw [mul_assoc]
  rw [refinedLocalWeight_sum_mul]
  apply Finset.sum_congr rfl
  intro hidden _
  congr 1
  simpa [mul_assoc] using
    (conditionalTableWeight_joint_marginal model hidden
      aliceSetting bobSetting aliceOutcome bobOutcome)

/-- Complete-table agreement is the sum of its two diagonal joint-outcome probabilities. -/
theorem crossPartyAgreementProbability_eq_joint_outcomes
    (weight : LocalAssignment → ℝ) (aliceSetting bobSetting : Setting) :
    crossPartyAgreementProbability weight aliceSetting bobSetting =
      ∑ outcome : Bool,
        tableJointOutcomeProbability weight
          aliceSetting bobSetting outcome outcome := by
  unfold crossPartyAgreementProbability tableJointOutcomeProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assignment _
  cases hAlice : aliceResponse assignment aliceSetting <;>
    cases hBob : bobResponse assignment bobSetting <;>
      simp [crossPartyAgreementIndicator, hAlice, hBob,
        responseOutcomeIndicator]

/-- Stochastic agreement is the sum of its two factorizable diagonal joint probabilities. -/
theorem stochasticAgreementProbability_eq_joint_outcomes
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) :
    stochasticAgreementProbability model aliceSetting bobSetting =
      ∑ outcome : Bool,
        stochasticJointOutcomeProbability model
          aliceSetting bobSetting outcome outcome := by
  unfold stochasticAgreementProbability stochasticJointOutcomeProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hidden _
  rw [Finset.mul_sum]

/-- The refined deterministic-table distribution preserves every agreement probability. -/
theorem refinedLocalWeight_preserves_agreement
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (aliceSetting bobSetting : Setting) :
    crossPartyAgreementProbability (refinedLocalWeight model)
        aliceSetting bobSetting =
      stochasticAgreementProbability model aliceSetting bobSetting := by
  rw [crossPartyAgreementProbability_eq_joint_outcomes,
    stochasticAgreementProbability_eq_joint_outcomes]
  apply Finset.sum_congr rfl
  intro outcome _
  exact refinedLocalWeight_preserves_joint_outcome
    model aliceSetting bobSetting outcome outcome

/-! ## Three-setting EPR contradiction -/

/--
A finite factorizable stochastic local model reproduces the EPR agreement family when its
agreement probability equals the quantum prediction at every pair of the three settings.
-/
def ReproducesThreeSettingStochasticAgreements
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) : Prop :=
  ∀ aliceSetting bobSetting : Setting,
    stochasticAgreementProbability model aliceSetting bobSetting =
      sameOutcomeProbability
        (threeSettingAngle aliceSetting) (threeSettingAngle bobSetting)

/-- Agreement reproduction transfers constructively to the refined complete-table distribution. -/
theorem refinedLocalWeight_reproduces_three_setting_agreements
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (reproduces : ReproducesThreeSettingStochasticAgreements model) :
    ReproducesThreeSettingQuantumAgreements (refinedLocalWeight model) := by
  intro aliceSetting bobSetting
  exact (refinedLocalWeight_preserves_agreement
    model aliceSetting bobSetting).trans (reproduces aliceSetting bobSetting)

/--
No finite, normalized, nonnegative, setting-independent hidden-variable model with normalized
nonnegative local response kernels and factorizable joint responses reproduces the complete
three-setting EPR agreement family.

There is no deterministic response-table or perfect-support premise: the complete-table weight is
constructed from the kernels, and equal-setting support is derived downstream from the reproduced
probability-one predictions.
-/
theorem epr_three_settings_refute_stochastic_local_model
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω)
    (reproduces : ReproducesThreeSettingStochasticAgreements model) :
    False := by
  exact epr_three_settings_refute_normalized_local_model
    (refinedLocalWeight model)
    (refinedLocalWeight_nonnegative model)
    (refinedLocalWeight_normalized model)
    (refinedLocalWeight_reproduces_three_setting_agreements model reproduces)

/-- Negated packaging of `epr_three_settings_refute_stochastic_local_model`. -/
theorem no_stochastic_local_model_reproduces_epr_three_settings
    {Ω : Type*} [Fintype Ω] (model : StochasticLocalModel Ω) :
    ¬ ReproducesThreeSettingStochasticAgreements model := by
  intro reproduces
  exact epr_three_settings_refute_stochastic_local_model model reproduces

end

end Bell
end Deutsch
