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

end

end Bell
end Deutsch
