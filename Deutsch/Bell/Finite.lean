import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A finite three-setting Bell inequality

This module isolates the finite combinatorics used by the three-setting Bell argument.  A common
deterministic assignment gives one Boolean result for each of three settings.  A model is an
arbitrary real weight on the eight assignments, subject only to explicit nonnegativity and
normalization hypotheses.

For every assignment, at least one of the three setting-pairs agrees.  Averaging that pointwise
fact proves that the sum of the three agreement probabilities is at least one.  Consequently no
such weight can give agreement probability `1/4` to all three pairs, as predicted by the
EPR calculation for three settings separated pairwise by 120 degrees.
-/

namespace Deutsch
namespace Bell

open scoped BigOperators

noncomputable section

/-- The three measurement settings in the finite Bell argument. -/
abbrev Setting := Fin 3

/-- One predetermined Boolean result for every setting. -/
abbrev CommonAssignment := Setting → Bool

/-- The indicator that one deterministic assignment agrees at two settings. -/
def agreementIndicator (assignment : CommonAssignment) (i j : Setting) : ℝ :=
  if assignment i = assignment j then 1 else 0

@[simp]
theorem agreementIndicator_eq_one {assignment : CommonAssignment} {i j : Setting}
    (h : assignment i = assignment j) :
    agreementIndicator assignment i j = 1 := by
  simp [agreementIndicator, h]

@[simp]
theorem agreementIndicator_eq_zero {assignment : CommonAssignment} {i j : Setting}
    (h : assignment i ≠ assignment j) :
    agreementIndicator assignment i j = 0 := by
  simp [agreementIndicator, h]

/-- Every agreement indicator is nonnegative. -/
theorem agreementIndicator_nonnegative (assignment : CommonAssignment) (i j : Setting) :
    0 ≤ agreementIndicator assignment i j := by
  by_cases h : assignment i = assignment j <;>
    simp [agreementIndicator, h]

/-- Among three Boolean values, at least one of the three unordered pairs agrees. -/
theorem commonAssignment_has_agreeing_pair (assignment : CommonAssignment) :
    assignment 0 = assignment 1 ∨
      assignment 1 = assignment 2 ∨
        assignment 0 = assignment 2 := by
  cases h0 : assignment 0 <;>
    cases h1 : assignment 1 <;>
      cases h2 : assignment 2 <;>
        simp_all

/-- Pointwise form of the finite Bell bound. -/
theorem commonAssignment_indicator_sum_ge_one (assignment : CommonAssignment) :
    1 ≤
      agreementIndicator assignment 0 1 +
        agreementIndicator assignment 1 2 +
          agreementIndicator assignment 0 2 := by
  rcases commonAssignment_has_agreeing_pair assignment with h01 | h12 | h02
  · rw [agreementIndicator_eq_one h01]
    linarith [agreementIndicator_nonnegative assignment 1 2,
      agreementIndicator_nonnegative assignment 0 2]
  · rw [agreementIndicator_eq_one h12]
    linarith [agreementIndicator_nonnegative assignment 0 1,
      agreementIndicator_nonnegative assignment 0 2]
  · rw [agreementIndicator_eq_one h02]
    linarith [agreementIndicator_nonnegative assignment 0 1,
      agreementIndicator_nonnegative assignment 1 2]

/-- Agreement probability induced by a real weight on common deterministic assignments. -/
def agreementProbability (weight : CommonAssignment → ℝ) (i j : Setting) : ℝ :=
  ∑ assignment : CommonAssignment,
    weight assignment * agreementIndicator assignment i j

/--
The finite three-setting Bell inequality.  Its only assumptions on `weight` are pointwise
nonnegativity and total mass one.
-/
theorem three_setting_bell_inequality
    (weight : CommonAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    1 ≤
      agreementProbability weight 0 1 +
        agreementProbability weight 1 2 +
          agreementProbability weight 0 2 := by
  rw [← weight_normalized]
  calc
    ∑ assignment, weight assignment ≤
        ∑ assignment, weight assignment *
          (agreementIndicator assignment 0 1 +
            agreementIndicator assignment 1 2 +
              agreementIndicator assignment 0 2) := by
      refine Finset.sum_le_sum fun assignment _ ↦ ?_
      have h := mul_le_mul_of_nonneg_left
        (commonAssignment_indicator_sum_ge_one assignment)
        (weight_nonnegative assignment)
      simpa using h
    _ = agreementProbability weight 0 1 +
          agreementProbability weight 1 2 +
            agreementProbability weight 0 2 := by
      simp [agreementProbability, mul_add, Finset.sum_add_distrib]

/--
Three agreement probabilities equal to `1/4` contradict every nonnegative normalized common
deterministic-assignment model.
-/
theorem quarter_agreements_contradict_common_assignment
    (weight : CommonAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (agreement_zero_one : agreementProbability weight 0 1 = (1 / 4 : ℝ))
    (agreement_one_two : agreementProbability weight 1 2 = (1 / 4 : ℝ))
    (agreement_zero_two : agreementProbability weight 0 2 = (1 / 4 : ℝ)) :
    False := by
  have hbound := three_setting_bell_inequality
    weight weight_nonnegative weight_normalized
  rw [agreement_zero_one, agreement_one_two, agreement_zero_two] at hbound
  norm_num at hbound

/-- Negated-model packaging of `quarter_agreements_contradict_common_assignment`. -/
theorem no_common_assignment_has_three_quarter_agreements
    (weight : CommonAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ (agreementProbability weight 0 1 = (1 / 4 : ℝ) ∧
      agreementProbability weight 1 2 = (1 / 4 : ℝ) ∧
        agreementProbability weight 0 2 = (1 / 4 : ℝ)) := by
  rintro ⟨h01, h12, h02⟩
  exact quarter_agreements_contradict_common_assignment
    weight weight_nonnegative weight_normalized h01 h12 h02

/-! ## Explicit two-party local model -/

/--
A deterministic local hidden assignment consists of an Alice response table and a Bob response
table.  Each table takes only its own party's setting as input.
-/
abbrev LocalAssignment := (Setting → Bool) × (Setting → Bool)

/-- Alice's response depends only on Alice's setting. -/
def aliceResponse (assignment : LocalAssignment) (aliceSetting : Setting) : Bool :=
  assignment.1 aliceSetting

/-- Bob's response depends only on Bob's setting. -/
def bobResponse (assignment : LocalAssignment) (bobSetting : Setting) : Bool :=
  assignment.2 bobSetting

/-- The indicator that Alice and Bob agree at a specified pair of local settings. -/
def crossPartyAgreementIndicator (assignment : LocalAssignment)
    (aliceSetting bobSetting : Setting) : ℝ :=
  if aliceResponse assignment aliceSetting = bobResponse assignment bobSetting then 1 else 0

/--
The setting-independent hidden-variable average of the cross-party agreement indicator.  The
weight has no measurement-setting argument.
-/
def crossPartyAgreementProbability (weight : LocalAssignment → ℝ)
    (aliceSetting bobSetting : Setting) : ℝ :=
  ∑ assignment : LocalAssignment,
    weight assignment *
      crossPartyAgreementIndicator assignment aliceSetting bobSetting

/--
Every positive-weight deterministic assignment gives Alice and Bob the same result when their
settings are equal.  Zero-weight assignments are deliberately unconstrained.
-/
def HasPerfectEqualSettingSupport (weight : LocalAssignment → ℝ) : Prop :=
  ∀ assignment, 0 < weight assignment →
    ∀ setting, aliceResponse assignment setting = bobResponse assignment setting

/-- Every cross-party agreement indicator is at most one. -/
theorem crossPartyAgreementIndicator_le_one (assignment : LocalAssignment)
    (aliceSetting bobSetting : Setting) :
    crossPartyAgreementIndicator assignment aliceSetting bobSetting ≤ 1 := by
  by_cases h : aliceResponse assignment aliceSetting = bobResponse assignment bobSetting <;>
    simp [crossPartyAgreementIndicator, h]

/--
Probability-one agreement at every equal-setting pair forces equal responses on every
positive-weight assignment.  Nonnegative zero-weight assignments remain unconstrained.
-/
theorem perfectEqualSettingSupport_of_agreementProbability_one
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (equal_setting_probability_one :
      ∀ setting, crossPartyAgreementProbability weight setting setting = 1) :
    HasPerfectEqualSettingSupport weight := by
  intro assignment weight_positive setting
  have hterm_le : ∀ candidate : LocalAssignment,
      weight candidate * crossPartyAgreementIndicator candidate setting setting ≤
        weight candidate := by
    intro candidate
    have h := mul_le_mul_of_nonneg_left
      (crossPartyAgreementIndicator_le_one candidate setting setting)
      (weight_nonnegative candidate)
    simpa using h
  have hsum :
      (∑ candidate : LocalAssignment,
          weight candidate * crossPartyAgreementIndicator candidate setting setting) =
        ∑ candidate : LocalAssignment, weight candidate := by
    calc
      ∑ candidate : LocalAssignment,
          weight candidate * crossPartyAgreementIndicator candidate setting setting =
          crossPartyAgreementProbability weight setting setting := rfl
      _ = 1 := equal_setting_probability_one setting
      _ = ∑ candidate : LocalAssignment, weight candidate := weight_normalized.symm
  have hall_terms_equal :=
    (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ)
      (f := fun candidate : LocalAssignment ↦
        weight candidate * crossPartyAgreementIndicator candidate setting setting)
      (g := weight)
      (fun candidate _ ↦ hterm_le candidate)).mp hsum
  have hterm := hall_terms_equal assignment (Finset.mem_univ assignment)
  have hindicator_one :
      crossPartyAgreementIndicator assignment setting setting = 1 := by
    apply mul_left_cancel₀ (ne_of_gt weight_positive)
    simpa using hterm
  by_contra hne
  simp [crossPartyAgreementIndicator, hne] at hindicator_one

private theorem positive_weight_local_indicator_sum_ge_one
    (weight : LocalAssignment → ℝ)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (assignment : LocalAssignment)
    (weight_positive : 0 < weight assignment) :
    1 ≤
      crossPartyAgreementIndicator assignment 0 1 +
        crossPartyAgreementIndicator assignment 1 2 +
          crossPartyAgreementIndicator assignment 0 2 := by
  have hsupport := perfect_support assignment weight_positive
  have hsupport_one : assignment.1 1 = assignment.2 1 := hsupport 1
  have hsupport_two : assignment.1 2 = assignment.2 2 := hsupport 2
  have hcommon := commonAssignment_indicator_sum_ge_one assignment.1
  unfold crossPartyAgreementIndicator aliceResponse bobResponse
  rw [← hsupport_one, ← hsupport_two]
  simpa [agreementIndicator] using hcommon

private theorem localAssignment_weighted_indicator_bound
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (assignment : LocalAssignment) :
    weight assignment ≤
      weight assignment *
        (crossPartyAgreementIndicator assignment 0 1 +
          crossPartyAgreementIndicator assignment 1 2 +
            crossPartyAgreementIndicator assignment 0 2) := by
  by_cases hzero : weight assignment = 0
  · simp [hzero]
  · have hpositive : 0 < weight assignment :=
      lt_of_le_of_ne (weight_nonnegative assignment) (Ne.symm hzero)
    have hpoint := positive_weight_local_indicator_sum_ge_one
      weight perfect_support assignment hpositive
    have hweighted := mul_le_mul_of_nonneg_left hpoint (weight_nonnegative assignment)
    simpa using hweighted

/--
The two-party local form of the finite Bell inequality.  Besides nonnegative normalized,
setting-independent weights, it assumes perfect equal-setting agreement on positive-weight
support.
-/
theorem local_three_setting_bell_inequality
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    1 ≤
      crossPartyAgreementProbability weight 0 1 +
        crossPartyAgreementProbability weight 1 2 +
          crossPartyAgreementProbability weight 0 2 := by
  rw [← weight_normalized]
  calc
    ∑ assignment, weight assignment ≤
        ∑ assignment, weight assignment *
          (crossPartyAgreementIndicator assignment 0 1 +
            crossPartyAgreementIndicator assignment 1 2 +
              crossPartyAgreementIndicator assignment 0 2) := by
      refine Finset.sum_le_sum fun assignment _ ↦ ?_
      exact localAssignment_weighted_indicator_bound
        weight weight_nonnegative perfect_support assignment
    _ = crossPartyAgreementProbability weight 0 1 +
          crossPartyAgreementProbability weight 1 2 +
            crossPartyAgreementProbability weight 0 2 := by
      simp [crossPartyAgreementProbability, mul_add, Finset.sum_add_distrib]

/--
Observable-probability form of `local_three_setting_bell_inequality`: perfect support is derived
from probability-one agreement at each equal-setting pair.
-/
theorem local_three_setting_bell_inequality_of_equal_setting_probability_one
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (equal_setting_probability_one :
      ∀ setting, crossPartyAgreementProbability weight setting setting = 1) :
    1 ≤
      crossPartyAgreementProbability weight 0 1 +
        crossPartyAgreementProbability weight 1 2 +
          crossPartyAgreementProbability weight 0 2 := by
  exact local_three_setting_bell_inequality
    weight weight_nonnegative weight_normalized
      (perfectEqualSettingSupport_of_agreementProbability_one
        weight weight_nonnegative weight_normalized equal_setting_probability_one)

/--
The three `1/4` cross-party agreement predictions contradict the explicit local model
assumptions.
-/
theorem quarter_agreements_contradict_local_assignments
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight)
    (agreement_zero_one : crossPartyAgreementProbability weight 0 1 = (1 / 4 : ℝ))
    (agreement_one_two : crossPartyAgreementProbability weight 1 2 = (1 / 4 : ℝ))
    (agreement_zero_two : crossPartyAgreementProbability weight 0 2 = (1 / 4 : ℝ)) :
    False := by
  have hbound := local_three_setting_bell_inequality
    weight weight_nonnegative weight_normalized perfect_support
  rw [agreement_zero_one, agreement_one_two, agreement_zero_two] at hbound
  norm_num at hbound

/--
Probability-only wrapper for the local contradiction: equal-setting agreement one derives the
positive-support premise used by `quarter_agreements_contradict_local_assignments`.
-/
theorem quarter_agreements_contradict_local_assignments_of_equal_setting_probability_one
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (equal_setting_probability_one :
      ∀ setting, crossPartyAgreementProbability weight setting setting = 1)
    (agreement_zero_one : crossPartyAgreementProbability weight 0 1 = (1 / 4 : ℝ))
    (agreement_one_two : crossPartyAgreementProbability weight 1 2 = (1 / 4 : ℝ))
    (agreement_zero_two : crossPartyAgreementProbability weight 0 2 = (1 / 4 : ℝ)) :
    False := by
  exact quarter_agreements_contradict_local_assignments
    weight weight_nonnegative weight_normalized
      (perfectEqualSettingSupport_of_agreementProbability_one
        weight weight_nonnegative weight_normalized equal_setting_probability_one)
      agreement_zero_one agreement_one_two agreement_zero_two

/-- Negated-model packaging of `quarter_agreements_contradict_local_assignments`. -/
theorem no_local_assignment_has_three_quarter_agreements
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1)
    (perfect_support : HasPerfectEqualSettingSupport weight) :
    ¬ (crossPartyAgreementProbability weight 0 1 = (1 / 4 : ℝ) ∧
      crossPartyAgreementProbability weight 1 2 = (1 / 4 : ℝ) ∧
        crossPartyAgreementProbability weight 0 2 = (1 / 4 : ℝ)) := by
  rintro ⟨h01, h12, h02⟩
  exact quarter_agreements_contradict_local_assignments
    weight weight_nonnegative weight_normalized perfect_support h01 h12 h02

end

end Bell
end Deutsch
