import Deutsch.Bell.Quantum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite weighted Bell moments

This module formalizes the three-setting expectation argument on a finite probability space.
Boolean response tables are represented by real zero-one indicators.  The only probabilistic
assumptions are nonnegative normalized weights and the explicitly stated one- and two-response
moments.

The derivation follows Equations (42)--(46) directly.  It is independent of the finite pigeonhole
inequality in `Deutsch.Bell.Finite`.
-/

namespace Deutsch
namespace Bell

open scoped BigOperators

noncomputable section

/-! ## Finite real probability spaces and Boolean indicators -/

/-- A nonnegative normalized real weight on a finite sample type. -/
structure FiniteProbabilityWeight (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ sample, 0 ≤ weight sample
  normalized : ∑ sample, weight sample = 1

namespace FiniteProbabilityWeight

variable {Ω : Type*} [Fintype Ω]

/-- Weighted expectation of a real random variable. -/
def expectation (space : FiniteProbabilityWeight Ω) (value : Ω → ℝ) : ℝ :=
  ∑ sample, space.weight sample * value sample

theorem expectation_congr (space : FiniteProbabilityWeight Ω)
    {value₁ value₂ : Ω → ℝ} (h : ∀ sample, value₁ sample = value₂ sample) :
    space.expectation value₁ = space.expectation value₂ := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro sample _
  rw [h sample]

/--
Weighted expectations agree when their integrands agree on positive-weight support.  Values at
zero-weight samples may differ.
-/
theorem expectation_congr_on_positive_support
    (space : FiniteProbabilityWeight Ω)
    {value₁ value₂ : Ω → ℝ}
    (h : ∀ sample, 0 < space.weight sample → value₁ sample = value₂ sample) :
    space.expectation value₁ = space.expectation value₂ := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro sample _
  by_cases weight_zero : space.weight sample = 0
  · simp [weight_zero]
  · have weight_positive : 0 < space.weight sample :=
      lt_of_le_of_ne (space.nonnegative sample) (Ne.symm weight_zero)
    rw [h sample weight_positive]

theorem expectation_add (space : FiniteProbabilityWeight Ω)
    (value₁ value₂ : Ω → ℝ) :
    space.expectation (fun sample => value₁ sample + value₂ sample) =
      space.expectation value₁ + space.expectation value₂ := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (space : FiniteProbabilityWeight Ω)
    (value₁ value₂ : Ω → ℝ) :
    space.expectation (fun sample => value₁ sample - value₂ sample) =
      space.expectation value₁ - space.expectation value₂ := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_const_mul (space : FiniteProbabilityWeight Ω)
    (constant : ℝ) (value : Ω → ℝ) :
    space.expectation (fun sample => constant * value sample) =
      constant * space.expectation value := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  ring

@[simp]
theorem expectation_one (space : FiniteProbabilityWeight Ω) :
    space.expectation (fun _ => 1) = 1 := by
  simpa [expectation] using space.normalized

theorem expectation_mono (space : FiniteProbabilityWeight Ω)
    {value₁ value₂ : Ω → ℝ} (h : ∀ sample, value₁ sample ≤ value₂ sample) :
    space.expectation value₁ ≤ space.expectation value₂ := by
  unfold expectation
  exact Finset.sum_le_sum fun sample _ =>
    mul_le_mul_of_nonneg_left (h sample) (space.nonnegative sample)

/--
A nonnegative random variable with zero weighted expectation vanishes at every positive-weight
sample.  Nothing is asserted at zero-weight samples.
-/
theorem eq_zero_on_positive_support (space : FiniteProbabilityWeight Ω)
    (value : Ω → ℝ) (value_nonnegative : ∀ sample, 0 ≤ value sample)
    (expectation_zero : space.expectation value = 0)
    {sample : Ω} (sample_positive : 0 < space.weight sample) :
    value sample = 0 := by
  have term_nonnegative :
      ∀ candidate, 0 ≤ space.weight candidate * value candidate :=
    fun candidate =>
      mul_nonneg (space.nonnegative candidate) (value_nonnegative candidate)
  have term_le_sum :
      space.weight sample * value sample ≤
        ∑ candidate, space.weight candidate * value candidate :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate => space.weight candidate * value candidate)
      (fun candidate _ => term_nonnegative candidate)
      (Finset.mem_univ sample)
  rw [← expectation, expectation_zero] at term_le_sum
  have term_zero : space.weight sample * value sample = 0 :=
    le_antisymm term_le_sum (term_nonnegative sample)
  rcases mul_eq_zero.mp term_zero with weight_zero | value_zero
  · exact (ne_of_gt sample_positive weight_zero).elim
  · exact value_zero

end FiniteProbabilityWeight

/-- Real zero-one value of a Boolean response. -/
def booleanIndicator : Bool → ℝ
  | false => 0
  | true => 1

@[simp] theorem booleanIndicator_false : booleanIndicator false = 0 := rfl

@[simp] theorem booleanIndicator_true : booleanIndicator true = 1 := rfl

theorem booleanIndicator_nonnegative (value : Bool) :
    0 ≤ booleanIndicator value := by
  cases value <;> norm_num

theorem booleanIndicator_le_one (value : Bool) :
    booleanIndicator value ≤ 1 := by
  cases value <;> norm_num

@[simp]
theorem booleanIndicator_sq (value : Bool) :
    booleanIndicator value ^ 2 = booleanIndicator value := by
  cases value <;> norm_num

theorem booleanIndicator_injective :
    Function.Injective booleanIndicator := by
  intro left right h
  cases left <;> cases right <;> simp_all

/-- Real indicator of Boolean disjunction. -/
def disjunctionIndicator (left right : Bool) : ℝ :=
  booleanIndicator (left || right)

/-- Real indicator of the event complementary to a Boolean disjunction. -/
def complementaryDisjunctionIndicator (left right : Bool) : ℝ :=
  booleanIndicator (!(left || right))

theorem disjunctionIndicator_eq (left right : Bool) :
    disjunctionIndicator left right =
      booleanIndicator left + booleanIndicator right -
        booleanIndicator left * booleanIndicator right := by
  cases left <;> cases right <;> norm_num [disjunctionIndicator]

theorem complementaryDisjunctionIndicator_eq (left right : Bool) :
    complementaryDisjunctionIndicator left right =
      1 - booleanIndicator left - booleanIndicator right +
        booleanIndicator left * booleanIndicator right := by
  cases left <;> cases right <;>
    norm_num [complementaryDisjunctionIndicator]

theorem disjunction_complement_partition (left right : Bool) :
    disjunctionIndicator left right +
      complementaryDisjunctionIndicator left right = 1 := by
  cases left <;> cases right <;>
    norm_num [disjunctionIndicator, complementaryDisjunctionIndicator]

theorem complementaryDisjunctionIndicator_eq_one_sub (left right : Bool) :
    complementaryDisjunctionIndicator left right =
      1 - disjunctionIndicator left right := by
  cases left <;> cases right <;>
    norm_num [disjunctionIndicator, complementaryDisjunctionIndicator]

theorem complementaryDisjunctionIndicator_nonnegative (left right : Bool) :
    0 ≤ complementaryDisjunctionIndicator left right :=
  booleanIndicator_nonnegative _

/-! ## The three-setting EPR moment contract -/

/-- Alice's real zero-one response at one sample and setting. -/
def aliceValue {Ω : Type*} (alice : Ω → Fin 3 → Bool)
    (sample : Ω) (setting : Fin 3) : ℝ :=
  booleanIndicator (alice sample setting)

/-- Bob's real zero-one response at one sample and setting. -/
def bobValue {Ω : Type*} (bob : Ω → Fin 3 → Bool)
    (sample : Ω) (setting : Fin 3) : ℝ :=
  booleanIndicator (bob sample setting)

/-- The joint moment supplied by the EPR calculation for the three named settings. -/
def eprJointMoment (aliceSetting bobSetting : Fin 3) : ℝ :=
  (1 / 2 : ℝ) *
    Real.cos
      ((threeSettingAngle aliceSetting - threeSettingAngle bobSetting) / 2) ^ 2

@[simp]
theorem eprJointMoment_self (setting : Fin 3) :
    eprJointMoment setting setting = (1 / 2 : ℝ) := by
  simp [eprJointMoment]

theorem eprJointMoment_zero_one :
    eprJointMoment 0 1 = (1 / 8 : ℝ) := by
  rw [eprJointMoment, threeSettingAngle_zero, threeSettingAngle_one,
    cos_half_settingZero_sub_settingOne]
  norm_num

theorem eprJointMoment_zero_two :
    eprJointMoment 0 2 = (1 / 8 : ℝ) := by
  rw [eprJointMoment, threeSettingAngle_zero, threeSettingAngle_two,
    cos_half_settingZero_sub_settingTwo]
  norm_num

theorem eprJointMoment_one_two :
    eprJointMoment 1 2 = (1 / 8 : ℝ) := by
  rw [eprJointMoment, threeSettingAngle_one, threeSettingAngle_two,
    cos_half_settingOne_sub_settingTwo]
  norm_num

/--
The source's Equations (40) and (41), stated as moments of two local Boolean response tables on one
finite weighted space.
-/
structure ReproducesThreeSettingEPRMoments
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool) : Prop where
  alice_mean :
    ∀ setting,
      space.expectation (fun sample => aliceValue alice sample setting) = (1 / 2 : ℝ)
  bob_mean :
    ∀ setting,
      space.expectation (fun sample => bobValue bob sample setting) = (1 / 2 : ℝ)
  joint_mean :
    ∀ aliceSetting bobSetting,
      space.expectation (fun sample =>
        aliceValue alice sample aliceSetting *
          bobValue bob sample bobSetting) =
        eprJointMoment aliceSetting bobSetting

/-! ## Equations (42)--(44) -/

/-- Equation (42): equal-setting responses have zero mean squared difference. -/
theorem equation42_mean_square_zero
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    (setting : Fin 3) :
    space.expectation (fun sample =>
      (aliceValue alice sample setting - bobValue bob sample setting) ^ 2) = 0 := by
  have expand :
      space.expectation (fun sample =>
          (aliceValue alice sample setting - bobValue bob sample setting) ^ 2) =
        space.expectation (fun sample => aliceValue alice sample setting) +
          space.expectation (fun sample => bobValue bob sample setting) -
            2 * space.expectation (fun sample =>
              aliceValue alice sample setting * bobValue bob sample setting) := by
    calc
      space.expectation (fun sample =>
          (aliceValue alice sample setting -
            bobValue bob sample setting) ^ 2) =
        space.expectation (fun sample =>
          aliceValue alice sample setting +
            bobValue bob sample setting -
              2 * (aliceValue alice sample setting *
                bobValue bob sample setting)) := by
            apply space.expectation_congr
            intro sample
            unfold aliceValue bobValue
            rw [sub_sq, booleanIndicator_sq, booleanIndicator_sq]
            ring
      _ = space.expectation (fun sample => aliceValue alice sample setting) +
          space.expectation (fun sample => bobValue bob sample setting) -
            space.expectation (fun sample =>
              2 * (aliceValue alice sample setting *
                bobValue bob sample setting)) := by
            rw [space.expectation_sub, space.expectation_add]
      _ = space.expectation (fun sample => aliceValue alice sample setting) +
          space.expectation (fun sample => bobValue bob sample setting) -
            2 * space.expectation (fun sample =>
              aliceValue alice sample setting * bobValue bob sample setting) := by
            rw [space.expectation_const_mul]
  rw [expand, reproduces.alice_mean, reproduces.bob_mean,
    reproduces.joint_mean, eprJointMoment_self]
  norm_num

/--
Equation (43): at every positive-weight sample, equal settings give equal Boolean responses.
Zero-weight samples are deliberately unconstrained.
-/
theorem equation43_equal_on_positive_support
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    {sample : Ω} (sample_positive : 0 < space.weight sample)
    (setting : Fin 3) :
    bob sample setting = alice sample setting := by
  have square_zero :
      (aliceValue alice sample setting - bobValue bob sample setting) ^ 2 = 0 :=
    space.eq_zero_on_positive_support
      (fun candidate =>
        (aliceValue alice candidate setting -
          bobValue bob candidate setting) ^ 2)
      (fun candidate => sq_nonneg _)
      (equation42_mean_square_zero space alice bob reproduces setting)
      sample_positive
  have values_equal :
      aliceValue alice sample setting = bobValue bob sample setting := by
    have difference_zero :
        aliceValue alice sample setting - bobValue bob sample setting = 0 :=
      (sq_eq_zero_iff).mp square_zero
    exact sub_eq_zero.mp difference_zero
  exact (booleanIndicator_injective values_equal).symm

/-- Equation (44): the counterfactual Alice--Alice moment follows on the common finite space. -/
theorem equation44_alice_joint_moment
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob)
    (setting₀ setting₁ : Fin 3) :
    space.expectation (fun sample =>
      aliceValue alice sample setting₀ * aliceValue alice sample setting₁) =
        eprJointMoment setting₀ setting₁ := by
  calc
    space.expectation (fun sample =>
        aliceValue alice sample setting₀ * aliceValue alice sample setting₁) =
      space.expectation (fun sample =>
        aliceValue alice sample setting₀ * bobValue bob sample setting₁) := by
          apply space.expectation_congr_on_positive_support
          intro sample weight_positive
          have responses_equal :
              alice sample setting₁ = bob sample setting₁ :=
            (equation43_equal_on_positive_support
              space alice bob reproduces weight_positive setting₁).symm
          unfold aliceValue bobValue
          rw [responses_equal]
    _ = eprJointMoment setting₀ setting₁ :=
      reproduces.joint_mean setting₀ setting₁

/-! ## Equations (45)--(46) -/

/-- Multiplication by a Boolean event and its actual complement partitions `a₀`. -/
theorem boolean_disjunction_complement_partition (a₀ a₁ a₂ : Bool) :
    booleanIndicator a₀ =
      booleanIndicator a₀ * disjunctionIndicator a₁ a₂ +
        booleanIndicator a₀ * complementaryDisjunctionIndicator a₁ a₂ := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;>
    norm_num [disjunctionIndicator, complementaryDisjunctionIndicator]

/--
Equation (45), in its displayed real-arithmetic form.  The parenthesized second factor is the
indicator of the event complementary to the disjunction.
-/
theorem equation45_complementary_partition (a₀ a₁ a₂ : Bool) :
    booleanIndicator a₀ =
      booleanIndicator a₀ * disjunctionIndicator a₁ a₂ +
        booleanIndicator a₀ * (1 - disjunctionIndicator a₁ a₂) := by
  rw [← complementaryDisjunctionIndicator_eq_one_sub]
  exact boolean_disjunction_complement_partition a₀ a₁ a₂

/-- Averaged form of Equation (45), ready for the first line of Equation (46). -/
theorem equation45_expectation_partition
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (a₀ a₁ a₂ : Ω → Bool) :
    space.expectation (fun sample => booleanIndicator (a₀ sample)) =
      space.expectation (fun sample =>
        booleanIndicator (a₀ sample) *
          disjunctionIndicator (a₁ sample) (a₂ sample)) +
      space.expectation (fun sample =>
        booleanIndicator (a₀ sample) *
          complementaryDisjunctionIndicator (a₁ sample) (a₂ sample)) := by
  rw [← space.expectation_add]
  exact space.expectation_congr fun sample =>
    boolean_disjunction_complement_partition
      (a₀ sample) (a₁ sample) (a₂ sample)

/-- Linear expansion used in the middle of Equation (46). -/
theorem expectation_disjunction_expansion
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (value₀ value₁ value₂ : Ω → ℝ) :
    space.expectation (fun sample =>
        value₀ sample *
          (value₁ sample + value₂ sample - value₁ sample * value₂ sample)) +
      space.expectation (fun sample =>
        1 - value₁ sample - value₂ sample + value₁ sample * value₂ sample) =
      (space.expectation (fun sample => value₀ sample * value₁ sample) +
          space.expectation (fun sample => value₀ sample * value₂ sample) -
            space.expectation (fun sample =>
              value₀ sample * value₁ sample * value₂ sample)) +
        (1 - space.expectation value₁ - space.expectation value₂ +
          space.expectation (fun sample => value₁ sample * value₂ sample)) := by
  have first_expansion :
      space.expectation (fun sample =>
          value₀ sample *
            (value₁ sample + value₂ sample -
              value₁ sample * value₂ sample)) =
        space.expectation (fun sample => value₀ sample * value₁ sample) +
          space.expectation (fun sample => value₀ sample * value₂ sample) -
            space.expectation (fun sample =>
              value₀ sample * value₁ sample * value₂ sample) := by
    calc
      space.expectation (fun sample =>
          value₀ sample *
            (value₁ sample + value₂ sample -
              value₁ sample * value₂ sample)) =
        space.expectation (fun sample =>
          value₀ sample * value₁ sample +
            value₀ sample * value₂ sample -
              value₀ sample * value₁ sample * value₂ sample) := by
                apply space.expectation_congr
                intro sample
                ring
      _ = space.expectation (fun sample => value₀ sample * value₁ sample) +
          space.expectation (fun sample => value₀ sample * value₂ sample) -
            space.expectation (fun sample =>
              value₀ sample * value₁ sample * value₂ sample) := by
              rw [space.expectation_sub, space.expectation_add]
  have complement_expansion :
      space.expectation (fun sample =>
          1 - value₁ sample - value₂ sample + value₁ sample * value₂ sample) =
        1 - space.expectation value₁ - space.expectation value₂ +
          space.expectation (fun sample => value₁ sample * value₂ sample) := by
    calc
      space.expectation (fun sample =>
          1 - value₁ sample - value₂ sample + value₁ sample * value₂ sample) =
        space.expectation (fun sample => 1 - value₁ sample - value₂ sample) +
          space.expectation (fun sample => value₁ sample * value₂ sample) := by
            rw [space.expectation_add]
      _ = (space.expectation (fun _ => 1) - space.expectation value₁ -
          space.expectation value₂) +
            space.expectation (fun sample => value₁ sample * value₂ sample) := by
              rw [space.expectation_sub, space.expectation_sub]
      _ = 1 - space.expectation value₁ - space.expectation value₂ +
          space.expectation (fun sample => value₁ sample * value₂ sample) := by
            rw [space.expectation_one]
  rw [first_expansion, complement_expansion]

/-- The two complementary terms in the first line of Equation (46). -/
def equation46PartitionedMean
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) : ℝ :=
  space.expectation (fun sample =>
      aliceValue alice sample 0 *
        disjunctionIndicator (alice sample 1) (alice sample 2)) +
    space.expectation (fun sample =>
      aliceValue alice sample 0 *
        complementaryDisjunctionIndicator (alice sample 1) (alice sample 2))

/-- The arithmetic disjunction and complement bound in the second line of Equation (46). -/
def equation46ExpandedMean
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) : ℝ :=
  space.expectation (fun sample =>
      aliceValue alice sample 0 *
        (aliceValue alice sample 1 + aliceValue alice sample 2 -
          aliceValue alice sample 1 * aliceValue alice sample 2)) +
    space.expectation (fun sample =>
      1 - aliceValue alice sample 1 - aliceValue alice sample 2 +
        aliceValue alice sample 1 * aliceValue alice sample 2)

/-- The nonnegative triple-response moment subtracted in the last two lines of Equation (46). -/
def equation46TripleMean
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) : ℝ :=
  space.expectation (fun sample =>
    aliceValue alice sample 0 *
      aliceValue alice sample 1 *
        aliceValue alice sample 2)

/-- First line of Equation (46): Equation (45) and the `a(0)` marginal give one half. -/
theorem equation46_first_equality
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) = equation46PartitionedMean space alice := by
  calc
    (1 / 2 : ℝ) =
        space.expectation (fun sample => aliceValue alice sample 0) :=
      (reproduces.alice_mean 0).symm
    _ = equation46PartitionedMean space alice := by
      simpa [equation46PartitionedMean, aliceValue] using
        equation45_expectation_partition space
          (fun sample => alice sample 0)
          (fun sample => alice sample 1)
          (fun sample => alice sample 2)

/--
First inequality of Equation (46): the disjunction is expanded exactly, while multiplication of
its complementary indicator by `a(0)` can only decrease it.
-/
theorem equation46_first_inequality
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) :
    equation46PartitionedMean space alice ≤
      equation46ExpandedMean space alice := by
  have disjunction_term :
      space.expectation (fun sample =>
          aliceValue alice sample 0 *
            disjunctionIndicator (alice sample 1) (alice sample 2)) =
        space.expectation (fun sample =>
          aliceValue alice sample 0 *
            (aliceValue alice sample 1 + aliceValue alice sample 2 -
              aliceValue alice sample 1 * aliceValue alice sample 2)) := by
    apply space.expectation_congr
    intro sample
    rw [disjunctionIndicator_eq]
    rfl
  have complement_term :
      space.expectation (fun sample =>
          aliceValue alice sample 0 *
            complementaryDisjunctionIndicator
              (alice sample 1) (alice sample 2)) ≤
        space.expectation (fun sample =>
          1 - aliceValue alice sample 1 - aliceValue alice sample 2 +
            aliceValue alice sample 1 * aliceValue alice sample 2) := by
    apply space.expectation_mono
    intro sample
    rw [show
      1 - aliceValue alice sample 1 - aliceValue alice sample 2 +
          aliceValue alice sample 1 * aliceValue alice sample 2 =
        complementaryDisjunctionIndicator
          (alice sample 1) (alice sample 2) by
      symm
      exact complementaryDisjunctionIndicator_eq
        (alice sample 1) (alice sample 2)]
    exact mul_le_of_le_one_left
      (complementaryDisjunctionIndicator_nonnegative
        (alice sample 1) (alice sample 2))
      (booleanIndicator_le_one (alice sample 0))
  unfold equation46PartitionedMean equation46ExpandedMean
  rw [disjunction_term]
  exact add_le_add (le_refl _) complement_term

/-- Exact moment evaluation underlying the second inequality in Equation (46). -/
theorem equation46_expanded_mean
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    equation46ExpandedMean space alice =
      (3 / 8 : ℝ) - equation46TripleMean space alice := by
  rw [equation46ExpandedMean, equation46TripleMean,
    expectation_disjunction_expansion]
  rw [equation44_alice_joint_moment space alice bob reproduces 0 1,
    equation44_alice_joint_moment space alice bob reproduces 0 2,
    equation44_alice_joint_moment space alice bob reproduces 1 2,
    reproduces.alice_mean 1, reproduces.alice_mean 2,
    eprJointMoment_zero_one, eprJointMoment_zero_two,
    eprJointMoment_one_two]
  ring

/-- Second inequality in Equation (46), with its exact moment evaluation exposed separately. -/
theorem equation46_second_inequality
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    equation46ExpandedMean space alice ≤
      (3 / 8 : ℝ) - equation46TripleMean space alice :=
  (equation46_expanded_mean space alice bob reproduces).le

/-- The triple Boolean product, and hence its weighted mean, is nonnegative. -/
theorem equation46_triple_mean_nonnegative
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) :
    0 ≤ equation46TripleMean space alice := by
  unfold equation46TripleMean FiniteProbabilityWeight.expectation
  apply Finset.sum_nonneg
  intro sample _
  exact mul_nonneg (space.nonnegative sample)
    (mul_nonneg
      (mul_nonneg
        (booleanIndicator_nonnegative (alice sample 0))
        (booleanIndicator_nonnegative (alice sample 1)))
      (booleanIndicator_nonnegative (alice sample 2)))

/-- Last inequality in Equation (46), from nonnegativity of the triple product. -/
theorem equation46_third_inequality
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice : Ω → Fin 3 → Bool) :
    (3 / 8 : ℝ) - equation46TripleMean space alice ≤ (3 / 8 : ℝ) :=
  sub_le_self _ (equation46_triple_mean_nonnegative space alice)

/--
All displayed comparisons in Equation (46), packaged without replacing any line by the separate
pigeonhole argument.
-/
theorem equation46_chain
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) = equation46PartitionedMean space alice ∧
      equation46PartitionedMean space alice ≤ equation46ExpandedMean space alice ∧
      equation46ExpandedMean space alice ≤
        (3 / 8 : ℝ) - equation46TripleMean space alice ∧
      (3 / 8 : ℝ) - equation46TripleMean space alice ≤ (3 / 8 : ℝ) := by
  exact ⟨
    equation46_first_equality space alice bob reproduces,
    equation46_first_inequality space alice,
    equation46_second_inequality space alice bob reproduces,
    equation46_third_inequality space alice⟩

/-- The numerical endpoint of Equation (46): the assumptions force `1/2 ≤ 3/8`. -/
theorem equation46_impossible_bound
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) ≤ (3 / 8 : ℝ) := by
  rcases equation46_chain space alice bob reproduces with
    ⟨first_equality, first_inequality, second_inequality, third_inequality⟩
  calc
    (1 / 2 : ℝ) = equation46PartitionedMean space alice := first_equality
    _ ≤ equation46ExpandedMean space alice := first_inequality
    _ ≤ (3 / 8 : ℝ) - equation46TripleMean space alice := second_inequality
    _ ≤ (3 / 8 : ℝ) := third_inequality

/-- The Equation (46) chain yields the displayed impossibility `1/2 ≤ 3/8`. -/
theorem equation46_contradiction
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : ReproducesThreeSettingEPRMoments space alice bob) :
    False := by
  have impossible := equation46_impossible_bound space alice bob reproduces
  norm_num at impossible

end
end Bell
end Deutsch
