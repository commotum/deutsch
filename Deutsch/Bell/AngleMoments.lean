import Deutsch.Bell.Moments

/-!
# Arbitrary-setting Bell moments

This module generalizes the finite three-setting moment contract to an arbitrary type of
measurement settings equipped with a real angle.  The probability space remains finite, but the
setting type need not be finite.  In particular, taking the setting type to be `ℝ` and the angle
map to be the identity gives the all-real-angle form of Equations (42)--(44).

Equality of the two response tables is derived only on positive-weight support.  A separate
restriction theorem turns an all-real-angle model into the existing three-setting contract used
by the finite Equation-(45)--(46) argument.
-/

namespace Deutsch
namespace Bell

noncomputable section

/-! ## Generic response values and moment reproduction -/

/-- The real zero-one value of a response at an arbitrary setting. -/
def angleResponseValue {Ω S : Type*} (response : Ω → S → Bool)
    (sample : Ω) (setting : S) : ℝ :=
  booleanIndicator (response sample setting)

/--
The EPR one-site and joint moments reproduced by two Boolean response tables on one finite
weighted space, for an arbitrary setting type with an explicit real-angle interpretation.
-/
structure ReproducesAngleEPRMoments
    {Ω S : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (angle : S → ℝ)
    (alice bob : Ω → S → Bool) : Prop where
  alice_mean :
    ∀ setting,
      space.expectation
          (fun sample => angleResponseValue alice sample setting) =
        (1 / 2 : ℝ)
  bob_mean :
    ∀ setting,
      space.expectation
          (fun sample => angleResponseValue bob sample setting) =
        (1 / 2 : ℝ)
  joint_mean :
    ∀ aliceSetting bobSetting,
      space.expectation (fun sample =>
        angleResponseValue alice sample aliceSetting *
          angleResponseValue bob sample bobSetting) =
        (1 / 2 : ℝ) *
          Real.cos
            ((angle aliceSetting - angle bobSetting) / 2) ^ 2

/-! ## Generic Equations (42)--(44) -/

/-- Equation (42) for an arbitrary setting: equal-setting responses have zero mean square. -/
theorem angleEquation42_mean_square_zero
    {Ω S : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (angle : S → ℝ)
    (alice bob : Ω → S → Bool)
    (reproduces : ReproducesAngleEPRMoments space angle alice bob)
    (setting : S) :
    space.expectation (fun sample =>
      (angleResponseValue alice sample setting -
        angleResponseValue bob sample setting) ^ 2) = 0 := by
  have expand :
      space.expectation (fun sample =>
          (angleResponseValue alice sample setting -
            angleResponseValue bob sample setting) ^ 2) =
        space.expectation
            (fun sample => angleResponseValue alice sample setting) +
          space.expectation
            (fun sample => angleResponseValue bob sample setting) -
            2 * space.expectation (fun sample =>
              angleResponseValue alice sample setting *
                angleResponseValue bob sample setting) := by
    calc
      space.expectation (fun sample =>
          (angleResponseValue alice sample setting -
            angleResponseValue bob sample setting) ^ 2) =
        space.expectation (fun sample =>
          angleResponseValue alice sample setting +
            angleResponseValue bob sample setting -
              2 * (angleResponseValue alice sample setting *
                angleResponseValue bob sample setting)) := by
            apply space.expectation_congr
            intro sample
            unfold angleResponseValue
            rw [sub_sq, booleanIndicator_sq, booleanIndicator_sq]
            ring
      _ =
        space.expectation
            (fun sample => angleResponseValue alice sample setting) +
          space.expectation
            (fun sample => angleResponseValue bob sample setting) -
            space.expectation (fun sample =>
              2 * (angleResponseValue alice sample setting *
                angleResponseValue bob sample setting)) := by
              rw [space.expectation_sub, space.expectation_add]
      _ =
        space.expectation
            (fun sample => angleResponseValue alice sample setting) +
          space.expectation
            (fun sample => angleResponseValue bob sample setting) -
            2 * space.expectation (fun sample =>
              angleResponseValue alice sample setting *
                angleResponseValue bob sample setting) := by
              rw [space.expectation_const_mul]
  rw [expand, reproduces.alice_mean, reproduces.bob_mean,
    reproduces.joint_mean]
  norm_num

/--
Equation (43) for an arbitrary setting: equal-setting responses agree at every positive-weight
sample.  No conclusion is made about samples of weight zero.
-/
theorem angleEquation43_equal_on_positive_support
    {Ω S : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (angle : S → ℝ)
    (alice bob : Ω → S → Bool)
    (reproduces : ReproducesAngleEPRMoments space angle alice bob)
    {sample : Ω} (samplePositive : 0 < space.weight sample)
    (setting : S) :
    bob sample setting = alice sample setting := by
  have squareZero :
      (angleResponseValue alice sample setting -
        angleResponseValue bob sample setting) ^ 2 = 0 :=
    space.eq_zero_on_positive_support
      (fun candidate =>
        (angleResponseValue alice candidate setting -
          angleResponseValue bob candidate setting) ^ 2)
      (fun candidate => sq_nonneg _)
      (angleEquation42_mean_square_zero
        space angle alice bob reproduces setting)
      samplePositive
  have valuesEqual :
      angleResponseValue alice sample setting =
        angleResponseValue bob sample setting := by
    have differenceZero :
        angleResponseValue alice sample setting -
          angleResponseValue bob sample setting = 0 :=
      (sq_eq_zero_iff).mp squareZero
    exact sub_eq_zero.mp differenceZero
  exact (booleanIndicator_injective valuesEqual).symm

/--
Equation (44) for arbitrary settings: replacing Bob's second response by Alice's equal response
preserves the joint moment on the common finite weighted space.
-/
theorem angleEquation44_alice_joint_moment
    {Ω S : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (angle : S → ℝ)
    (alice bob : Ω → S → Bool)
    (reproduces : ReproducesAngleEPRMoments space angle alice bob)
    (setting₀ setting₁ : S) :
    space.expectation (fun sample =>
      angleResponseValue alice sample setting₀ *
        angleResponseValue alice sample setting₁) =
      (1 / 2 : ℝ) *
        Real.cos ((angle setting₀ - angle setting₁) / 2) ^ 2 := by
  calc
    space.expectation (fun sample =>
        angleResponseValue alice sample setting₀ *
          angleResponseValue alice sample setting₁) =
      space.expectation (fun sample =>
        angleResponseValue alice sample setting₀ *
          angleResponseValue bob sample setting₁) := by
            apply space.expectation_congr_on_positive_support
            intro sample weightPositive
            have responsesEqual :
                alice sample setting₁ = bob sample setting₁ :=
              (angleEquation43_equal_on_positive_support
                space angle alice bob reproduces weightPositive setting₁).symm
            unfold angleResponseValue
            rw [responsesEqual]
    _ =
      (1 / 2 : ℝ) *
        Real.cos ((angle setting₀ - angle setting₁) / 2) ^ 2 :=
      reproduces.joint_mean setting₀ setting₁

/-! ## Restriction from all real angles to the three Bell settings -/

/--
An all-real-angle reproducing model restricts along `threeSettingAngle` to the existing
three-setting moment contract used by Equations (45)--(46).
-/
theorem restrictRealAngleMomentsToThreeSettings
    {Ω : Type*} [Fintype Ω]
    (space : FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces :
      ReproducesAngleEPRMoments space (fun theta : ℝ => theta) alice bob) :
    ReproducesThreeSettingEPRMoments space
      (fun sample setting => alice sample (threeSettingAngle setting))
      (fun sample setting => bob sample (threeSettingAngle setting)) where
  alice_mean setting := by
    simpa [aliceValue, angleResponseValue] using
      reproduces.alice_mean (threeSettingAngle setting)
  bob_mean setting := by
    simpa [bobValue, angleResponseValue] using
      reproduces.bob_mean (threeSettingAngle setting)
  joint_mean aliceSetting bobSetting := by
    simpa [aliceValue, bobValue, angleResponseValue, eprJointMoment] using
      reproduces.joint_mean
        (threeSettingAngle aliceSetting)
        (threeSettingAngle bobSetting)

end
end Bell
end Deutsch
