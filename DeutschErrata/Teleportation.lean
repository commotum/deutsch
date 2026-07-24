import Deutsch.Teleportation.Statistics

/-!
# Two propagated teleportation checks

The rotation orientation is visible again in the receiver effect of Equation (35) and in the
middle term of Equation (37).  This module records the two source displays locally and compares
them with the five-wire circuit derived in `Deutsch.Teleportation`.
-/

namespace DeutschErrata
namespace Teleportation

open Deutsch
open Deutsch.Foundations Deutsch.Gates Deutsch.Information Deutsch.Register
open Deutsch.Teleportation
open scoped Matrix

noncomputable section

/-! ## Equation (35) at the decisive angle -/

/--
The minus-sine receiver effect displayed in Equation (35), specialized at `theta = pi/2`.

Using the state at `-pi/2` is only a compact way to package the displayed positive rank-one
effect; the operator theorem below states its coefficients explicitly.
-/
def equation35PrintedEffectAtPiOverTwo : Effect ReceiverQubit :=
  (parameterizedReceiverDensity (-Real.pi / 2)).toEffect

theorem equation35PrintedEffectAtPiOverTwo_op :
    equation35PrintedEffectAtPiOverTwo.op =
      ((2 : Complex)⁻¹) •
        (1 - (Real.sin (Real.pi / 2) : Complex) • yAt receiverCoordinate -
          (Real.cos (Real.pi / 2) : Complex) • zAt receiverCoordinate) := by
  change (parameterizedReceiverDensity (-Real.pi / 2)).op = _
  rw [equation36_receiver_bloch_operator]
  simp [neg_div]
  module

/--
At `theta = pi/2`, the actual five-wire output accepts its derived receiver effect with
probability one, while the source's minus-sine effect is orthogonal to it.
-/
theorem equation35_endpoint_probabilities_at_pi_div_two :
    bornProbability (parameterizedTeleportedDensity (Real.pi / 2))
          (((parameterizedReceiverDensity (Real.pi / 2)).toEffect).embedSubsystem
            ({q5} : Finset TeleportQubit)) = 1 ∧
      bornProbability (parameterizedTeleportedDensity (Real.pi / 2))
          (equation35PrintedEffectAtPiOverTwo.embedSubsystem
            ({q5} : Finset TeleportQubit)) = 0 := by
  constructor
  · rw [equation36_receiver_all_effects]
    change purity (parameterizedReceiverDensity (Real.pi / 2)) = 1
    exact equation35_receiver_purity (Real.pi / 2)
  · rw [equation36_receiver_all_effects]
    change
      (Matrix.trace
        ((parameterizedReceiverDensity (Real.pi / 2)).op *
          equation35PrintedEffectAtPiOverTwo.op)).re = 0
    rw [equation36_receiver_bloch_operator,
      equation35PrintedEffectAtPiOverTwo_op]
    simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, Complex.ofReal_one,
      Complex.ofReal_zero, one_smul, zero_smul, sub_zero]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have horthogonal :
        (1 + yAt receiverCoordinate) * (1 - yAt receiverCoordinate) = 0 := by
      noncomm_ring [yAt_mul_yAt receiverCoordinate]
    rw [horthogonal]
    simp

/-! ## Equation (37) -/

/-- The plus-middle-sign operator displayed in Equation (37). -/
def equation37PrintedOperator (theta : Real) : Operator TeleportQubit :=
  ((theta.cos : Complex) * theta.cos) •
      (zAt q1 * zAt q2 * zAt q4) +
    ((theta.cos : Complex) * theta.sin) •
      (yAt q1 * zAt q2 *
        (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
    ((theta.sin : Complex) * theta.sin) •
      (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5)

private theorem neg_unitary_ne_self
    (A : Operator TeleportQubit)
    (hA : A ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex) :
    -A ≠ A := by
  intro h
  have hAA : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hA.2
  have hcancel := congrArg (fun M : Operator TeleportQubit ↦ M * Aᴴ) h
  rw [neg_mul, hAA] at hcancel
  have hentry := congrFun
    (congrFun hcancel (paperZeroAssignment TeleportQubit))
    (paperZeroAssignment TeleportQubit)
  norm_num [Matrix.one_apply] at hentry

private theorem zAt_q3_mul_zAt_q5_ne_one :
    zAt q3 * zAt q5 ≠ (1 : Operator TeleportQubit) := by
  intro h
  have hremote : xAt q3 * zAt q5 = zAt q5 * xAt q3 := by
    simpa [xAt, zAt] using
      embedQubit_commute_of_ne q3_ne_q5 pauliX pauliZ
  have hanti :
      xAt q3 * (zAt q3 * zAt q5) =
        -((zAt q3 * zAt q5) * xAt q3) := by
    calc
      xAt q3 * (zAt q3 * zAt q5) =
          (xAt q3 * zAt q3) * zAt q5 := by
            rw [Matrix.mul_assoc]
      _ = (-Complex.I • yAt q3) * zAt q5 := by
            rw [xAt_mul_zAt]
      _ = -((Complex.I • yAt q3) * zAt q5) := by
            simp only [neg_smul, Matrix.neg_mul, Matrix.smul_mul]
      _ = -((zAt q3 * xAt q3) * zAt q5) := by
            rw [zAt_mul_xAt]
      _ = -(zAt q3 * (xAt q3 * zAt q5)) := by
            rw [Matrix.mul_assoc]
      _ = -(zAt q3 * (zAt q5 * xAt q3)) := by rw [hremote]
      _ = -((zAt q3 * zAt q5) * xAt q3) := by
            rw [Matrix.mul_assoc]
  rw [h] at hanti
  simp only [Matrix.mul_one, Matrix.one_mul] at hanti
  exact neg_unitary_ne_self (xAt q3) (xAt_unitary q3) hanti.symm

private theorem equation37_middle_operator_ne_zero :
    yAt q1 * zAt q2 *
        (zAt q3 * zAt q4 * zAt q5 - zAt q4) ≠ 0 := by
  intro hzero
  have h43 : zAt q4 * zAt q3 = zAt q3 * zAt q4 := by
    simpa [zAt] using
      embedQubit_commute_of_ne q4_ne_q3 pauliZ pauliZ
  have hmove :
      zAt q3 * (zAt q4 * zAt q5) =
        zAt q4 * (zAt q3 * zAt q5) := by
    calc
      zAt q3 * (zAt q4 * zAt q5) =
          (zAt q3 * zAt q4) * zAt q5 :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (zAt q4 * zAt q3) * zAt q5 := by rw [h43]
      _ = zAt q4 * (zAt q3 * zAt q5) := Matrix.mul_assoc _ _ _
  have hfactor :
      yAt q1 * zAt q2 *
          (zAt q3 * zAt q4 * zAt q5 - zAt q4) =
        (yAt q1 * zAt q2 * zAt q4) *
          (zAt q3 * zAt q5 - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [hmove]
  rw [hfactor] at hzero
  have hU : yAt q1 * zAt q2 * zAt q4 ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
    (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        (yAt_unitary q1) (zAt_unitary q2))
      (zAt_unitary q4)
  have hUstar :
      (yAt q1 * zAt q2 * zAt q4)ᴴ *
          (yAt q1 * zAt q2 * zAt q4) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1
  have hcancel := congrArg
    (fun M : Operator TeleportQubit ↦
      (yAt q1 * zAt q2 * zAt q4)ᴴ * M)
    hzero
  rw [← Matrix.mul_assoc, hUstar, Matrix.one_mul, Matrix.mul_zero] at hcancel
  exact zAt_q3_mul_zAt_q5_ne_one (sub_eq_zero.mp hcancel)

private theorem equation37_ne_printed_of_middle_coefficient_ne_zero
    (theta : Real)
    (hcoefficient : (theta.cos : Complex) * theta.sin ≠ 0) :
    (timeFiveDescriptors theta q5).z ≠ equation37PrintedOperator theta := by
  rw [timeFive_q5_z]
  unfold equation37PrintedOperator
  intro h
  have hwithoutLast :
      ((theta.cos : Complex) * theta.cos) •
            (zAt q1 * zAt q2 * zAt q4) -
          ((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4)) =
        ((theta.cos : Complex) * theta.cos) •
            (zAt q1 * zAt q2 * zAt q4) +
          ((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4)) :=
    add_right_cancel h
  rw [sub_eq_add_neg] at hwithoutLast
  have hmiddleSign :
      -(((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4))) =
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) :=
    add_left_cancel hwithoutLast
  have htwice :
      (2 : Complex) •
          (((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4))) = 0 := by
    rw [two_smul]
    calc
      _ = -(((theta.cos : Complex) * theta.sin) •
              (yAt q1 * zAt q2 *
                (zAt q3 * zAt q4 * zAt q5 - zAt q4))) +
            ((theta.cos : Complex) * theta.sin) •
              (yAt q1 * zAt q2 *
                (zAt q3 * zAt q4 * zAt q5 - zAt q4)) := by
          exact congrArg
            (fun M : Operator TeleportQubit ↦
              M + ((theta.cos : Complex) * theta.sin) •
                (yAt q1 * zAt q2 *
                  (zAt q3 * zAt q4 * zAt q5 - zAt q4)))
            hmiddleSign.symm
      _ = 0 := neg_add_cancel _
  have hcoefficientTimesMiddle :
      ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) = 0 :=
    (smul_eq_zero.mp htwice).resolve_left (by norm_num)
  have hmiddle :
      yAt q1 * zAt q2 *
          (zAt q3 * zAt q4 * zAt q5 - zAt q4) = 0 :=
    (smul_eq_zero.mp hcoefficientTimesMiddle).resolve_left hcoefficient
  exact equation37_middle_operator_ne_zero hmiddle

/--
At `theta = pi/4`, the circuit-derived Equation (37) operator differs from the source's
plus-middle-sign display.
-/
theorem equation37_operator_ne_printed_at_pi_div_four :
    (timeFiveDescriptors (Real.pi / 4) q5).z ≠
      equation37PrintedOperator (Real.pi / 4) := by
  apply equation37_ne_printed_of_middle_coefficient_ne_zero
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hsqrt (by norm_num)))
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hsqrt (by norm_num)))

end
end Teleportation
end DeutschErrata
