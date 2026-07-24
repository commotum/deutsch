import Deutsch.Gates.OneQubit
import Deutsch.Gates.CNOT
import Deutsch.Locality.Heisenberg
import Mathlib.Tactic.FinCases

/-!
# Bell transform on named registers

Fig. 1 is read with time upward: CNOT acts first with the left wire as target and the
right wire as control, then Hadamard acts on the right/control wire. Matrix multiplication
therefore gives `bellAt = hadamardAt control * cnotAt target control h`; the inverse reverses
that order. The module proves both inverse laws, unitarity, pair-support witnesses and basis amplitudes,
and all twelve Pauli-component identities in Equations (20)--(21).
-/

namespace Deutsch
namespace Gates

open Foundations Register
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Fig. 1, time upward: CNOT first, then Hadamard on the right/control wire. -/
def bellAt (target control : Q) (h : target ≠ control) : Operator Q :=
  hadamardAt control * cnotAt target control h

/-- Fig. 1 upside down: Hadamard first, then CNOT. -/
def bellInverseAt (target control : Q) (h : target ≠ control) : Operator Q :=
  cnotAt target control h * hadamardAt control

theorem bellAt_unitary (target control : Q) (h : target ≠ control) :
    bellAt target control h ∈ Matrix.unitaryGroup (Basis Q) Complex := by
  exact (Matrix.unitaryGroup (Basis Q) Complex).mul_mem
    (hadamardAt_unitary control) (cnotAt_unitary target control h)

theorem bellInverseAt_unitary (target control : Q) (h : target ≠ control) :
    bellInverseAt target control h ∈
      Matrix.unitaryGroup (Basis Q) Complex := by
  exact (Matrix.unitaryGroup (Basis Q) Complex).mul_mem
    (cnotAt_unitary target control h) (hadamardAt_unitary control)

theorem bellAt_inverse_left (target control : Q) (h : target ≠ control) :
    bellInverseAt target control h * bellAt target control h = 1 := by
  simp only [bellInverseAt, bellAt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hadamardAt control) (hadamardAt control)
      (cnotAt target control h), hadamardAt_mul_self]
  simpa using cnotAt_mul_self target control h

theorem bellAt_inverse_right (target control : Q) (h : target ≠ control) :
    bellAt target control h * bellInverseAt target control h = 1 := by
  simp only [bellInverseAt, bellAt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cnotAt target control h) (cnotAt target control h)
      (hadamardAt control), cnotAt_mul_self]
  simpa using hadamardAt_mul_self control

theorem hadamardAt_heisenberg_remote (q r : Q) (hqr : q ≠ r)
    (A : QubitMatrix) :
    heisenberg (hadamardAt r) (embedQubit q A) = embedQubit q A := by
  have hcomm :
      hadamardAt r * embedQubit q A = embedQubit q A * hadamardAt r := by
    exact embedQubit_commute_of_ne hqr.symm hadamard A
  have hunit := hadamardAt_unitary r
  have hisometry : (hadamardAt r)ᴴ * hadamardAt r = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hunit.1
  exact Locality.heisenberg_eq_self_of_commute_of_isometry
    (hadamardAt r) (embedQubit q A) hcomm hisometry

theorem hadamardAt_heisenberg_remote_x
    (target control : Q) (h : target ≠ control) :
    heisenberg (hadamardAt control) (xAt target) = xAt target := by
  exact hadamardAt_heisenberg_remote target control h pauliX

theorem hadamardAt_heisenberg_remote_y
    (target control : Q) (h : target ≠ control) :
    heisenberg (hadamardAt control) (yAt target) = yAt target := by
  exact hadamardAt_heisenberg_remote target control h pauliY

theorem hadamardAt_heisenberg_remote_z
    (target control : Q) (h : target ≠ control) :
    heisenberg (hadamardAt control) (zAt target) = zAt target := by
  exact hadamardAt_heisenberg_remote target control h pauliZ

theorem heisenberg_neg (U A : Operator Q) :
    heisenberg U (-A) = -heisenberg U A := by
  simpa only [neg_one_smul] using heisenberg_smul U A (-1)

/-! Equation (20), all six named-register components. -/

theorem bellAt_conjugates_target_x (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (xAt target) = xAt target := by
  rw [bellAt, heisenberg_chronology,
    hadamardAt_heisenberg_remote_x target control h,
    cnotAt_conjugates_target_x]

theorem bellAt_conjugates_target_y (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (yAt target) =
      -(yAt target * zAt control) := by
  rw [bellAt, heisenberg_chronology,
    hadamardAt_heisenberg_remote_y target control h,
    cnotAt_conjugates_target_y]

theorem bellAt_conjugates_target_z (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (zAt target) =
      -(zAt target * zAt control) := by
  rw [bellAt, heisenberg_chronology,
    hadamardAt_heisenberg_remote_z target control h,
    cnotAt_conjugates_target_z]

theorem bellAt_conjugates_control_x (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (xAt control) = zAt control := by
  rw [bellAt, heisenberg_chronology, hadamardAt_heisenberg_x,
    cnotAt_conjugates_control_z]

theorem bellAt_conjugates_control_y (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (yAt control) =
      -(xAt target * yAt control) := by
  rw [bellAt, heisenberg_chronology, hadamardAt_heisenberg_y,
    heisenberg_neg, cnotAt_conjugates_control_y]

theorem bellAt_conjugates_control_z (target control : Q) (h : target ≠ control) :
    heisenberg (bellAt target control h) (zAt control) =
      xAt target * xAt control := by
  rw [bellAt, heisenberg_chronology, hadamardAt_heisenberg_z,
    cnotAt_conjugates_control_x]

/-! Equation (21), all six named-register components. -/

theorem bellInverseAt_conjugates_target_x
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (xAt target) = xAt target := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_target_x,
    hadamardAt_heisenberg_remote_x target control h]

theorem bellInverseAt_conjugates_target_y
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (yAt target) =
      -(yAt target * xAt control) := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_target_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary control),
    hadamardAt_heisenberg_remote_y target control h,
    hadamardAt_heisenberg_z]

theorem bellInverseAt_conjugates_target_z
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (zAt target) =
      -(zAt target * xAt control) := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_target_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary control),
    hadamardAt_heisenberg_remote_z target control h,
    hadamardAt_heisenberg_z]

theorem bellInverseAt_conjugates_control_x
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (xAt control) =
      xAt target * zAt control := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_control_x,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary control),
    hadamardAt_heisenberg_remote_x target control h,
    hadamardAt_heisenberg_x]

theorem bellInverseAt_conjugates_control_y
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (yAt control) =
      -(xAt target * yAt control) := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_control_y,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary control),
    hadamardAt_heisenberg_remote_x target control h,
    hadamardAt_heisenberg_y]
  rw [Matrix.mul_neg]

theorem bellInverseAt_conjugates_control_z
    (target control : Q) (h : target ≠ control) :
    heisenberg (bellInverseAt target control h) (zAt control) = xAt control := by
  rw [bellInverseAt, heisenberg_chronology,
    cnotAt_conjugates_control_z, hadamardAt_heisenberg_z]

theorem hadamardAt_isSupportedOn_pair
    (target control : Q) (h : target ≠ control) :
    IsSupportedOn {target, control} (hadamardAt control) := by
  let p := targetControlPlacement target control h
  have hs := embedAlong_isSupportedOn p (hadamardAt (1 : Fin 2))
  rw [show placementFinset p = {target, control} by
    exact placementFinset_targetControl target control h] at hs
  have heq : embedAlong p (hadamardAt (1 : Fin 2)) = hadamardAt control := by
    unfold hadamardAt
    rw [embedAlong_embedQubit]
    rfl
  rw [heq] at hs
  exact hs

theorem bellAt_isSupportedOn (target control : Q) (h : target ≠ control) :
    IsSupportedOn {target, control} (bellAt target control h) := by
  exact (hadamardAt_isSupportedOn_pair target control h).mul
    (cnotAt_isSupportedOn_pair target control h)

theorem bellInverseAt_isSupportedOn
    (target control : Q) (h : target ≠ control) :
    IsSupportedOn {target, control} (bellInverseAt target control h) := by
  exact (cnotAt_isSupportedOn_pair target control h).mul
    (hadamardAt_isSupportedOn_pair target control h)

theorem bellAt_evolves_target_descriptor
    (target control : Q) (h : target ≠ control) :
    DescriptorFamily.evolve (bellAt target control h)
        (DescriptorFamily.initial Q) target =
      { x := xAt target
        y := -(yAt target * zAt control)
        z := -(zAt target * zAt control) } := by
  apply Descriptor.ext_components
  · exact bellAt_conjugates_target_x target control h
  · exact bellAt_conjugates_target_y target control h
  · exact bellAt_conjugates_target_z target control h

theorem bellAt_evolves_control_descriptor
    (target control : Q) (h : target ≠ control) :
    DescriptorFamily.evolve (bellAt target control h)
        (DescriptorFamily.initial Q) control =
      { x := zAt control
        y := -(xAt target * yAt control)
        z := xAt target * xAt control } := by
  apply Descriptor.ext_components
  · exact bellAt_conjugates_control_x target control h
  · exact bellAt_conjugates_control_y target control h
  · exact bellAt_conjugates_control_z target control h

theorem bellInverseAt_evolves_target_descriptor
    (target control : Q) (h : target ≠ control) :
    DescriptorFamily.evolve (bellInverseAt target control h)
        (DescriptorFamily.initial Q) target =
      { x := xAt target
        y := -(yAt target * xAt control)
        z := -(zAt target * xAt control) } := by
  apply Descriptor.ext_components
  · exact bellInverseAt_conjugates_target_x target control h
  · exact bellInverseAt_conjugates_target_y target control h
  · exact bellInverseAt_conjugates_target_z target control h

theorem bellInverseAt_evolves_control_descriptor
    (target control : Q) (h : target ≠ control) :
    DescriptorFamily.evolve (bellInverseAt target control h)
        (DescriptorFamily.initial Q) control =
      { x := xAt target * zAt control
        y := -(xAt target * yAt control)
        z := xAt control } := by
  apply Descriptor.ext_components
  · exact bellInverseAt_conjugates_control_x target control h
  · exact bellInverseAt_conjugates_control_y target control h
  · exact bellInverseAt_conjugates_control_z target control h

/-! Exact basis-amplitude cross-check, independent of the descriptor calculation. -/

def bellLocal : Operator (Fin 2) :=
  hadamardAt (1 : Fin 2) * cnotLocal

def bellInverseLocal : Operator (Fin 2) :=
  cnotLocal * hadamardAt (1 : Fin 2)

theorem bellAt_eq_embedAlong (target control : Q) (h : target ≠ control) :
    bellAt target control h =
      embedAlong (targetControlPlacement target control h) bellLocal := by
  rw [bellAt, bellLocal, embedAlong_mul, cnotAt]
  congr 1
  unfold hadamardAt
  rw [embedAlong_embedQubit]
  rfl

theorem bellInverseAt_eq_embedAlong
    (target control : Q) (h : target ≠ control) :
    bellInverseAt target control h =
      embedAlong (targetControlPlacement target control h) bellInverseLocal := by
  rw [bellInverseAt, bellInverseLocal, embedAlong_mul, cnotAt]
  congr 1
  unfold hadamardAt
  rw [embedAlong_embedQubit]
  rfl

theorem bellLocal_apply (output input : Basis (Fin 2)) :
    bellLocal output input =
      if output 0 = cnotLocalOutput input 0
      then hadamard (output 1) (input 1)
      else 0 := by
  rw [bellLocal, Matrix.mul_apply]
  rw [Finset.sum_eq_single (cnotLocalOutput input)]
  · rw [cnotLocal_apply, if_pos rfl, mul_one, hadamardAt,
      embedQubit_apply_ite]
    have hcontrol : cnotLocalOutput input 1 = input 1 :=
      cnotLocalOutput_one input
    by_cases htarget : output 0 = cnotLocalOutput input 0
    · rw [if_pos htarget, if_pos]
      · rw [hcontrol]
      · intro j hj
        fin_cases j
        · exact htarget
        · exact (hj rfl).elim
    · rw [if_neg htarget, if_neg]
      intro hall
      exact htarget (hall 0 (by decide))
  · intro z _ hz
    rw [cnotLocal_apply, if_neg hz]
    simp
  · simp

theorem bellAt_apply (target control : Q) (h : target ≠ control)
    (output input : Basis Q) :
    bellAt target control h output input =
      if ∀ q, q ∉ Set.range (targetControlPlacement target control h) →
          output q = input q
      then if output target =
          (if input control = 0 then flipRaw (input target) else input target)
        then hadamard (output control) (input control)
        else 0
      else 0 := by
  rw [bellAt_eq_embedAlong, embedAlong_apply_ite]
  by_cases hout : ∀ q, q ∉ Set.range (targetControlPlacement target control h) →
      output q = input q
  · rw [if_pos hout, if_pos hout, bellLocal_apply]
    rfl
  · rw [if_neg hout, if_neg hout]

theorem bellInverseLocal_eq_conjTranspose :
    bellInverseLocal = bellLocalᴴ := by
  rw [bellInverseLocal, bellLocal, Matrix.conjTranspose_mul,
    cnotLocal_isHermitian, hadamardAt_isHermitian]

theorem star_hadamard_swap (i j : QubitIndex) :
    star (hadamard i j) = hadamard j i := by
  fin_cases i <;> fin_cases j <;> simp [hadamard, invSqrtTwo]

theorem bellInverseLocal_apply (output input : Basis (Fin 2)) :
    bellInverseLocal output input =
      if input 0 = cnotLocalOutput output 0
      then hadamard (output 1) (input 1)
      else 0 := by
  rw [bellInverseLocal_eq_conjTranspose, Matrix.conjTranspose_apply,
    bellLocal_apply]
  by_cases htarget : input 0 = cnotLocalOutput output 0
  · rw [if_pos htarget, if_pos htarget]
    exact star_hadamard_swap (input 1) (output 1)
  · rw [if_neg htarget, if_neg htarget]
    simp

theorem bellInverseAt_apply (target control : Q) (h : target ≠ control)
    (output input : Basis Q) :
    bellInverseAt target control h output input =
      if ∀ q, q ∉ Set.range (targetControlPlacement target control h) →
          output q = input q
      then if input target =
          (if output control = 0 then flipRaw (output target) else output target)
        then hadamard (output control) (input control)
        else 0
      else 0 := by
  rw [bellInverseAt_eq_embedAlong, embedAlong_apply_ite]
  by_cases hout : ∀ q, q ∉ Set.range (targetControlPlacement target control h) →
      output q = input q
  · rw [if_pos hout, if_pos hout, bellInverseLocal_apply]
    rfl
  · rw [if_neg hout, if_neg hout]

end
end Gates
end Deutsch
