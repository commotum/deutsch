import Deutsch.Gates.OneQubit
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Arbitrary-axis one-qubit rotations

This module gives a coordinate-explicit model of real three-vectors, their Pauli
operators, and rotations about a bundled unit axis.  The rotation matrix is connected
to the genuine Banach-algebra matrix exponential.  Its Heisenberg action is then proved
both as exponential conjugation and as the corresponding Rodrigues rotation.

The sign convention agrees with `Foundations.heisenberg U A = Uᴴ * A * U`:
the Schrödinger rotation is `exp (-i θ (n · σ) / 2)`, so an `x`-axis
rotation sends `Y` to `cos θ Y - sin θ Z`.
-/

namespace Deutsch
namespace Gates

open Foundations Register
open NormedSpace
open scoped Matrix

noncomputable section

/-! ## Real three-vectors and Pauli operators -/

/-- A real three-vector, with coordinates ordered as the Pauli matrices `X`, `Y`, `Z`. -/
@[ext]
structure Vector3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vector3

/-- Euclidean dot product on real three-vectors. -/
def dot (u v : Vector3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Right-handed cross product on real three-vectors. -/
def cross (u v : Vector3) : Vector3 where
  x := u.y * v.z - u.z * v.y
  y := u.z * v.x - u.x * v.z
  z := u.x * v.y - u.y * v.x

/-- Squared Euclidean length. -/
def normSq (v : Vector3) : ℝ :=
  dot v v

/-- The Rodrigues rotation appropriate to the project's Heisenberg convention.

Because observables evolve as `Uᴴ A U`, the sine term has the opposite orientation
from the active rotation of a spatial vector.
-/
def heisenbergRotate (n : Vector3) (theta : ℝ) (v : Vector3) : Vector3 where
  x :=
    theta.cos * v.x +
      (1 - theta.cos) * dot n v * n.x -
      theta.sin * (cross n v).x
  y :=
    theta.cos * v.y +
      (1 - theta.cos) * dot n v * n.y -
      theta.sin * (cross n v).y
  z :=
    theta.cos * v.z +
      (1 - theta.cos) * dot n v * n.z -
      theta.sin * (cross n v).z

end Vector3

/-- A rotation axis is a real three-vector of squared length one. -/
def UnitAxis :=
  {n : Vector3 // n.normSq = 1}

namespace UnitAxis

/-- The positive `x`-axis. -/
def xAxis : UnitAxis :=
  ⟨⟨1, 0, 0⟩, by norm_num [Vector3.normSq, Vector3.dot]⟩

/-- The positive `y`-axis. -/
def yAxis : UnitAxis :=
  ⟨⟨0, 1, 0⟩, by norm_num [Vector3.normSq, Vector3.dot]⟩

/-- The positive `z`-axis. -/
def zAxis : UnitAxis :=
  ⟨⟨0, 0, 1⟩, by norm_num [Vector3.normSq, Vector3.dot]⟩

end UnitAxis

/-- The Pauli operator `v · σ` associated with a real three-vector. -/
def pauliVector (v : Vector3) : QubitMatrix :=
  (v.x : ℂ) • pauliX + (v.y : ℂ) • pauliY + (v.z : ℂ) • pauliZ

/-- The Hermitian Pauli operator associated with a unit rotation axis. -/
def axisPauli (n : UnitAxis) : QubitMatrix :=
  pauliVector n.1

theorem pauliVector_isHermitian (v : Vector3) :
    (pauliVector v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

/-- Pauli multiplication in vector form. -/
theorem pauliVector_mul_pauliVector (u v : Vector3) :
    pauliVector u * pauliVector v =
      (Vector3.dot u v : ℂ) • identity₂ +
        Complex.I • pauliVector (Vector3.cross u v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, Vector3.dot, Vector3.cross, identity₂,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;>
    norm_num [Complex.I_sq] <;>
    simp [sub_eq_add_neg]

/-- A unit-axis Pauli operator is an involution. -/
theorem axisPauli_sq (n : UnitAxis) :
    axisPauli n * axisPauli n = identity₂ := by
  rw [axisPauli, pauliVector_mul_pauliVector]
  have hn : Vector3.dot n.1 n.1 = 1 := n.2
  have hcross : Vector3.cross n.1 n.1 = ⟨0, 0, 0⟩ := by
    ext <;> simp [Vector3.cross] <;> ring
  rw [hcross]
  simp [hn, pauliVector, identity₂]

theorem axisPauli_isHermitian (n : UnitAxis) :
    (axisPauli n).IsHermitian :=
  pauliVector_isHermitian n.1

/-- A unit-axis Pauli operator is unitary. -/
theorem axisPauli_unitary (n : UnitAxis) :
    axisPauli n ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (axisPauli n)ᴴ * axisPauli n = 1
  rw [axisPauli_isHermitian, axisPauli_sq, identity₂]

@[simp]
theorem axisPauli_xAxis : axisPauli UnitAxis.xAxis = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisPauli, pauliVector, UnitAxis.xAxis, pauliX, pauliY, pauliZ]

/-! ## Closed and exponential forms -/

/-- The matrix in the exponent of the Schrödinger rotation. -/
def axisRotationGenerator (n : UnitAxis) (theta : ℝ) : QubitMatrix :=
  (-Complex.I * (theta / 2 : ℂ)) • axisPauli n

/-- Closed Pauli form of rotation through `theta` about `n`. -/
def axisRotation (n : UnitAxis) (theta : ℝ) : QubitMatrix :=
  (Real.cos (theta / 2) : ℂ) • identity₂ -
    (Complex.I * (Real.sin (theta / 2) : ℂ)) • axisPauli n

private theorem involution_pow_even (A : QubitMatrix)
    (hA : A * A = identity₂) (k : ℕ) :
    A ^ (2 * k) = identity₂ := by
  rw [pow_mul]
  have hA' : A ^ 2 = identity₂ := by simpa [pow_two] using hA
  rw [hA']
  simp [identity₂]

private theorem involution_pow_odd (A : QubitMatrix)
    (hA : A * A = identity₂) (k : ℕ) :
    A ^ (2 * k + 1) = A := by
  rw [pow_add, involution_pow_even A hA]
  simp [identity₂]

private theorem expSeries_even_of_involution (A : QubitMatrix)
    (hA : A * A = identity₂) (z : ℂ) (k : ℕ) :
    expSeries ℂ QubitMatrix (2 * k) (fun _ => z • A) =
      (z ^ (2 * k) / (2 * k).factorial) • identity₂ := by
  rw [expSeries_apply_eq, smul_pow, involution_pow_even A hA]
  simp [div_eq_mul_inv, smul_smul, mul_comm]

private theorem expSeries_odd_of_involution (A : QubitMatrix)
    (hA : A * A = identity₂) (z : ℂ) (k : ℕ) :
    expSeries ℂ QubitMatrix (2 * k + 1) (fun _ => z • A) =
      (z ^ (2 * k + 1) / (2 * k + 1).factorial) • A := by
  rw [expSeries_apply_eq, smul_pow, involution_pow_odd A hA]
  simp [div_eq_mul_inv, smul_smul, mul_comm]

private theorem exp_smul_involution (A : QubitMatrix)
    (hA : A * A = identity₂) (z : ℂ) :
    exp (z • A) =
      Complex.cosh z • identity₂ + Complex.sinh z • A := by
  rw [exp_eq_tsum ℂ]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  apply HasSum.even_add_odd
  · rw [show (fun k => expSeries ℂ QubitMatrix (2 * k) (fun _ => z • A)) =
        (fun k => (z ^ (2 * k) / (2 * k).factorial) • identity₂) by
      funext k
      exact expSeries_even_of_involution A hA z k]
    exact (Complex.hasSum_cosh z).smul_const identity₂
  · rw [show (fun k => expSeries ℂ QubitMatrix (2 * k + 1) (fun _ => z • A)) =
        (fun k => (z ^ (2 * k + 1) / (2 * k + 1).factorial) • A) by
      funext k
      exact expSeries_odd_of_involution A hA z k]
    exact (Complex.hasSum_sinh z).smul_const A

/-- The closed rotation is the actual matrix exponential of its generator. -/
theorem exp_axisRotationGenerator (n : UnitAxis) (theta : ℝ) :
    exp (axisRotationGenerator n theta) = axisRotation n theta := by
  rw [axisRotationGenerator, exp_smul_involution (axisPauli n) (axisPauli_sq n)]
  unfold axisRotation
  have hcosh :
      Complex.cosh (-Complex.I * (theta / 2 : ℂ)) =
        (Real.cos (theta / 2) : ℂ) := by
    calc
      Complex.cosh (-Complex.I * (theta / 2 : ℂ)) =
          Complex.cosh ((-(theta / 2 : ℂ)) * Complex.I) := by
            congr 1
            ring
      _ = Complex.cos (-(theta / 2 : ℂ)) := Complex.cosh_mul_I _
      _ = Complex.cos (theta / 2 : ℂ) := Complex.cos_neg _
      _ = (Real.cos (theta / 2) : ℂ) := by
        convert (Complex.ofReal_cos (theta / 2)).symm using 1
        all_goals
          push_cast
          rfl
  have hsinh :
      Complex.sinh (-Complex.I * (theta / 2 : ℂ)) =
        -(Complex.I * (Real.sin (theta / 2) : ℂ)) := by
    calc
      Complex.sinh (-Complex.I * (theta / 2 : ℂ)) =
          Complex.sinh ((-(theta / 2 : ℂ)) * Complex.I) := by
            congr 1
            ring
      _ = Complex.sin (-(theta / 2 : ℂ)) * Complex.I := Complex.sinh_mul_I _
      _ = -(Complex.sin (theta / 2 : ℂ)) * Complex.I := by rw [Complex.sin_neg]
      _ = -(Complex.I * (Real.sin (theta / 2) : ℂ)) := by
        have hsin : Complex.sin (theta / 2 : ℂ) =
            (Real.sin (theta / 2) : ℂ) := by
          convert (Complex.ofReal_sin (theta / 2)).symm using 1
          all_goals
            push_cast
            rfl
        rw [hsin]
        ring
  rw [hcosh, hsinh]
  module

/-- Exponential form with the positive sign used on the left of Heisenberg conjugation. -/
theorem exp_positive_axisGenerator (n : UnitAxis) (theta : ℝ) :
    exp ((Complex.I * (theta / 2 : ℂ)) • axisPauli n) =
      axisRotation n (-theta) := by
  rw [← exp_axisRotationGenerator n (-theta)]
  apply congrArg exp
  unfold axisRotationGenerator
  congr 1
  push_cast
  ring

private theorem axisRotationGenerator_conjTranspose (n : UnitAxis) (theta : ℝ) :
    (axisRotationGenerator n theta)ᴴ = -axisRotationGenerator n theta := by
  unfold axisRotationGenerator
  rw [Matrix.conjTranspose_smul, axisPauli_isHermitian]
  rw [← neg_smul]
  congr 1
  apply Complex.ext <;> simp

theorem axisRotation_isUnitary (n : UnitAxis) (theta : ℝ) :
    axisRotation n theta ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [← exp_axisRotationGenerator]
  rw [Matrix.mem_unitaryGroup_iff']
  change (exp (axisRotationGenerator n theta))ᴴ *
      exp (axisRotationGenerator n theta) = 1
  rw [← Matrix.exp_conjTranspose, axisRotationGenerator_conjTranspose]
  rw [← Matrix.exp_add_of_commute]
  · simp
  · exact (Commute.refl (axisRotationGenerator n theta)).neg_left

theorem axisRotation_conjTranspose (n : UnitAxis) (theta : ℝ) :
    (axisRotation n theta)ᴴ = axisRotation n (-theta) := by
  rw [← exp_axisRotationGenerator, ← exp_axisRotationGenerator,
    ← Matrix.exp_conjTranspose, axisRotationGenerator_conjTranspose]
  apply congrArg exp
  unfold axisRotationGenerator
  rw [← neg_smul]
  congr 1
  push_cast
  ring

/-- Equation-(17)-shaped exponential conjugation for an arbitrary Pauli vector. -/
theorem axisRotation_heisenberg_eq_exponential_conjugation
    (n : UnitAxis) (theta : ℝ) (v : Vector3) :
    Foundations.heisenberg (axisRotation n theta) (pauliVector v) =
      exp ((Complex.I * (theta / 2 : ℂ)) • axisPauli n) *
        pauliVector v *
        exp ((-Complex.I * (theta / 2 : ℂ)) • axisPauli n) := by
  rw [Foundations.heisenberg, axisRotation_conjTranspose,
    ← exp_positive_axisGenerator, ← exp_axisRotationGenerator]
  rfl

/-! ## Rodrigues conjugation and the `x`-axis specialization -/

/-- Exact Rodrigues formula for conjugation of an arbitrary Pauli vector. -/
theorem axisRotation_heisenberg (n : UnitAxis) (theta : ℝ) (v : Vector3) :
    Foundations.heisenberg (axisRotation n theta) (pauliVector v) =
      pauliVector (Vector3.heisenbergRotate n.1 theta v) := by
  set c : ℝ := Real.cos (theta / 2) with hc_def
  set s : ℝ := Real.sin (theta / 2) with hs_def
  set C : ℝ := Real.cos theta with hC_def
  set S : ℝ := Real.sin theta with hS_def
  have hc : C = c * c - s * s := by
    rw [hC_def, hc_def, hs_def,
      show theta = theta / 2 + theta / 2 by ring, Real.cos_add]
    ring_nf
  have hs : S = 2 * s * c := by
    rw [hS_def, hc_def, hs_def,
      show theta = theta / 2 + theta / 2 by ring, Real.sin_add]
    ring_nf
  have hhalf : c * c + s * s = 1 := by
    rw [hc_def, hs_def]
    nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]
  have honeSubCos : 1 - (c * c - s * s) = 2 * s * s := by
    nlinarith
  have hpositive :
      axisRotation n theta =
        (c : ℂ) • identity₂ - (Complex.I * (s : ℂ)) • axisPauli n := by
    rw [axisRotation, hc_def, hs_def]
  have hnegative :
      axisRotation n (-theta) =
        (c : ℂ) • identity₂ + (Complex.I * (s : ℂ)) • axisPauli n := by
    unfold axisRotation
    rw [show -theta / 2 = -(theta / 2) by ring, Real.cos_neg, Real.sin_neg,
      ← hc_def, ← hs_def]
    module
  have hn := n.2
  simp [Vector3.normSq, Vector3.dot] at hn
  have hn_x := congrArg (fun r : ℝ => s ^ 2 * v.x * r) hn
  have hn_y := congrArg (fun r : ℝ => s ^ 2 * v.y * r) hn
  have hn_z := congrArg (fun r : ℝ => s ^ 2 * v.z * r) hn
  rw [Foundations.heisenberg, axisRotation_conjTranspose, hpositive, hnegative]
  unfold Vector3.heisenbergRotate
  rw [← hC_def, ← hS_def]
  rw [hc, hs, honeSubCos]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [axisPauli, pauliVector, Vector3.dot, Vector3.cross, identity₂,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;>
    ring_nf at hn_x hn_y hn_z ⊢ <;>
    linarith

@[simp]
theorem axisRotation_xAxis (theta : ℝ) :
    axisRotation UnitAxis.xAxis theta = rotationX theta := by
  simp [axisRotation, rotationX, rotationCosHalf, rotationSinHalf]

theorem axisRotation_xAxis_heisenberg_x (theta : ℝ) :
    Foundations.heisenberg (axisRotation UnitAxis.xAxis theta) pauliX =
      pauliX := by
  simpa using rotationX_heisenberg_x theta

theorem axisRotation_xAxis_heisenberg_y (theta : ℝ) :
    Foundations.heisenberg (axisRotation UnitAxis.xAxis theta) pauliY =
      (theta.cos : ℂ) • pauliY - (theta.sin : ℂ) • pauliZ := by
  simpa using rotationX_heisenberg_y theta

theorem axisRotation_xAxis_heisenberg_z (theta : ℝ) :
    Foundations.heisenberg (axisRotation UnitAxis.xAxis theta) pauliZ =
      (theta.sin : ℂ) • pauliY + (theta.cos : ℂ) • pauliZ := by
  simpa using rotationX_heisenberg_z theta

end
end Gates
end Deutsch
