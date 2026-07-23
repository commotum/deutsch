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
    simp [pauliVector, pauliX, pauliY, pauliZ, Matrix.IsHermitian,
      Matrix.conjTranspose_apply]

/-- Pauli multiplication in vector form. -/
theorem pauliVector_mul_pauliVector (u v : Vector3) :
    pauliVector u * pauliVector v =
      (Vector3.dot u v : ℂ) • identity₂ +
        Complex.I • pauliVector (Vector3.cross u v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, Vector3.dot, Vector3.cross, identity₂,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;>
    ring_nf <;>
    norm_num [Complex.I_sq]

/-- A unit-axis Pauli operator is an involution. -/
theorem axisPauli_sq (n : UnitAxis) :
    axisPauli n * axisPauli n = identity₂ := by
  rw [axisPauli, pauliVector_mul_pauliVector]
  have hn : Vector3.dot n.1 n.1 = 1 := n.2
  have hcross : Vector3.cross n.1 n.1 = ⟨0, 0, 0⟩ := by
    ext <;> simp [Vector3.cross]
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
  · exact ((Complex.hasSum_cosh z).smul_const identity₂).congr
      (fun k => (expSeries_even_of_involution A hA z k).symm)
  · exact ((Complex.hasSum_sinh z).smul_const A).congr
      (fun k => (expSeries_odd_of_involution A hA z k).symm)

/-- The closed rotation is the actual matrix exponential of its generator. -/
theorem exp_axisRotationGenerator (n : UnitAxis) (theta : ℝ) :
    exp (axisRotationGenerator n theta) = axisRotation n theta := by
  rw [axisRotationGenerator, exp_smul_involution (axisPauli n) (axisPauli_sq n)]
  unfold axisRotation
  rw [show (-Complex.I * (theta / 2 : ℂ)) =
      (-(theta / 2 : ℂ)) * Complex.I by ring]
  simp only [Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_neg,
    Complex.sin_neg, neg_mul, Complex.ofReal_cos, Complex.ofReal_sin]
  module

/-- Exponential form with the positive sign used on the left of Heisenberg conjugation. -/
theorem exp_positive_axisGenerator (n : UnitAxis) (theta : ℝ) :
    exp ((Complex.I * (theta / 2 : ℂ)) • axisPauli n) =
      axisRotation n (-theta) := by
  rw [← exp_axisRotationGenerator n (-theta)]
  congr 2
  push_cast
  ring

private theorem axisRotationGenerator_conjTranspose (n : UnitAxis) (theta : ℝ) :
    (axisRotationGenerator n theta)ᴴ = -axisRotationGenerator n theta := by
  unfold axisRotationGenerator
  rw [Matrix.conjTranspose_smul, axisPauli_isHermitian]
  congr 1
  simp only [map_mul, map_neg, starRingEnd_apply, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, neg_mul]
  ring

theorem axisRotation_isUnitary (n : UnitAxis) (theta : ℝ) :
    axisRotation n theta ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [← exp_axisRotationGenerator]
  rw [Matrix.mem_unitaryGroup_iff']
  rw [← Matrix.exp_conjTranspose, axisRotationGenerator_conjTranspose]
  rw [← Matrix.exp_add_of_commute]
  · simp
  · exact (Commute.refl (axisRotationGenerator n theta)).neg_left

theorem axisRotation_conjTranspose (n : UnitAxis) (theta : ℝ) :
    (axisRotation n theta)ᴴ = axisRotation n (-theta) := by
  rw [← exp_axisRotationGenerator, ← exp_axisRotationGenerator,
    ← Matrix.exp_conjTranspose, axisRotationGenerator_conjTranspose]
  congr 2
  unfold axisRotationGenerator
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
  rw [Foundations.heisenberg, axisRotation_conjTranspose]
  have hc : Real.cos theta =
      Real.cos (theta / 2) * Real.cos (theta / 2) -
        Real.sin (theta / 2) * Real.sin (theta / 2) := by
    rw [show theta = theta / 2 + theta / 2 by ring, Real.cos_add]
    ring
  have hs : Real.sin theta =
      2 * Real.sin (theta / 2) * Real.cos (theta / 2) := by
    rw [show theta = theta / 2 + theta / 2 by ring, Real.sin_add]
    ring
  have hn := n.2
  simp [Vector3.normSq, Vector3.dot] at hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [axisRotation, axisPauli, pauliVector,
      Vector3.heisenbergRotate, Vector3.dot, Vector3.cross, identity₂,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;>
    ring_nf at hc hs hn ⊢ <;>
    nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]

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
