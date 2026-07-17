import Deutsch.Foundations.Concrete
import Mathlib.Tactic

/-!
# Concrete state and finite-measurement API probe

This verification-only module exercises matrix positivity, unnormalized trace, finite effect
families, and an explicit mixed-state measurement. It deliberately does not commit the public API
to these thin wrappers.
-/

open scoped ComplexOrder Matrix

noncomputable section

namespace DeutschTests
namespace Foundations
namespace MatrixSemanticsProbe

open Deutsch Foundations

variable {n outcome : Type*}
variable [Fintype n] [DecidableEq n]

/-- A finite-dimensional density matrix: positive semidefinite with trace one. -/
structure Density (n : Type*) [Fintype n] [DecidableEq n] where
  op : Matrix n n ℂ
  positive : op.PosSemidef
  trace_one : op.trace = 1

/-- An effect `E`, encoded by positivity of `E` and `I - E`. -/
structure Effect (n : Type*) [Fintype n] [DecidableEq n] where
  op : Matrix n n ℂ
  positive : op.PosSemidef
  complement_positive : (1 - op).PosSemidef

/-- A finite-outcome family of effects summing to the identity. -/
structure FiniteMeasurement (n outcome : Type*)
    [Fintype n] [DecidableEq n] [Fintype outcome] where
  effect : outcome → Effect n
  complete : ∑ x, (effect x).op = 1

/-- The complex trace expression underlying the Born rule. -/
def bornWeight (rho : Density n) (effect : Effect n) : ℂ :=
  Matrix.trace (rho.op * effect.op)

/-- Real presentation of the Born weight; general bounds are not claimed by this probe. -/
def bornProbability (rho : Density n) (effect : Effect n) : ℝ :=
  (bornWeight rho effect).re

theorem bornWeights_normalize [Fintype outcome] (rho : Density n)
    (measurement : FiniteMeasurement n outcome) :
    ∑ x, bornWeight rho (measurement.effect x) = 1 := by
  classical
  simp only [bornWeight]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, measurement.complete, mul_one, rho.trace_one]

theorem bornProbabilities_normalize [Fintype outcome] (rho : Density n)
    (measurement : FiniteMeasurement n outcome) :
    ∑ x, bornProbability rho (measurement.effect x) = 1 := by
  have h := congrArg Complex.re (bornWeights_normalize rho measurement)
  simpa [bornProbability] using h

private def diagonalQubit (a b : ℂ) : QubitMatrix :=
  Matrix.diagonal ![a, b]

private theorem diagonalQubit_eq (a b : ℂ) :
    diagonalQubit a b = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalQubit]

/-- A mixed qubit density matrix, diagonal with two equal nonzero weights. -/
def maximallyMixed : Density QubitIndex where
  op := diagonalQubit (2 : ℂ)⁻¹ (2 : ℂ)⁻¹
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff]
  trace_one := by
    rw [diagonalQubit_eq, Matrix.trace_fin_two_of]
    norm_num

/-- Matrix index zero is the paper's logical bit value `1`. -/
def computationalEffectZero : Effect QubitIndex where
  op := diagonalQubit 1 0
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  complement_positive := by
    rw [diagonalQubit_eq]
    convert Matrix.PosSemidef.diagonal (d := ![(0 : ℂ), 1]) (by
      intro i
      fin_cases i <;> norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Matrix.one_apply]

/-- Matrix index one is the paper's logical bit value `0`. -/
def computationalEffectOne : Effect QubitIndex where
  op := diagonalQubit 0 1
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  complement_positive := by
    rw [diagonalQubit_eq]
    convert Matrix.PosSemidef.diagonal (d := ![(1 : ℂ), 0]) (by
      intro i
      fin_cases i <;> norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Matrix.one_apply]

def computationalMeasurement : FiniteMeasurement QubitIndex (Fin 2) where
  effect := ![computationalEffectZero, computationalEffectOne]
  complete := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [computationalEffectZero, computationalEffectOne, diagonalQubit,
        Matrix.diagonal, Matrix.one_apply]

theorem maximallyMixed_probability_zero :
    bornProbability maximallyMixed computationalEffectZero = (2 : ℝ)⁻¹ := by
  norm_num [bornProbability, bornWeight, maximallyMixed, computationalEffectZero,
    diagonalQubit_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_succ]

theorem maximallyMixed_probability_one :
    bornProbability maximallyMixed computationalEffectOne = (2 : ℝ)⁻¹ := by
  norm_num [bornProbability, bornWeight, maximallyMixed, computationalEffectOne,
    diagonalQubit_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_succ]

theorem maximallyMixed_probabilities_normalize :
    ∑ x : Fin 2, bornProbability maximallyMixed (computationalMeasurement.effect x) = 1 := by
  rw [show (∑ x : Fin 2, bornProbability maximallyMixed
      (computationalMeasurement.effect x)) =
      bornProbability maximallyMixed computationalEffectZero +
        bornProbability maximallyMixed computationalEffectOne by
    simp [computationalMeasurement, Fin.sum_univ_two]]
  rw [maximallyMixed_probability_zero, maximallyMixed_probability_one]
  norm_num

end MatrixSemanticsProbe
end Foundations
end DeutschTests

end
