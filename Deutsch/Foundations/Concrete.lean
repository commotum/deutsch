import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Concrete finite quantum operators

This is the executable convention layer selected provisionally in Stage 2. Register-size and
arbitrary-subsystem APIs remain Stage 3 work.
-/

namespace Deutsch
namespace Foundations

open scoped Matrix Kronecker

noncomputable section

/-- The paper's one-qubit matrix index. -/
abbrev QubitIndex := Fin 2

/-- A concrete one-qubit complex operator. -/
abbrev QubitMatrix := Matrix QubitIndex QubitIndex ℂ

/-- A two-qubit operator whose first product coordinate is the left tensor factor. -/
abbrev TwoQubitMatrix := Matrix (QubitIndex × QubitIndex) (QubitIndex × QubitIndex) ℂ

/-- Pauli `X` under the row/column order `0, 1`. -/
def pauliX : QubitMatrix := !![0, 1; 1, 0]

/-- Pauli `Y` under the row/column order `0, 1`. -/
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `Z` under the row/column order `0, 1`. -/
def pauliZ : QubitMatrix := !![1, 0; 0, -1]

/-- The one-qubit identity, named to avoid confusing it with `Complex.I`. -/
def identity₂ : QubitMatrix := 1

/-- The paper's projector for logical bit value `1`, namely the `+1` eigenspace of `Z`. -/
def bitOneProjector : QubitMatrix := ((2 : ℂ)⁻¹) • (identity₂ + pauliZ)

/-- The paper's projector for logical bit value `0`, namely the `-1` eigenspace of `Z`. -/
def bitZeroProjector : QubitMatrix := ((2 : ℂ)⁻¹) • (identity₂ - pauliZ)

/-- The column vector for paper bit value `1`; it is matrix-basis index `0`. -/
def ketOne : QubitIndex → ℂ := ![1, 0]

/-- The column vector for paper bit value `0`; it is matrix-basis index `1`. -/
def ketZero : QubitIndex → ℂ := ![0, 1]

/-- Tensor product of two column vectors, left factor first. -/
def tensorKet (left right : QubitIndex → ℂ) : QubitIndex × QubitIndex → ℂ :=
  fun index => left index.1 * right index.2

/-- Paper-convention CNOT: left factor is target and right factor is control. -/
def cnotTargetLeftControlRight : TwoQubitMatrix :=
  identity₂ ⊗ₖ bitZeroProjector + pauliX ⊗ₖ bitOneProjector

/-- Heisenberg evolution convention used throughout the project: `U† A U`. -/
def heisenberg (U A : QubitMatrix) : QubitMatrix := Uᴴ * A * U

/-- A phase gate used to distinguish `U† A U` from `U A U†`. -/
def phaseS : QubitMatrix := !![1, 0; 0, Complex.I]

end
end Foundations
end Deutsch
