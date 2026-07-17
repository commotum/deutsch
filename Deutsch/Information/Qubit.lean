import Deutsch.Information.Reduction
import Deutsch.Register.Pauli
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# One-qubit statistical semantics and mixed-state boundary

This module contains exact one-qubit calculations used to audit the paper's mixed-state
fixed-reference sentence and, downstream, to connect Pauli moments with local measurement
statistics.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The maximally mixed state of one named qubit. -/
def maximallyMixedQubit : Density (Fin 1) where
  op := Matrix.diagonal (fun _ => (2 : ℂ)⁻¹)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    norm_num [Complex.nonneg_iff]
  trace_one := by
    simp [Matrix.trace]

theorem maximallyMixedQubit_purity :
    purity maximallyMixedQubit = (2 : ℝ)⁻¹ := by
  simp [purity, maximallyMixedQubit, Matrix.trace]

theorem basisDensity_purity (bits : Basis Q) :
    purity (basisDensity bits) = 1 := by
  classical
  have hidem :
      (basisDensity bits).op * (basisDensity bits).op =
        (basisDensity bits).op := by
    simp only [basisDensity]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i = bits
    · subst i
      simp
    · simp [Pi.single, h]
  rw [purity, hidem, (basisDensity bits).trace_one]
  norm_num

theorem referenceDensity_purity (Q : Type*) [Fintype Q] [DecidableEq Q] :
    purity (referenceDensity Q) = 1 := by
  simpa [referenceDensity] using
    basisDensity_purity (paperZeroAssignment Q)

/-- A maximally mixed qubit cannot become any pure basis state by same-register unitarity. -/
theorem maximallyMixedQubit_cannot_evolve_to_basis
    (U : Operator (Fin 1))
    (hU : U ∈ Matrix.unitaryGroup (Basis (Fin 1)) ℂ)
    (bits : Basis (Fin 1)) :
    maximallyMixedQubit.evolve U hU ≠ basisDensity bits := by
  intro h
  have hp := purity_evolve maximallyMixedQubit U hU
  rw [h, basisDensity_purity, maximallyMixedQubit_purity] at hp
  norm_num at hp

/--
Executable obstruction to the paper's same-register mixed-state fixed-pure-reference reading.
Unitary conjugation preserves purity `1/2`, whereas the reference density has purity `1`.
-/
theorem maximallyMixedQubit_cannot_evolve_to_reference
    (U : Operator (Fin 1))
    (hU : U ∈ Matrix.unitaryGroup (Basis (Fin 1)) ℂ) :
    maximallyMixedQubit.evolve U hU ≠ referenceDensity (Fin 1) := by
  simpa [referenceDensity] using
    maximallyMixedQubit_cannot_evolve_to_basis U hU
      (paperZeroAssignment (Fin 1))

private def plusProjector (A : QubitMatrix) : QubitMatrix :=
  ((2 : ℂ)⁻¹) • (identity₂ + A)

private theorem plusProjector_isHermitian (A : QubitMatrix)
    (hA : A.IsHermitian) : (plusProjector A).IsHermitian := by
  rw [Matrix.IsHermitian] at hA ⊢
  simp [plusProjector, identity₂, hA]

private theorem plusProjector_mul_self (A : QubitMatrix)
    (hAA : A * A = identity₂) :
    plusProjector A * plusProjector A = plusProjector A := by
  unfold plusProjector
  have hAA' : A * A = 1 := by simpa [identity₂] using hAA
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [identity₂, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hAA']
  module

private theorem projection_posSemidef {n : Type*} [Fintype n]
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    P.PosSemidef := by
  rw [← hPP]
  simpa only [hP.eq] using Matrix.posSemidef_conjTranspose_mul_self P

private theorem projection_complement_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) : (1 - P).PosSemidef := by
  apply projection_posSemidef
  · rw [Matrix.IsHermitian]
    simp [hP.eq]
  · simp [Matrix.sub_mul, Matrix.mul_sub, hPP]

private def effectOfProjection {R : Type*} [Fintype R] [DecidableEq R]
    (P : Operator R) (hP : P.IsHermitian) (hPP : P * P = P) : Effect R where
  op := P
  positive := projection_posSemidef hP hPP
  complement_positive := projection_complement_posSemidef hP hPP

private def localPauliPlusEffect {R : Type*} [Fintype R] [DecidableEq R]
    (q : R) (A : QubitMatrix) (hA : A.IsHermitian)
    (hAA : A * A = identity₂) : Effect R :=
  effectOfProjection (embedQubit q (plusProjector A))
    (embedQubit_isHermitian q _ (plusProjector_isHermitian A hA))
    (by
      rw [← embedQubit_mul, plusProjector_mul_self A hAA])

/-- The `+1` Pauli-X effect on a named qubit. -/
def xPlusEffect {R : Type*} [Fintype R] [DecidableEq R] (q : R) : Effect R :=
  localPauliPlusEffect q pauliX pauliX_isHermitian pauliX_mul_pauliX

/-- The `+1` Pauli-Y effect on a named qubit. -/
def yPlusEffect {R : Type*} [Fintype R] [DecidableEq R] (q : R) : Effect R :=
  localPauliPlusEffect q pauliY pauliY_isHermitian pauliY_mul_pauliY

/-- The `+1` Pauli-Z effect on a named qubit. -/
def zPlusEffect {R : Type*} [Fintype R] [DecidableEq R] (q : R) : Effect R :=
  localPauliPlusEffect q pauliZ pauliZ_isHermitian pauliZ_mul_pauliZ

@[simp]
theorem xPlusEffect_op {R : Type*} [Fintype R] [DecidableEq R] (q : R) :
    (xPlusEffect q).op = ((2 : ℂ)⁻¹) • (1 + xAt q) := by
  simp [xPlusEffect, localPauliPlusEffect, effectOfProjection, plusProjector,
    xAt, identity₂]

@[simp]
theorem yPlusEffect_op {R : Type*} [Fintype R] [DecidableEq R] (q : R) :
    (yPlusEffect q).op = ((2 : ℂ)⁻¹) • (1 + yAt q) := by
  simp [yPlusEffect, localPauliPlusEffect, effectOfProjection, plusProjector,
    yAt, identity₂]

@[simp]
theorem zPlusEffect_op {R : Type*} [Fintype R] [DecidableEq R] (q : R) :
    (zPlusEffect q).op = ((2 : ℂ)⁻¹) • (1 + zAt q) := by
  simp [zPlusEffect, localPauliPlusEffect, effectOfProjection, plusProjector,
    zAt, identity₂]

/-- The `Z=+1` effect is exactly the paper's `bit 1` projector. -/
theorem zPlusEffect_op_eq_paperBitOneProjectorAt
    {R : Type*} [Fintype R] [DecidableEq R] (q : R) :
    (zPlusEffect q).op = paperBitOneProjectorAt q := by
  rw [zPlusEffect_op, paperBitOneProjectorAt_eq]

/-- Equality of the identity and three Pauli moments determines a `2 × 2` matrix. -/
theorem qubitMatrix_eq_of_pauli_traces_eq {A B : QubitMatrix}
    (hI : A.trace = B.trace)
    (hX : (A * pauliX).trace = (B * pauliX).trace)
    (hY : (A * pauliY).trace = (B * pauliY).trace)
    (hZ : (A * pauliZ).trace = (B * pauliZ).trace) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
      pauliX, pauliY, pauliZ] at hI hX hY hZ ⊢
  · linear_combination (hI + hZ) / 2
  · have hY' := congrArg (fun z : ℂ => -Complex.I * z) hY
    ring_nf at hY'
    simp [pow_two, Complex.I_mul_I] at hY'
    linear_combination (hX + hY') / 2
  · have hY' := congrArg (fun z : ℂ => -Complex.I * z) hY
    ring_nf at hY'
    simp [pow_two, Complex.I_mul_I] at hY'
    linear_combination (hX - hY') / 2
  · linear_combination (hI - hZ) / 2

private def uniqueBasisEquiv {R : Type*} [Subsingleton R] (q : R) :
    Basis R ≃ QubitIndex where
  toFun bits := bits q
  invFun bit := fun _ ↦ bit
  left_inv bits := by
    funext r
    exact congrArg bits (Subsingleton.elim q r)
  right_inv _ := rfl

private def toQubitMatrix {R : Type*} [Fintype R] [DecidableEq R]
    [Subsingleton R] (q : R) (A : Operator R) : QubitMatrix :=
  Matrix.reindexRingEquiv ℂ (uniqueBasisEquiv q) A

private theorem toQubitMatrix_trace {R : Type*} [Fintype R] [DecidableEq R]
    [Subsingleton R] (q : R) (A : Operator R) :
    (toQubitMatrix q A).trace = A.trace := by
  unfold toQubitMatrix Matrix.trace Matrix.diag Matrix.reindexRingEquiv
  exact Equiv.sum_comp (uniqueBasisEquiv q).symm (fun i ↦ A i i)

private theorem toQubitMatrix_embedQubit {R : Type*} [Fintype R] [DecidableEq R]
    [Subsingleton R] (q : R) (A : QubitMatrix) :
    toQubitMatrix q (embedQubit q A) = A := by
  ext i j
  rw [toQubitMatrix]
  change embedQubit q A ((uniqueBasisEquiv q).symm i)
      ((uniqueBasisEquiv q).symm j) = A i j
  rw [embedQubit_apply_ite]
  rw [if_pos (by
    intro r hr
    exact False.elim (hr (Subsingleton.elim r q)))]
  rfl

private theorem toQubitMatrix_trace_mul_embedQubit
    {R : Type*} [Fintype R] [DecidableEq R] [Subsingleton R]
    (q : R) (A : Operator R) (P : QubitMatrix) :
    (toQubitMatrix q A * P).trace = (A * embedQubit q P).trace := by
  calc
    (toQubitMatrix q A * P).trace =
        (toQubitMatrix q A * toQubitMatrix q (embedQubit q P)).trace := by
          rw [toQubitMatrix_embedQubit]
    _ = (toQubitMatrix q (A * embedQubit q P)).trace := by
      unfold toQubitMatrix
      rw [map_mul]
    _ = (A * embedQubit q P).trace := toQubitMatrix_trace q _

private theorem pauliMoment_eq_of_plusProbability_eq
    {R : Type*} [Fintype R] [DecidableEq R]
    (rho sigma : Density R) (P : Operator R) (effect : Effect R)
    (hop : effect.op = ((2 : ℂ)⁻¹) • (1 + P))
    (hprob : bornProbability rho effect = bornProbability sigma effect) :
    (rho.op * P).trace = (sigma.op * P).trace := by
  have hw : bornWeight rho effect = bornWeight sigma effect := by
    rw [bornWeight_eq_probability, bornWeight_eq_probability, hprob]
  simp only [bornWeight, hop, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add,
    rho.trace_one, sigma.trace_one] at hw
  linear_combination 2 * hw

/-- Three Pauli `+1` probabilities determine a one-qubit density state. -/
theorem density_eq_of_pauliPlus_probabilities
    {R : Type*} [Fintype R] [DecidableEq R] [Subsingleton R]
    (q : R) {rho sigma : Density R}
    (hX : bornProbability rho (xPlusEffect q) =
      bornProbability sigma (xPlusEffect q))
    (hY : bornProbability rho (yPlusEffect q) =
      bornProbability sigma (yPlusEffect q))
    (hZ : bornProbability rho (zPlusEffect q) =
      bornProbability sigma (zPlusEffect q)) :
    rho = sigma := by
  have hXmoment : (rho.op * xAt q).trace = (sigma.op * xAt q).trace :=
    pauliMoment_eq_of_plusProbability_eq rho sigma (xAt q) (xPlusEffect q)
      (xPlusEffect_op q) hX
  have hYmoment : (rho.op * yAt q).trace = (sigma.op * yAt q).trace :=
    pauliMoment_eq_of_plusProbability_eq rho sigma (yAt q) (yPlusEffect q)
      (yPlusEffect_op q) hY
  have hZmoment : (rho.op * zAt q).trace = (sigma.op * zAt q).trace :=
    pauliMoment_eq_of_plusProbability_eq rho sigma (zAt q) (zPlusEffect q)
      (zPlusEffect_op q) hZ
  apply Density.ext
  apply (Matrix.reindexRingEquiv ℂ (uniqueBasisEquiv q)).injective
  change toQubitMatrix q rho.op = toQubitMatrix q sigma.op
  apply qubitMatrix_eq_of_pauli_traces_eq
  · rw [toQubitMatrix_trace, toQubitMatrix_trace, rho.trace_one, sigma.trace_one]
  · rw [toQubitMatrix_trace_mul_embedQubit, toQubitMatrix_trace_mul_embedQubit]
    simpa [xAt] using hXmoment
  · rw [toQubitMatrix_trace_mul_embedQubit, toQubitMatrix_trace_mul_embedQubit]
    simpa [yAt] using hYmoment
  · rw [toQubitMatrix_trace_mul_embedQubit, toQubitMatrix_trace_mul_embedQubit]
    simpa [zAt] using hZmoment

/-- Three embedded Pauli probabilities characterize a one-qubit reduced state. -/
theorem reduce_eq_iff_embedded_pauliPlus_probabilities
    {R : Type*} [Fintype R] [DecidableEq R]
    (s : Finset R) [Subsingleton {q : R // q ∈ s}] [Nonempty {q : R // q ∈ s}]
    (q : {q : R // q ∈ s}) {rho sigma : Density R} :
    rho.reduce s = sigma.reduce s ↔
      (bornProbability rho ((xPlusEffect q).embedSubsystem s) =
          bornProbability sigma ((xPlusEffect q).embedSubsystem s) ∧
       bornProbability rho ((yPlusEffect q).embedSubsystem s) =
          bornProbability sigma ((yPlusEffect q).embedSubsystem s) ∧
       bornProbability rho ((zPlusEffect q).embedSubsystem s) =
          bornProbability sigma ((zPlusEffect q).embedSubsystem s)) := by
  constructor
  · intro h
    constructor
    · rw [← bornProbability_reduce, ← bornProbability_reduce, h]
    constructor
    · rw [← bornProbability_reduce, ← bornProbability_reduce, h]
    · rw [← bornProbability_reduce, ← bornProbability_reduce, h]
  · rintro ⟨hX, hY, hZ⟩
    apply density_eq_of_pauliPlus_probabilities q
    · rw [bornProbability_reduce, bornProbability_reduce]
      exact hX
    · rw [bornProbability_reduce, bornProbability_reduce]
      exact hY
    · rw [bornProbability_reduce, bornProbability_reduce]
      exact hZ

/-- Singleton reduction equality is equivalent to every embedded local effect statistic. -/
theorem reduce_singleton_eq_iff_embedded_effect_probabilities
    {R : Type*} [Fintype R] [DecidableEq R] (q : R)
    {rho sigma : Density R} :
    rho.reduce {q} = sigma.reduce {q} ↔
      ∀ effect : Effect {r : R // r ∈ ({q} : Finset R)},
        bornProbability rho (effect.embedSubsystem {q}) =
          bornProbability sigma (effect.embedSubsystem {q}) := by
  exact reduced_density_eq_iff_embedded_effect_probabilities
    ({q} : Finset R) rho sigma

end
end Information
end Deutsch
