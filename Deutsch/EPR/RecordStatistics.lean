import Deutsch.EPR.Circuit
import Deutsch.EPR.Statistics
import Deutsch.Information.Qubit
import Deutsch.Information.Reduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Four-wire EPR record statistics

This module gives Schrödinger-state semantics to Figure 2's literal four-wire chronology.  The
time-three state is obtained from the named circuit with both coherent record CNOTs still present,
and the time-four state additionally includes the final comparison CNOT.  Computational record
effects are placed explicitly on `q1,q4`.

The coherent records have the same computational-basis outcome probabilities as the independent
two-qubit EPR calculation.  This is intentionally a statistical bridge, not an equality of reduced
density operators: tracing out the two source wires removes record-basis coherences.  No selective
measurement or collapse is inserted into the circuit.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Information Register
open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

noncomputable section

def pairPlacement : Fin 2 ↪ EPRQubit :=
  targetControlPlacement q2 q3 q2_ne_q3

private theorem embedAlong_pairIdentity (A : Operator (Fin 2)) :
    embedAlong
        (targetControlPlacement (0 : Fin 2) (1 : Fin 2) (by decide)) A =
      A := by
  ext output input
  rw [embedAlong_apply_ite]
  have houtside :
      ∀ q, q ∉ Set.range
          (targetControlPlacement (0 : Fin 2) (1 : Fin 2) (by decide)) →
        output q = input q := by
    intro q hq
    exfalso
    apply hq
    fin_cases q
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  rw [if_pos houtside]
  congr 1 <;> funext k <;> fin_cases k <;> rfl

private theorem pairPreparation_eq_bellInverseLocal :
    pairPreparation = bellInverseLocal := by
  rw [pairPreparation, bellInverseAt_eq_embedAlong,
    embedAlong_pairIdentity]

theorem timeTwoUnitary_eq_embedAlong_pairCircuit (theta phi : ℝ) :
    timeTwoUnitary theta phi =
      embedAlong pairPlacement (pairCircuit theta phi) := by
  rw [timeTwoUnitary, pairCircuit, pairRotations, rotationLayer,
    timeOneUnitary, bellInverseAt_eq_embedAlong]
  rw [embedAlong_mul, embedAlong_mul]
  unfold rotationXAt
  rw [
    embedAlong_embedQubit, embedAlong_embedQubit]
  rw [pairPreparation_eq_bellInverseLocal]
  rfl

def liftPairCoordinates (psi : Basis (Fin 2) → ℂ) :
    Basis EPRQubit → ℂ :=
  fun bits =>
    if bits q1 = 1 ∧ bits q4 = 1 then
      psi (pairBits (bits q2) (bits q3))
    else 0

def liftPairKet (psi : Ket (Fin 2)) : Ket EPRQubit :=
  WithLp.toLp 2 (liftPairCoordinates psi.ofLp)

theorem embedPair_act_reference (U : Operator (Fin 2)) :
    act (embedAlong pairPlacement U) (referenceKet EPRQubit) =
      liftPairKet (act U (referenceKet (Fin 2))) := by
  apply WithLp.ofLp_injective
  change (embedAlong pairPlacement U).mulVec
      (Pi.single (paperZeroAssignment EPRQubit) 1) =
    liftPairCoordinates
      (U.mulVec (Pi.single (paperZeroAssignment (Fin 2)) 1))
  rw [Matrix.mulVec_single_one]
  funext output
  change embedAlong pairPlacement U output (paperZeroAssignment EPRQubit) = _
  rw [embedAlong_apply_ite, Matrix.mulVec_single_one]
  simp only [liftPairCoordinates, Matrix.col_apply]
  have houtside :
      (∀ q, q ∉ Set.range pairPlacement →
        output q = paperZeroAssignment EPRQubit q) ↔
      output q1 = 1 ∧ output q4 = 1 := by
    constructor
    · intro h
      constructor
      · exact h q1 (by
          intro hrange
          rcases hrange with ⟨k, hk⟩
          fin_cases k <;> simp [pairPlacement, q1, q2, q3] at hk)
      · exact h q4 (by
          intro hrange
          rcases hrange with ⟨k, hk⟩
          fin_cases k <;> simp [pairPlacement, q2, q3, q4] at hk)
    · rintro ⟨h1, h4⟩ q hq
      fin_cases q
      · exact h1
      · exact (hq ⟨0, rfl⟩).elim
      · exact (hq ⟨1, rfl⟩).elim
      · exact h4
  have hselected :
      (fun k => output (pairPlacement k)) =
        pairBits (output q2) (output q3) := by
    funext k
    fin_cases k <;> rfl
  have hreference :
      (fun k => paperZeroAssignment EPRQubit (pairPlacement k)) =
        paperZeroAssignment (Fin 2) := rfl
  by_cases hrecord : output q1 = 1 ∧ output q4 = 1
  · rw [if_pos (houtside.mpr hrecord), if_pos hrecord,
      hselected, hreference]
  · rw [if_neg (fun h => hrecord (houtside.mp h)), if_neg hrecord]

theorem timeTwoPureKet_eq_liftPair (theta phi : ℝ) :
    act (timeTwoUnitary theta phi) (referenceKet EPRQubit) =
      liftPairKet (pairPureState theta phi).ket := by
  rw [timeTwoUnitary_eq_embedAlong_pairCircuit,
    embedPair_act_reference]
  rfl

def recordedPairCoordinates (psi : Basis (Fin 2) → ℂ) :
    Basis EPRQubit → ℂ :=
  fun bits =>
    if bits q1 = bits q2 ∧ bits q4 = bits q3 then
      psi (pairBits (bits q1) (bits q4))
    else 0

def recordedPairKet (psi : Ket (Fin 2)) : Ket EPRQubit :=
  WithLp.toLp 2 (recordedPairCoordinates psi.ofLp)

private theorem cnotOutput_involutive
    (target control : EPRQubit) (h : target ≠ control)
    (bits : Basis EPRQubit) :
    cnotOutput target control (cnotOutput target control bits) = bits := by
  funext q
  by_cases hqt : q = target
  · subst q
    have hflip (bit : QubitIndex) : flipRaw (flipRaw bit) = bit := by
      fin_cases bit <;> rfl
    rw [cnotOutput_target, cnotOutput_control h, cnotOutput_target]
    generalize bits control = bit
    fin_cases bit <;> simp [hflip]
  · rw [cnotOutput_other _ hqt, cnotOutput_other _ hqt]

private theorem cnotAt_act_coordinate
    (target control : EPRQubit) (h : target ≠ control)
    (psi : Ket EPRQubit) (output : Basis EPRQubit) :
    (act (cnotAt target control h) psi).ofLp output =
      psi.ofLp (cnotOutput target control output) := by
  change ((cnotAt target control h).mulVec psi.ofLp) output = _
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (cnotOutput target control output)]
  · rw [cnotAt_apply, if_pos]
    · simp
    · exact (cnotOutput_involutive target control h output).symm
  · intro other hother
    rw [cnotAt_apply, if_neg]
    · simp
    · intro hout
      apply hother
      rw [← cnotOutput_involutive target control h other, ← hout]

theorem recordingLayer_liftPairKet (psi : Ket (Fin 2)) :
    act recordingLayer (liftPairKet psi) = recordedPairKet psi := by
  apply WithLp.ofLp_injective
  funext output
  rw [show recordingLayer = rightRecordingGate * leftRecordingGate by rfl,
    act_mul]
  change
    (act rightRecordingGate
      (act leftRecordingGate (liftPairKet psi))).ofLp output = _
  rw [show rightRecordingGate = cnotAt q4 q3 q4_ne_q3 by rfl,
    cnotAt_act_coordinate]
  rw [show leftRecordingGate = cnotAt q1 q2 q1_ne_q2 by rfl,
    cnotAt_act_coordinate]
  change liftPairCoordinates psi.ofLp
      (cnotOutput q1 q2 (cnotOutput q4 q3 output)) =
    recordedPairCoordinates psi.ofLp output
  have hout : output = ![output q1, output q2, output q3, output q4] := by
    funext q
    fin_cases q <;> rfl
  rw [hout]
  generalize output q1 = b1
  generalize output q2 = b2
  generalize output q3 = b3
  generalize output q4 = b4
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> fin_cases b4 <;>
    simp [liftPairCoordinates, recordedPairCoordinates, cnotOutput, flipRaw,
      pairBits, q1, q2, q3, q4]

def fourWireReferencePureState : PureState EPRQubit where
  ket := referenceKet EPRQubit
  norm_eq_one := norm_referenceKet

def fourWireTimeThreePureState (theta phi : ℝ) : PureState EPRQubit :=
  fourWireReferencePureState.evolve (timeThreeUnitary theta phi)
    (timeThreeUnitary_unitary theta phi)

def fourWireTimeThreeDensity (theta phi : ℝ) : Density EPRQubit :=
  pureDensity (fourWireTimeThreePureState theta phi)

def fourWireTimeFourPureState (theta phi : ℝ) : PureState EPRQubit :=
  fourWireReferencePureState.evolve (timeFourUnitary theta phi)
    (timeFourUnitary_unitary theta phi)

def fourWireTimeFourDensity (theta phi : ℝ) : Density EPRQubit :=
  pureDensity (fourWireTimeFourPureState theta phi)

theorem fourWireTimeThreeDensity_eq_referenceDensity_evolve
    (theta phi : ℝ) :
    fourWireTimeThreeDensity theta phi =
      (referenceDensity EPRQubit).evolve
        (timeThreeUnitary theta phi)
        (timeThreeUnitary_unitary theta phi) := by
  rw [fourWireTimeThreeDensity, fourWireTimeThreePureState,
    pureDensity_evolve]
  congr 1
  simpa [fourWireReferencePureState, referenceDensity, referenceKet] using
    (pureDensity_basisState (paperZeroAssignment EPRQubit))

theorem fourWireTimeFourDensity_eq_referenceDensity_evolve
    (theta phi : ℝ) :
    fourWireTimeFourDensity theta phi =
      (referenceDensity EPRQubit).evolve
        (timeFourUnitary theta phi)
        (timeFourUnitary_unitary theta phi) := by
  rw [fourWireTimeFourDensity, fourWireTimeFourPureState,
    pureDensity_evolve]
  congr 1
  simpa [fourWireReferencePureState, referenceDensity, referenceKet] using
    (pureDensity_basisState (paperZeroAssignment EPRQubit))

theorem fourWireTimeThreePureState_ket (theta phi : ℝ) :
    (fourWireTimeThreePureState theta phi).ket =
      recordedPairKet (pairPureState theta phi).ket := by
  change act (timeThreeUnitary theta phi) (referenceKet EPRQubit) = _
  rw [timeThreeUnitary, act_mul, timeTwoPureKet_eq_liftPair,
    recordingLayer_liftPairKet]

private def diagonalEventEffect {Q : Type*} [Fintype Q] [DecidableEq Q]
    (event : Basis Q → Prop) [DecidablePred event] : Effect Q where
  op := Matrix.diagonal (fun bits => if event bits then 1 else 0)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro bits
    by_cases h : event bits <;> simp [h]
  complement_positive := by
    rw [show (1 : Operator Q) -
          Matrix.diagonal (fun bits => if event bits then 1 else 0) =
        Matrix.diagonal (fun bits => if event bits then 0 else 1) by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases h : event i <;> simp [Matrix.diagonal, h]
      · simp [Matrix.diagonal, hij]]
    apply Matrix.PosSemidef.diagonal
    intro bits
    by_cases h : event bits <;> simp [h]

private theorem pureDensity_diagonalEventEffect_probability
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : PureState Q) (event : Basis Q → Prop) [DecidablePred event] :
    bornProbability (pureDensity psi) (diagonalEventEffect event) =
      (∑ bits : Basis Q,
        if event bits then
          psi.ket.ofLp bits * star (psi.ket.ofLp bits)
        else 0).re := by
  simp only [bornProbability, bornWeight, pureDensity, densityOfVector,
    diagonalEventEffect, Matrix.trace, Matrix.diag, Matrix.mul_diagonal,
    Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro bits _
  by_cases h : event bits <;> simp [h]

private theorem pureDensity_basisEffect_probability'
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : PureState Q) (bits : Basis Q) :
    bornProbability (pureDensity psi) (basisEffect bits) =
      (psi.ket.ofLp bits * star (psi.ket.ofLp bits)).re := by
  classical
  simp only [bornProbability, bornWeight, pureDensity, densityOfVector,
    basisEffect, basisDensity, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply]
  rw [Finset.sum_eq_single bits]
  · simp
  · intro other _ hne
    simp [hne]
  · simp

def recordPlacement : Fin 2 ↪ EPRQubit :=
  targetControlPlacement q1 q4 q1_ne_q4

def recordOutcomeEffect (left right : QubitIndex) : Effect EPRQubit :=
  (basisEffect (pairBits left right)).embedAlong recordPlacement

theorem recordOutcomeEffect_eq_embedAlong
    (left right : QubitIndex) :
    recordOutcomeEffect left right =
      (basisEffect (pairBits left right)).embedAlong recordPlacement := rfl

private theorem recordOutcomeEffect_eq_diagonalEvent
    (left right : QubitIndex) :
    recordOutcomeEffect left right =
      diagonalEventEffect
        (fun bits : Basis EPRQubit =>
          bits q1 = left ∧ bits q4 = right) := by
  apply Effect.ext
  ext row column
  rw [recordOutcomeEffect, Effect.embedAlong_op,
    embedAlong_apply_ite]
  simp only [basisEffect_op, basisDensity, Matrix.diagonal_apply]
  change
    (if ∀ q, q ∉ Set.range recordPlacement → row q = column q then
      if (fun k => row (recordPlacement k)) =
          (fun k => column (recordPlacement k))
      then Pi.single (pairBits left right) 1
        (fun k => row (recordPlacement k))
      else 0
    else 0) =
      if row = column then
        if row q1 = left ∧ row q4 = right then 1 else 0
      else 0
  by_cases hrc : row = column
  · subst column
    rw [if_pos rfl]
    have houtside :
        ∀ q, q ∉ Set.range recordPlacement → row q = row q :=
      fun _ _ => rfl
    rw [if_pos houtside, if_pos rfl]
    have hlocal :
        (fun k => row (recordPlacement k)) = pairBits left right ↔
          row q1 = left ∧ row q4 = right := by
      constructor
      · intro h
        exact ⟨congrFun h 0, congrFun h 1⟩
      · rintro ⟨hleft, hright⟩
        funext k
        fin_cases k
        · exact hleft
        · exact hright
    by_cases hrecord : row q1 = left ∧ row q4 = right
    · rw [if_pos hrecord]
      rw [Pi.single_apply, if_pos (hlocal.mpr hrecord)]
    · rw [if_neg hrecord]
      have hne :
          (fun k => row (recordPlacement k)) ≠ pairBits left right :=
        fun h => hrecord (hlocal.mp h)
      rw [Pi.single_apply, if_neg hne]
  · rw [if_neg hrc]
    by_cases houtside :
        ∀ q, q ∉ Set.range recordPlacement → row q = column q
    · rw [if_pos houtside]
      rw [if_neg]
      intro hlocal
      apply hrc
      funext q
      by_cases hq : q ∈ Set.range recordPlacement
      · rcases hq with ⟨k, rfl⟩
        exact congrFun hlocal k
      · exact houtside q hq
    · rw [if_neg houtside]

def recordLeftPaperOneEffect : Effect EPRQubit :=
  zPlusEffect q1

def recordRightPaperOneEffect : Effect EPRQubit :=
  zPlusEffect q4

def recordJointPaperOneEffect : Effect EPRQubit :=
  recordOutcomeEffect 0 0

def finalComparisonPaperOneEffect : Effect EPRQubit :=
  zPlusEffect q1

private theorem zPlusEffect_eq_diagonalEvent (q : EPRQubit) :
    zPlusEffect q =
      diagonalEventEffect (fun bits : Basis EPRQubit => bits q = 0) := by
  apply Effect.ext
  rw [zPlusEffect_op_eq_paperBitOneProjectorAt]
  ext row column
  change paperBitOneProjectorAt q row column =
    Matrix.diagonal
      (fun bits : Basis EPRQubit => if bits q = 0 then 1 else 0)
      row column
  rw [paperBitOneProjectorAt, embedQubit_apply_ite]
  by_cases hrc : row = column
  · subst column
    rw [if_pos (fun _ _ => rfl)]
    generalize hbit : row q = bit
    fin_cases bit <;>
      simp [hbit, bitOneProjector_explicit, Matrix.diagonal]
  · rw [Matrix.diagonal_apply, if_neg hrc]
    by_cases hout : ∀ j, j ≠ q → row j = column j
    · rw [if_pos hout]
      have hbit : row q ≠ column q := by
        intro hq
        apply hrc
        funext j
        by_cases hj : j = q
        · subst j
          exact hq
        · exact hout j hj
      generalize hrow : row q = rowBit
      generalize hcol : column q = colBit
      fin_cases rowBit <;> fin_cases colBit <;>
        simp_all [bitOneProjector_explicit]
    · rw [if_neg hout]

private def fourBitsEquiv :
    Basis EPRQubit ≃
      QubitIndex × (QubitIndex × (QubitIndex × QubitIndex)) where
  toFun bits := (bits q1, bits q2, bits q3, bits q4)
  invFun bits := ![bits.1, bits.2.1, bits.2.2.1, bits.2.2.2]
  left_inv bits := by
    funext q
    fin_cases q <;> rfl
  right_inv bits := by
    rcases bits with ⟨b1, b2, b3, b4⟩
    rfl

theorem fourWireTimeThree_recordOutcome_probability
    (theta phi : ℝ) (left right : QubitIndex) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        (recordOutcomeEffect left right) =
      ((pairPureState theta phi).ket.ofLp (pairBits left right) *
        star ((pairPureState theta phi).ket.ofLp
          (pairBits left right))).re := by
  rw [fourWireTimeThreeDensity,
    recordOutcomeEffect_eq_diagonalEvent,
    pureDensity_diagonalEventEffect_probability]
  rw [fourWireTimeThreePureState_ket]
  change
    (∑ bits : Basis EPRQubit,
      if bits q1 = left ∧ bits q4 = right then
        recordedPairCoordinates (pairPureState theta phi).ket.ofLp bits *
          star (recordedPairCoordinates
            (pairPureState theta phi).ket.ofLp bits)
      else 0).re = _
  rw [← fourBitsEquiv.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  fin_cases left <;> fin_cases right <;>
    simp [recordedPairCoordinates, fourBitsEquiv, pairBits,
      q1, q2, q3, q4, Fin.sum_univ_succ]

theorem fourWireTimeThree_recordOutcome_probability_eq_pairDensity
    (theta phi : ℝ) (left right : QubitIndex) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        (recordOutcomeEffect left right) =
      bornProbability (pairDensity theta phi)
        (basisEffect (pairBits left right)) := by
  rw [fourWireTimeThree_recordOutcome_probability, pairDensity,
    pureDensity_basisEffect_probability']

private theorem fourWireTimeThree_leftPaperOne_amplitudes
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordLeftPaperOneEffect =
      ((pairPureState theta phi).ket.ofLp paperOneOne *
          star ((pairPureState theta phi).ket.ofLp paperOneOne)).re +
        ((pairPureState theta phi).ket.ofLp paperOneZero *
          star ((pairPureState theta phi).ket.ofLp paperOneZero)).re := by
  rw [fourWireTimeThreeDensity, recordLeftPaperOneEffect,
    zPlusEffect_eq_diagonalEvent,
    pureDensity_diagonalEventEffect_probability,
    fourWireTimeThreePureState_ket]
  change
    (∑ bits : Basis EPRQubit,
      if bits q1 = 0 then
        recordedPairCoordinates (pairPureState theta phi).ket.ofLp bits *
          star (recordedPairCoordinates
            (pairPureState theta phi).ket.ofLp bits)
      else 0).re = _
  rw [← fourBitsEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp [recordedPairCoordinates, fourBitsEquiv, paperOneOne, paperOneZero,
    pairBits, q1, q2, q3, q4, Fin.sum_univ_succ, Complex.add_re]

private theorem fourWireTimeThree_rightPaperOne_amplitudes
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordRightPaperOneEffect =
      ((pairPureState theta phi).ket.ofLp paperOneOne *
          star ((pairPureState theta phi).ket.ofLp paperOneOne)).re +
        ((pairPureState theta phi).ket.ofLp paperZeroOne *
          star ((pairPureState theta phi).ket.ofLp paperZeroOne)).re := by
  rw [fourWireTimeThreeDensity, recordRightPaperOneEffect,
    zPlusEffect_eq_diagonalEvent,
    pureDensity_diagonalEventEffect_probability,
    fourWireTimeThreePureState_ket]
  change
    (∑ bits : Basis EPRQubit,
      if bits q4 = 0 then
        recordedPairCoordinates (pairPureState theta phi).ket.ofLp bits *
          star (recordedPairCoordinates
            (pairPureState theta phi).ket.ofLp bits)
      else 0).re = _
  rw [← fourBitsEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp [recordedPairCoordinates, fourBitsEquiv, paperOneOne, paperZeroOne,
    pairBits, q1, q2, q3, q4, Fin.sum_univ_succ, Complex.add_re]

theorem fourWireTimeThree_leftRecord_probability (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordLeftPaperOneEffect = (1 / 2 : ℝ) := by
  rw [fourWireTimeThree_leftPaperOne_amplitudes]
  rw [← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperOneOne,
    ← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperOneZero]
  change
    bornProbability (pairDensity theta phi) (basisEffect paperOneOne) +
      bornProbability (pairDensity theta phi) (basisEffect paperOneZero) =
        (1 / 2 : ℝ)
  rw [pairDensity_paperOneOne_probability,
    pairDensity_paperOneZero_probability]
  nlinarith [Real.sin_sq_add_cos_sq ((theta - phi) / 2)]

theorem fourWireTimeThree_rightRecord_probability (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordRightPaperOneEffect = (1 / 2 : ℝ) := by
  rw [fourWireTimeThree_rightPaperOne_amplitudes]
  rw [← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperOneOne,
    ← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperZeroOne]
  change
    bornProbability (pairDensity theta phi) (basisEffect paperOneOne) +
      bornProbability (pairDensity theta phi) (basisEffect paperZeroOne) =
        (1 / 2 : ℝ)
  rw [pairDensity_paperOneOne_probability,
    pairDensity_paperZeroOne_probability]
  nlinarith [Real.sin_sq_add_cos_sq ((theta - phi) / 2)]

theorem fourWireTimeThree_leftRecord_probability_eq_pairDensity
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordLeftPaperOneEffect =
      bornProbability (pairDensity theta phi) (paperOneMarginalEffect 0) := by
  rw [fourWireTimeThree_leftRecord_probability,
    pairDensity_left_paperOne_probability]

theorem fourWireTimeThree_rightRecord_probability_eq_pairDensity
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordRightPaperOneEffect =
      bornProbability (pairDensity theta phi) (paperOneMarginalEffect 1) := by
  rw [fourWireTimeThree_rightRecord_probability,
    pairDensity_right_paperOne_probability]

theorem fourWireTimeThree_jointRecord_probability_eq_pairDensity
    (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordJointPaperOneEffect =
      bornProbability (pairDensity theta phi) jointPaperOneEffect := by
  simpa [recordJointPaperOneEffect, jointPaperOneEffect, paperOneOne] using
    fourWireTimeThree_recordOutcome_probability_eq_pairDensity
      theta phi 0 0

theorem fourWireTimeThree_jointRecord_probability (theta phi : ℝ) :
    bornProbability (fourWireTimeThreeDensity theta phi)
        recordJointPaperOneEffect =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 := by
  rw [fourWireTimeThree_jointRecord_probability_eq_pairDensity,
    pairDensity_jointPaperOne_probability]

theorem fourWireTimeFourPureState_ket (theta phi : ℝ) :
    (fourWireTimeFourPureState theta phi).ket =
      act comparisonGate
        (recordedPairKet (pairPureState theta phi).ket) := by
  change act (timeFourUnitary theta phi) (referenceKet EPRQubit) = _
  rw [timeFourUnitary, act_mul, timeThreeUnitary, act_mul,
    timeTwoPureKet_eq_liftPair, recordingLayer_liftPairKet]

private theorem finalComparisonPaperOneEffect_eq_diagonal :
    finalComparisonPaperOneEffect =
      diagonalEventEffect (fun bits : Basis EPRQubit => bits q1 = 0) := by
  exact zPlusEffect_eq_diagonalEvent q1

private theorem fourWireTimeFour_comparison_amplitudes
    (theta phi : ℝ) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect =
      ((pairPureState theta phi).ket.ofLp paperOneZero *
          star ((pairPureState theta phi).ket.ofLp paperOneZero)).re +
        ((pairPureState theta phi).ket.ofLp paperZeroOne *
          star ((pairPureState theta phi).ket.ofLp paperZeroOne)).re := by
  rw [finalComparisonPaperOneEffect_eq_diagonal,
    fourWireTimeFourDensity,
    pureDensity_diagonalEventEffect_probability,
    fourWireTimeFourPureState_ket]
  have hcoordinate (bits : Basis EPRQubit) :
      (act comparisonGate
          (recordedPairKet (pairPureState theta phi).ket)).ofLp bits =
        recordedPairCoordinates (pairPureState theta phi).ket.ofLp
          (cnotOutput q1 q4 bits) := by
    exact cnotAt_act_coordinate q1 q4 q1_ne_q4
      (recordedPairKet (pairPureState theta phi).ket) bits
  simp_rw [hcoordinate]
  rw [← fourBitsEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp [recordedPairCoordinates, fourBitsEquiv, cnotOutput, flipRaw,
    paperOneZero, paperZeroOne, pairBits, q1, q2, q3, q4,
    Fin.sum_univ_succ, Complex.add_re]

/--
Before evaluating either side trigonometrically, the final four-wire comparison probability is
the sum of the two unequal outcomes of the independently constructed pair state.
-/
theorem fourWireTimeFour_comparison_probability_eq_unequal_pair_sum
    (theta phi : ℝ) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect =
      bornProbability (pairDensity theta phi) (basisEffect paperOneZero) +
        bornProbability (pairDensity theta phi) (basisEffect paperZeroOne) := by
  rw [fourWireTimeFour_comparison_amplitudes]
  rw [← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperOneZero,
    ← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperZeroOne]
  rfl

theorem fourWireTimeFour_comparison_probability (theta phi : ℝ) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect =
      Real.sin ((theta - phi) / 2) ^ 2 := by
  rw [fourWireTimeFour_comparison_amplitudes]
  rw [← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperOneZero,
    ← pureDensity_basisEffect_probability'
      (pairPureState theta phi) paperZeroOne]
  change
    bornProbability (pairDensity theta phi) (basisEffect paperOneZero) +
      bornProbability (pairDensity theta phi) (basisEffect paperZeroOne) =
        _
  rw [pairDensity_paperOneZero_probability,
    pairDensity_paperZeroOne_probability]
  ring

theorem fourWireTimeFour_comparison_probability_eq_pairDensity
    (theta phi : ℝ) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect =
      bornProbability (pairDensity theta phi) differentEffect := by
  rw [fourWireTimeFour_comparison_probability_eq_unequal_pair_sum]
  simp only [bornProbability, bornWeight,
    differentEffect_op_eq_unequal_basis_sum, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re]

theorem fourWireTimeFour_comparison_equal_settings (theta : ℝ) :
    bornProbability (fourWireTimeFourDensity theta theta)
        finalComparisonPaperOneEffect = 0 := by
  rw [fourWireTimeFour_comparison_probability]
  simp

theorem fourWireTimeFour_comparison_pi_zero :
    bornProbability (fourWireTimeFourDensity Real.pi 0)
        finalComparisonPaperOneEffect = 1 := by
  rw [fourWireTimeFour_comparison_probability]
  norm_num [Real.sin_pi_div_two]

theorem fourWireTimeFour_comparison_relative_pi
    (theta phi : ℝ) (hrelative : theta - phi = Real.pi) :
    bornProbability (fourWireTimeFourDensity theta phi)
        finalComparisonPaperOneEffect = 1 := by
  rw [fourWireTimeFour_comparison_probability, hrelative]
  norm_num [Real.sin_pi_div_two]

end
end EPR
end Deutsch
