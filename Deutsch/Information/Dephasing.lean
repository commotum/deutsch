import Deutsch.Information.Channel
import Deutsch.Information.Qubit
import Deutsch.Register.Pauli
import Deutsch.Gates.CNOT
import Mathlib.Tactic.FinCases

namespace Deutsch
namespace Information

open Foundations Register Gates
open scoped ComplexOrder Matrix MatrixOrder BigOperators

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The two computational-basis projectors at coordinate `q`, indexed by raw bit. -/
def coordinateDephasingKraus (q : Q) (b : QubitIndex) : Operator Q :=
  if b = 0 then paperBitOneProjectorAt q else paperBitZeroProjectorAt q

theorem coordinateDephasingKraus_zero (q : Q) :
    coordinateDephasingKraus q 0 = paperBitOneProjectorAt q := by
  simp [coordinateDephasingKraus]

theorem coordinateDephasingKraus_one (q : Q) :
    coordinateDephasingKraus q 1 = paperBitZeroProjectorAt q := by
  simp [coordinateDephasingKraus]

theorem coordinateDephasingKraus_isHermitian (q : Q) (b : QubitIndex) :
    (coordinateDephasingKraus q b).IsHermitian := by
  fin_cases b
  · change (paperBitOneProjectorAt q).IsHermitian
    exact paperBitOneProjectorAt_isHermitian q
  · change (paperBitZeroProjectorAt q).IsHermitian
    exact paperBitZeroProjectorAt_isHermitian q

theorem coordinateDephasingKraus_mul_self (q : Q) (b : QubitIndex) :
    coordinateDephasingKraus q b * coordinateDephasingKraus q b =
      coordinateDephasingKraus q b := by
  fin_cases b
  · change paperBitOneProjectorAt q * paperBitOneProjectorAt q =
      paperBitOneProjectorAt q
    exact paperBitOneProjectorAt_mul_self q
  · change paperBitZeroProjectorAt q * paperBitZeroProjectorAt q =
      paperBitZeroProjectorAt q
    exact paperBitZeroProjectorAt_mul_self q

private theorem paperBitOneProjectorAt_eq_diagonal (q : Q) :
    paperBitOneProjectorAt q =
      Matrix.diagonal (fun x : Basis Q => if x q = 0 then (1 : ℂ) else 0) := by
  ext a b
  rw [paperBitOneProjectorAt, embedQubit_apply_ite]
  by_cases hab : a = b
  · subst b
    rw [if_pos (fun _ _ ↦ rfl)]
    simp only [Matrix.diagonal_apply_eq]
    rw [bitOneProjector_explicit]
    generalize ha : a q = aq
    fin_cases aq <;> simp_all
  · rw [Matrix.diagonal_apply_ne _ hab]
    by_cases hout : ∀ j, j ≠ q → a j = b j
    · rw [if_pos hout, bitOneProjector_explicit]
      have hq : a q ≠ b q := by
        intro h
        apply hab
        funext r
        by_cases hr : r = q
        · subst r
          exact h
        · exact hout r hr
      generalize ha : a q = aq
      generalize hb : b q = bq
      fin_cases aq <;> fin_cases bq <;> simp_all
    · rw [if_neg hout]

private theorem paperBitZeroProjectorAt_eq_diagonal (q : Q) :
    paperBitZeroProjectorAt q =
      Matrix.diagonal (fun x : Basis Q => if x q = 1 then (1 : ℂ) else 0) := by
  ext a b
  rw [paperBitZeroProjectorAt, embedQubit_apply_ite]
  by_cases hab : a = b
  · subst b
    rw [if_pos (fun _ _ ↦ rfl)]
    simp only [Matrix.diagonal_apply_eq]
    rw [bitZeroProjector_explicit]
    generalize ha : a q = aq
    fin_cases aq <;> simp_all
  · rw [Matrix.diagonal_apply_ne _ hab]
    by_cases hout : ∀ j, j ≠ q → a j = b j
    · rw [if_pos hout, bitZeroProjector_explicit]
      have hq : a q ≠ b q := by
        intro h
        apply hab
        funext r
        by_cases hr : r = q
        · subst r
          exact h
        · exact hout r hr
      generalize ha : a q = aq
      generalize hb : b q = bq
      fin_cases aq <;> fin_cases bq <;> simp_all
    · rw [if_neg hout]

theorem coordinateDephasingKraus_eq_diagonal (q : Q) (b : QubitIndex) :
    coordinateDephasingKraus q b =
      Matrix.diagonal (fun x : Basis Q => if x q = b then (1 : ℂ) else 0) := by
  by_cases hb : b = 0
  · subst b
    rw [coordinateDephasingKraus_zero]
    exact paperBitOneProjectorAt_eq_diagonal q
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
    subst b
    rw [coordinateDephasingKraus_one]
    exact paperBitZeroProjectorAt_eq_diagonal q

/-- Nonselective computational-basis measurement at one named coordinate. -/
def coordinateDephasing (q : Q) : KrausChannel Q Q QubitIndex where
  kraus := coordinateDephasingKraus q
  complete := by
    rw [Fin.sum_univ_two]
    simp only [coordinateDephasingKraus_zero, coordinateDephasingKraus_one]
    rw [(paperBitOneProjectorAt_isHermitian q).eq,
      (paperBitZeroProjectorAt_isHermitian q).eq,
      paperBitOneProjectorAt_mul_self,
      paperBitZeroProjectorAt_mul_self,
      paperBitProjectorAt_sum]

/-- Exact two-projector operator action. -/
theorem coordinateDephasing_mapOperator (q : Q) (A : Operator Q) :
    (coordinateDephasing q).mapOperator A =
      paperBitOneProjectorAt q * A * paperBitOneProjectorAt q +
      paperBitZeroProjectorAt q * A * paperBitZeroProjectorAt q := by
  rw [KrausChannel.mapOperator, Fin.sum_univ_two]
  simp only [coordinateDephasing, coordinateDephasingKraus_zero,
    coordinateDephasingKraus_one]
  rw [(paperBitOneProjectorAt_isHermitian q).eq,
    (paperBitZeroProjectorAt_isHermitian q).eq]

/-- Matrix-entry action: retain exactly the coherences whose two basis words agree at `q`. -/
theorem coordinateDephasing_mapOperator_apply (q : Q) (A : Operator Q)
    (x y : Basis Q) :
    (coordinateDephasing q).mapOperator A x y =
      if x q = y q then A x y else 0 := by
  rw [coordinateDephasing_mapOperator,
    ← coordinateDephasingKraus_zero q,
    ← coordinateDephasingKraus_one q,
    coordinateDephasingKraus_eq_diagonal,
    coordinateDephasingKraus_eq_diagonal]
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  generalize hx : x q = xb
  generalize hy : y q = yb
  fin_cases xb <;> fin_cases yb <;> simp

/-- The existing generic channel theorem gives trace preservation. -/
theorem coordinateDephasing_trace (q : Q) (A : Operator Q) :
    Matrix.trace ((coordinateDephasing q).mapOperator A) = Matrix.trace A :=
  (coordinateDephasing q).trace_mapOperator A

/-- Off-diagonal coherence across the selected coordinate is exactly erased. -/
theorem coordinateDephasing_kills_coherence (q : Q) (A : Operator Q)
    (x y : Basis Q) (hxy : x q ≠ y q) :
    (coordinateDephasing q).mapOperator A x y = 0 := by
  rw [coordinateDephasing_mapOperator_apply, if_neg hxy]

/--
Coordinate dephasing fixes exactly the operators that have no matrix entries between the two raw
bit sectors at the selected coordinate.
-/
theorem coordinateDephasing_fixes_operator_iff (q : Q) (A : Operator Q) :
    (coordinateDephasing q).mapOperator A = A ↔
      ∀ x y : Basis Q, x q ≠ y q → A x y = 0 := by
  constructor
  · intro h x y hxy
    have hentry := congrArg (fun B : Operator Q ↦ B x y) h
    rw [coordinateDephasing_mapOperator_apply, if_neg hxy] at hentry
    exact hentry.symm
  · intro h
    ext x y
    rw [coordinateDephasing_mapOperator_apply]
    by_cases hxy : x q = y q
    · rw [if_pos hxy]
    · rw [if_neg hxy, h x y hxy]

/-- Every computational-basis density is fixed. -/
theorem coordinateDephasing_map_basisDensity (q : Q) (bits : Basis Q) :
    (coordinateDephasing q).mapDensity (basisDensity bits) = basisDensity bits := by
  apply Density.ext
  ext x y
  change (coordinateDephasing q).mapOperator (basisDensity bits).op x y = _
  rw [coordinateDephasing_mapOperator_apply]
  by_cases hq : x q = y q
  · rw [if_pos hq]
  · rw [if_neg hq]
    have hxy : x ≠ y := by
      intro h
      exact hq (congrFun h q)
    simp [basisDensity, hxy]

/-- Dephasing is idempotent on every operator. -/
theorem coordinateDephasing_mapOperator_idempotent (q : Q) (A : Operator Q) :
    (coordinateDephasing q).mapOperator
        ((coordinateDephasing q).mapOperator A) =
      (coordinateDephasing q).mapOperator A := by
  ext x y
  rw [coordinateDephasing_mapOperator_apply,
    coordinateDephasing_mapOperator_apply]
  by_cases hxy : x q = y q <;> simp [hxy]

/-- Dephasing is idempotent on density states. -/
theorem coordinateDephasing_mapDensity_idempotent (q : Q) (rho : Density Q) :
    (coordinateDephasing q).mapDensity
        ((coordinateDephasing q).mapDensity rho) =
      (coordinateDephasing q).mapDensity rho := by
  apply Density.ext
  exact coordinateDephasing_mapOperator_idempotent q rho.op

/-- The raw-`0`/paper-bit-`1` projector is fixed by dephasing in the same basis. -/
theorem coordinateDephasing_map_paperBitOneProjectorAt (q : Q) :
    (coordinateDephasing q).mapOperator (paperBitOneProjectorAt q) =
      paperBitOneProjectorAt q := by
  rw [coordinateDephasing_fixes_operator_iff]
  intro x y hxy
  rw [paperBitOneProjectorAt_eq_diagonal]
  have hne : x ≠ y := by
    intro h
    exact hxy (congrFun h q)
  simp [hne]

/-- The selected coordinate's Pauli-X coherence is killed. -/
theorem coordinateDephasing_map_xAt (q : Q) :
    (coordinateDephasing q).mapOperator (xAt q) = 0 := by
  ext x y
  rw [coordinateDephasing_mapOperator_apply]
  by_cases hxy : x q = y q
  · rw [if_pos hxy, xAt, embedQubit_apply_ite]
    split_ifs
    · generalize hx : x q = xb
      generalize hy : y q = yb
      fin_cases xb <;> fin_cases yb <;> simp_all [pauliX]
    · rfl
  · rw [if_neg hxy]
    rfl

/-- For these Hermitian Kraus projectors, Schrödinger and dual operator actions coincide. -/
theorem coordinateDephasing_dualOperator (q : Q) (A : Operator Q) :
    (coordinateDephasing q).dualOperator A =
      (coordinateDephasing q).mapOperator A := by
  rw [KrausChannel.dualOperator, KrausChannel.mapOperator]
  apply Finset.sum_congr rfl
  intro b _
  change (coordinateDephasingKraus q b)ᴴ * A *
      coordinateDephasingKraus q b =
    coordinateDephasingKraus q b * A *
      (coordinateDephasingKraus q b)ᴴ
  rw [(coordinateDephasingKraus_isHermitian q b).eq]

theorem coordinateDephasing_dual_xAt (q : Q) :
    (coordinateDephasing q).dualOperator (xAt q) = 0 := by
  rw [coordinateDephasing_dualOperator, coordinateDephasing_map_xAt]

/-- The selected raw-`0`/paper-bit-`1` Z effect is a dual fixed point. -/
theorem coordinateDephasing_dual_zPlusEffect (q : Q) :
    (coordinateDephasing q).dualEffect (zPlusEffect q) = zPlusEffect q := by
  apply Effect.ext
  change (coordinateDephasing q).dualOperator (zPlusEffect q).op =
    (zPlusEffect q).op
  rw [zPlusEffect_op_eq_paperBitOneProjectorAt,
    coordinateDephasing_dualOperator,
    coordinateDephasing_map_paperBitOneProjectorAt]

/-- One application of coordinate dephasing preserves the selected Z-effect statistic. -/
theorem coordinateDephasing_preserves_zPlusProbability (q : Q) (rho : Density Q) :
    bornProbability ((coordinateDephasing q).mapDensity rho) (zPlusEffect q) =
      bornProbability rho (zPlusEffect q) := by
  rw [(coordinateDephasing q).bornProbability_mapDensity,
    coordinateDephasing_dual_zPlusEffect]

/-- Any finite repetition of the same dephasing preserves the selected Z-effect statistic. -/
theorem coordinateDephasing_preserves_zPlusProbability_iterate
    (q : Q) (rho : Density Q) (n : Nat) :
    bornProbability (((coordinateDephasing q).mapDensity)^[n] rho)
        (zPlusEffect q) =
      bornProbability rho (zPlusEffect q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        coordinateDephasing_preserves_zPlusProbability, ih]

/-- A concrete wrong-basis witness: the `X=+1` effect is changed by Z dephasing. -/
theorem coordinateDephasing_changes_xPlusEffect (q : Q) :
    (coordinateDephasing q).dualEffect (xPlusEffect q) ≠ xPlusEffect q := by
  intro h
  have hop := congrArg Effect.op h
  change (coordinateDephasing q).dualOperator (xPlusEffect q).op =
    (xPlusEffect q).op at hop
  rw [coordinateDephasing_dualOperator] at hop
  let x : Basis Q := fun _ ↦ 0
  let y : Basis Q := Function.update x q 1
  have hxy : x q ≠ y q := by
    simp [x, y]
  have hentry := congrArg (fun A : Operator Q ↦ A x y) hop
  rw [coordinateDephasing_mapOperator_apply, if_neg hxy] at hentry
  have hne : x ≠ y := by
    intro hEq
    exact hxy (congrFun hEq q)
  have houtside : ∀ j, j ≠ q → x j = y j := by
    intro j hj
    simp [x, y, Function.update_of_ne hj]
  have hxentry : xAt q x y = 1 := by
    rw [xAt, embedQubit_apply_ite, if_pos houtside]
    simp [x, y, pauliX]
  rw [xPlusEffect_op, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, if_neg hne, hxentry] at hentry
  norm_num at hentry

/-! ## A concrete classical bit-flip failure -/

/-- The one-qubit computational-basis assignment with supplied raw matrix index `b`. -/
def oneQubitRawAssignment (b : QubitIndex) : Basis (Fin 1) :=
  fun _ ↦ b

/-- On one qubit, the selected Z effect is exactly the raw-`0` basis effect. -/
theorem zPlusEffect_singleton_eq_basisEffect_raw_zero :
    zPlusEffect (0 : Fin 1) = basisEffect (oneQubitRawAssignment 0) := by
  apply Effect.ext
  rw [zPlusEffect_op_eq_paperBitOneProjectorAt, basisEffect_op,
    paperBitOneProjectorAt_eq_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, basisDensity]
    generalize hx : x 0 = xb
    fin_cases xb
    · have heq : x = oneQubitRawAssignment 0 := by
        funext i
        fin_cases i
        exact hx
      subst x
      simp
    · have hne : x ≠ oneQubitRawAssignment 0 := by
        intro heq
        have := congrFun heq 0
        simp [oneQubitRawAssignment, hx] at this
      simp [Pi.single, hne]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    simp [basisDensity, Matrix.diagonal_apply_ne _ hxy]

/-- The raw classical flip sends raw `0` (paper bit `1`) to raw `1` (paper bit `0`). -/
theorem classicalBitFlip_raw_zero_eq_raw_one :
    oneQubitRawAssignment (flipRaw 0) = oneQubitRawAssignment 1 := by
  rfl

/--
A classical bit flip therefore changes the selected Z probability from `1` to `0`.  This statement
keeps the project's reversed convention explicit: raw `0` is paper bit `1`, while raw `1` is paper
bit `0`.
-/
theorem classicalBitFlip_changes_zPlusProbability :
    bornProbability (basisDensity (oneQubitRawAssignment 0))
          (zPlusEffect (0 : Fin 1)) = 1 ∧
      bornProbability
          (basisDensity (oneQubitRawAssignment (flipRaw 0)))
          (zPlusEffect (0 : Fin 1)) = 0 := by
  rw [zPlusEffect_singleton_eq_basisEffect_raw_zero,
    basisDensity_basisEffect_probability,
    basisDensity_basisEffect_probability]
  have hne :
      oneQubitRawAssignment (flipRaw 0) ≠ oneQubitRawAssignment 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [oneQubitRawAssignment, flipRaw] at h0
  simp only [ite_true, if_neg hne]
  exact ⟨True.intro, True.intro⟩

/-! ## A one-qubit Stinespring realization by a CNOT environment -/

/-- Joint assignment with system at coordinate `0` and environment at coordinate `1`. -/
def systemEnvironmentBits (system environment : QubitIndex) : Basis (Fin 2) :=
  ![system, environment]

/-- The explicit paper-zero state supplied for the one-qubit environment. -/
def cnotEnvironmentState : Density (Fin 1) :=
  referenceDensity (Fin 1)

/-- Raw computational index of the supplied paper-zero environment state. -/
def cnotEnvironmentInputBit : QubitIndex :=
  paperZeroAssignment (Fin 1) 0

@[simp]
theorem cnotEnvironmentInputBit_eq_one : cnotEnvironmentInputBit = 1 := rfl

/-- The named environment state is the basis density selected by its named input bit. -/
theorem cnotEnvironmentState_eq_basisDensity :
    cnotEnvironmentState =
      basisDensity (fun _ : Fin 1 ↦ cnotEnvironmentInputBit) := by
  rfl

/-- CNOT coupling with system `0` controlling environment target `1`. -/
def cnotEnvironmentCoupling : Operator (Fin 2) :=
  cnotAt (1 : Fin 2) (0 : Fin 2) (by decide)

theorem cnotEnvironmentCoupling_unitary :
    cnotEnvironmentCoupling ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact cnotAt_unitary (1 : Fin 2) (0 : Fin 2) (by decide)

/--
The environment-output matrix element of a CNOT whose target is environment `1`, whose control is
system `0`, and whose environment input is paper zero (raw index `1`).
-/
def cnotEnvironmentKraus (environmentOutput : QubitIndex) :
    Matrix (Basis (Fin 1)) (Basis (Fin 1)) ℂ :=
  fun systemOutput systemInput ↦
    cnotEnvironmentCoupling
      (systemEnvironmentBits (systemOutput 0) environmentOutput)
      (systemEnvironmentBits (systemInput 0) cnotEnvironmentInputBit)

theorem cnotOutput_systemEnvironmentBits (system : QubitIndex) :
    cnotOutput (1 : Fin 2) (0 : Fin 2)
        (systemEnvironmentBits system cnotEnvironmentInputBit) =
      systemEnvironmentBits system (if system = 0 then 0 else 1) := by
  rw [cnotEnvironmentInputBit_eq_one]
  funext i
  fin_cases i <;> fin_cases system <;>
    simp [systemEnvironmentBits, cnotOutput, flipRaw]

/-- The CNOT-environment matrix elements are exactly the two computational projectors. -/
theorem cnotEnvironmentKraus_eq_coordinateDephasingKraus
    (environmentOutput : QubitIndex) :
    cnotEnvironmentKraus environmentOutput =
      coordinateDephasingKraus (0 : Fin 1) environmentOutput := by
  ext systemOutput systemInput
  rw [cnotEnvironmentKraus, cnotEnvironmentCoupling, cnotAt_apply,
    cnotOutput_systemEnvironmentBits]
  by_cases henv : environmentOutput = 0
  · subst environmentOutput
    rw [coordinateDephasingKraus_zero,
      paperBitOneProjectorAt, embedQubit_apply_ite]
    generalize hout : systemOutput 0 = outputBit
    generalize hin : systemInput 0 = inputBit
    fin_cases outputBit <;> fin_cases inputBit <;>
      simp_all [systemEnvironmentBits, bitOneProjector_explicit]
  · have henvOne : environmentOutput = 1 :=
      Fin.eq_one_of_ne_zero environmentOutput henv
    subst environmentOutput
    rw [coordinateDephasingKraus_one,
      paperBitZeroProjectorAt, embedQubit_apply_ite]
    generalize hout : systemOutput 0 = outputBit
    generalize hin : systemInput 0 = inputBit
    fin_cases outputBit <;> fin_cases inputBit <;>
      simp_all [systemEnvironmentBits, bitZeroProjector_explicit]

/-- The channel obtained by summing over both environment outputs. -/
def cnotEnvironmentDephasing :
    KrausChannel (Fin 1) (Fin 1) QubitIndex where
  kraus := cnotEnvironmentKraus
  complete := by
    simp_rw [cnotEnvironmentKraus_eq_coordinateDephasingKraus]
    exact (coordinateDephasing (0 : Fin 1)).complete

/-- The CNOT dilation and the projector-sum dephasing channel have identical operator action. -/
theorem cnotEnvironmentDephasing_mapOperator (A : Operator (Fin 1)) :
    cnotEnvironmentDephasing.mapOperator A =
      (coordinateDephasing (0 : Fin 1)).mapOperator A := by
  rw [KrausChannel.mapOperator, KrausChannel.mapOperator]
  apply Finset.sum_congr rfl
  intro environmentOutput _
  change cnotEnvironmentKraus environmentOutput * A *
      (cnotEnvironmentKraus environmentOutput)ᴴ =
    coordinateDephasingKraus 0 environmentOutput * A *
      (coordinateDephasingKraus 0 environmentOutput)ᴴ
  rw [cnotEnvironmentKraus_eq_coordinateDephasingKraus]

/-- Consequently the two realizations agree on every one-qubit density state. -/
theorem cnotEnvironmentDephasing_mapDensity (rho : Density (Fin 1)) :
    cnotEnvironmentDephasing.mapDensity rho =
      (coordinateDephasing (0 : Fin 1)).mapDensity rho := by
  apply Density.ext
  exact cnotEnvironmentDephasing_mapOperator rho.op


end
end Information
end Deutsch
