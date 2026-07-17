import Deutsch.EPR.Circuit
import Deutsch.Information.Dephasing

/-!
# Bounded EPR comparison invariance under record dephasing

The final comparison CNOT uses transported record `q4` as control and `q1` as target.  This module
pulls the final raw-`0`/paper-bit-`1` effect on `q1` backward through that comparison.  The resulting
effect is block diagonal at `q4`, so nonselective computational-basis dephasing of `q4` cannot
change its statistics.  The result is deliberately generic in the density immediately before the
comparison and does not claim that arbitrary decoherence mechanisms are harmless.
-/

namespace Deutsch
namespace Decoherence

open EPR Foundations Gates Information Register
open scoped BigOperators ComplexOrder Matrix MatrixOrder

noncomputable section

/-- The physical unitary channel for the final EPR comparison CNOT. -/
def eprComparisonChannel : KrausChannel EPRQubit EPRQubit Unit :=
  unitaryChannel comparisonGate comparisonGate_unitary

/-- Final `q1` paper-one selection, pulled backward through the comparison channel. -/
def eprComparisonPaperOneEffect : Effect EPRQubit :=
  eprComparisonChannel.dualEffect (zPlusEffect q1)

private theorem unitaryChannel_dualOperator_eq_heisenberg
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Operator Q) (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (A : Operator Q) :
    (unitaryChannel U hU).dualOperator A = heisenberg U A := by
  simp only [unitaryChannel, KrausChannel.dualOperator,
    Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem comparisonGate_heisenberg_q1_z :
    heisenberg comparisonGate (zAt q1) = -(zAt q1 * zAt q4) := by
  simpa [comparisonGate] using
    cnotAt_conjugates_target_z q1 q4 q1_ne_q4

/-- Exact operator of the comparison effect before the final CNOT. -/
theorem eprComparisonPaperOneEffect_op :
    eprComparisonPaperOneEffect.op =
      (2 : ℂ)⁻¹ • (1 - zAt q1 * zAt q4) := by
  change eprComparisonChannel.dualOperator (zPlusEffect q1).op = _
  rw [eprComparisonChannel,
    unitaryChannel_dualOperator_eq_heisenberg,
    zPlusEffect_op,
    heisenberg_smul,
    heisenberg_add]
  rw [heisenberg_one_of_unitary comparisonGate comparisonGate_unitary,
    comparisonGate_heisenberg_q1_z]
  module

private theorem eprComparisonPaperOneEffect_cross_q4_zero
    (x y : Basis EPRQubit) (hxy : x q4 ≠ y q4) :
    eprComparisonPaperOneEffect.op x y = 0 := by
  rw [eprComparisonPaperOneEffect_op]
  have hne : x ≠ y := by
    intro h
    exact hxy (congrFun h q4)
  have hproduct : (zAt q1 * zAt q4) x y = 0 := by
    rw [zAt, zAt,
      embedQubit_mul_embedQubit_apply_of_ne q1_ne_q4 pauliZ pauliZ]
    split_ifs
    · generalize hx : x q4 = xb
      generalize hy : y q4 = yb
      fin_cases xb <;> fin_cases yb <;> simp_all [pauliZ]
    · rfl
  simp [hne, hproduct]

/-- The pulled-back final comparison effect is fixed by `q4` coordinate dephasing. -/
theorem coordinateDephasing_q4_fixes_eprComparisonPaperOneEffect :
    (coordinateDephasing q4).dualEffect eprComparisonPaperOneEffect =
      eprComparisonPaperOneEffect := by
  apply Effect.ext
  change (coordinateDephasing q4).dualOperator eprComparisonPaperOneEffect.op =
    eprComparisonPaperOneEffect.op
  rw [coordinateDephasing_dualOperator,
    coordinateDephasing_fixes_operator_iff]
  exact eprComparisonPaperOneEffect_cross_q4_zero

/-- Dephasing `q4` once preserves the already-pulled-back comparison statistic. -/
theorem coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability
    (rho : Density EPRQubit) :
    bornProbability ((coordinateDephasing q4).mapDensity rho)
        eprComparisonPaperOneEffect =
      bornProbability rho eprComparisonPaperOneEffect := by
  rw [(coordinateDephasing q4).bornProbability_mapDensity,
    coordinateDephasing_q4_fixes_eprComparisonPaperOneEffect]

/-- Every finite repetition of the same `q4` dephasing preserves the comparison statistic. -/
theorem coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability_iterate
    (rho : Density EPRQubit) (n : Nat) :
    bornProbability (((coordinateDephasing q4).mapDensity)^[n] rho)
        eprComparisonPaperOneEffect =
      bornProbability rho eprComparisonPaperOneEffect := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability, ih]

/--
Bounded C34 statement: for every density immediately before the final comparison, inserting one
nonselective computational-basis dephasing of transported record `q4` leaves the final `q1`
paper-one probability unchanged.
-/
theorem epr_c34_q4_dephasing_before_comparison
    (rho : Density EPRQubit) :
    bornProbability
        (eprComparisonChannel.mapDensity
          ((coordinateDephasing q4).mapDensity rho))
        (zPlusEffect q1) =
      bornProbability (eprComparisonChannel.mapDensity rho)
        (zPlusEffect q1) := by
  rw [eprComparisonChannel.bornProbability_mapDensity,
    eprComparisonChannel.bornProbability_mapDensity]
  change bornProbability ((coordinateDephasing q4).mapDensity rho)
      eprComparisonPaperOneEffect =
    bornProbability rho eprComparisonPaperOneEffect
  exact coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability rho

/-- The same bounded C34 result for any finite number of repeated `q4` dephasings. -/
theorem epr_c34_q4_dephasing_before_comparison_iterate
    (rho : Density EPRQubit) (n : Nat) :
    bornProbability
        (eprComparisonChannel.mapDensity
          (((coordinateDephasing q4).mapDensity)^[n] rho))
        (zPlusEffect q1) =
      bornProbability (eprComparisonChannel.mapDensity rho)
        (zPlusEffect q1) := by
  rw [eprComparisonChannel.bornProbability_mapDensity,
    eprComparisonChannel.bornProbability_mapDensity]
  change bornProbability (((coordinateDephasing q4).mapDensity)^[n] rho)
      eprComparisonPaperOneEffect =
    bornProbability rho eprComparisonPaperOneEffect
  exact
    coordinateDephasing_q4_preserves_eprComparisonPaperOneProbability_iterate rho n

end
end Decoherence
end Deutsch
