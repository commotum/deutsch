import Deutsch.EPR.Circuit
import Deutsch.EPR.Statistics
import Deutsch.Information.Qubit

/-!
# Paper façade: the EPR experiment

Source-shaped entries for Equations (22)--(27).  The literal four-wire comparison result in
Equation (28) is supplied by the dedicated record-statistics bridge and is intentionally not
duplicated here.
-/

namespace Deutsch
namespace Paper

open Foundations Information Register
open scoped Matrix

noncomputable section

/--
Equation (22): the source-labelled EPR ket agrees with the exact inverse-Bell preparation up to
the displayed global phase.
-/
theorem equation22 :
    EPR.equation22Ket = (-Complex.I) • EPR.pairKet :=
  EPR.equation22Ket_eq_globalPhase

/-- Equation (23): both descriptors of the inverse-Bell EPR resource. -/
theorem equation23 :
    EPR.timeOneDescriptors EPR.q2 =
        { x := xAt EPR.q2
          y := -(yAt EPR.q2 * xAt EPR.q3)
          z := -(zAt EPR.q2 * xAt EPR.q3) } ∧
      EPR.timeOneDescriptors EPR.q3 =
        { x := xAt EPR.q2 * zAt EPR.q3
          y := -(xAt EPR.q2 * yAt EPR.q3)
          z := xAt EPR.q3 } :=
  ⟨EPR.equation23_q2, EPR.equation23_q3⟩

/-- Equation (24): the two record wires are unchanged through the EPR setting layer. -/
theorem equation24 (theta phi : ℝ) :
    EPR.timeTwoDescriptors theta phi EPR.q1 = Descriptor.initial EPR.q1 ∧
      EPR.timeTwoDescriptors theta phi EPR.q4 = Descriptor.initial EPR.q4 :=
  ⟨EPR.equation24_q1 theta phi, EPR.equation24_q4 theta phi⟩

/-- Equation (25): both setting-dependent EPR descriptors at time two. -/
theorem equation25 (theta phi : ℝ) :
    EPR.timeTwoDescriptors theta phi EPR.q2 =
        { x := xAt EPR.q2
          y := (theta.cos : ℂ) • (-(yAt EPR.q2 * xAt EPR.q3)) -
            (theta.sin : ℂ) • (-(zAt EPR.q2 * xAt EPR.q3))
          z := (theta.sin : ℂ) • (-(yAt EPR.q2 * xAt EPR.q3)) +
            (theta.cos : ℂ) • (-(zAt EPR.q2 * xAt EPR.q3)) } ∧
      EPR.timeTwoDescriptors theta phi EPR.q3 =
        { x := xAt EPR.q2 * zAt EPR.q3
          y := (phi.cos : ℂ) • (-(xAt EPR.q2 * yAt EPR.q3)) -
            (phi.sin : ℂ) • xAt EPR.q3
          z := (phi.sin : ℂ) • (-(xAt EPR.q2 * yAt EPR.q3)) +
            (phi.cos : ℂ) • xAt EPR.q3 } :=
  ⟨EPR.equation25_q2 theta phi, EPR.equation25_q3 theta phi⟩

private def selectedCoordinate (q : Fin 2) :
    {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))} :=
  ⟨q, Finset.mem_singleton_self q⟩

private theorem singletonMaximallyMixed_op_eq_smul_one (q : Fin 2) :
    (singletonMaximallyMixed q).op =
      ((2 : ℂ)⁻¹) •
        (1 : Operator {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))}) := by
  ext i j
  simp [singletonMaximallyMixed, Matrix.diagonal_apply, Matrix.one_apply]

private def selectedBasisEquiv (q : Fin 2) :
    Basis {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))} ≃ QubitIndex where
  toFun bits := bits (selectedCoordinate q)
  invFun bit := fun _ => bit
  left_inv bits := by
    funext r
    apply congrArg bits
    apply Subtype.ext
    exact (Finset.mem_singleton.mp r.2).symm
  right_inv _ := rfl

private theorem selected_embedQubit_apply (q : Fin 2) (A : QubitMatrix)
    (left right : QubitIndex) :
    embedQubit (selectedCoordinate q) A
        ((selectedBasisEquiv q).symm left)
        ((selectedBasisEquiv q).symm right) =
      A left right := by
  rw [embedQubit_apply_ite, if_pos]
  · rfl
  · intro r hr
    apply False.elim
    apply hr
    apply Subtype.ext
    exact Finset.mem_singleton.mp r.2

private theorem singleton_trace_x (q : Fin 2) :
    Matrix.trace (xAt (selectedCoordinate q)) = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [← (selectedBasisEquiv q).symm.sum_comp]
  simp [xAt, selected_embedQubit_apply, pauliX]

private theorem singleton_trace_y (q : Fin 2) :
    Matrix.trace (yAt (selectedCoordinate q)) = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [← (selectedBasisEquiv q).symm.sum_comp]
  simp [yAt, selected_embedQubit_apply, pauliY]

private theorem singleton_trace_z (q : Fin 2) :
    Matrix.trace (zAt (selectedCoordinate q)) = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [← (selectedBasisEquiv q).symm.sum_comp]
  simp [zAt, selected_embedQubit_apply, pauliZ]

/--
Equation (26): each time-two EPR qubit is maximally mixed and its three local Pauli moments
vanish.  Quantifying over `Fin 2` packages the two displayed qubits without privileging either.
-/
theorem equation26 (theta phi : ℝ) :
    ∀ q : Fin 2,
      (EPR.pairDensity theta phi).reduce ({q} : Finset (Fin 2)) =
          singletonMaximallyMixed q ∧
        densityExpectation
            ((EPR.pairDensity theta phi).reduce ({q} : Finset (Fin 2)))
            (xAt (selectedCoordinate q)) = 0 ∧
        densityExpectation
            ((EPR.pairDensity theta phi).reduce ({q} : Finset (Fin 2)))
            (yAt (selectedCoordinate q)) = 0 ∧
        densityExpectation
            ((EPR.pairDensity theta phi).reduce ({q} : Finset (Fin 2)))
            (zAt (selectedCoordinate q)) = 0 := by
  intro q
  constructor
  · exact EPR.pairDensity_reduce_singleton theta phi q
  rw [EPR.pairDensity_reduce_singleton]
  constructor
  · rw [densityExpectation, singletonMaximallyMixed_op_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, singleton_trace_x,
      smul_zero]
  constructor
  · rw [densityExpectation, singletonMaximallyMixed_op_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, singleton_trace_y,
      smul_zero]
  · rw [densityExpectation, singletonMaximallyMixed_op_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, singleton_trace_z,
      smul_zero]

/-- Equation (27): all four descriptors after the two local coherent records. -/
theorem equation27 (theta phi : ℝ) :
    EPR.timeThreeDescriptors theta phi EPR.q1 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q1).x
          y := -((EPR.timeTwoDescriptors theta phi EPR.q1).y *
            (EPR.timeTwoDescriptors theta phi EPR.q2).z)
          z := -((EPR.timeTwoDescriptors theta phi EPR.q1).z *
            (EPR.timeTwoDescriptors theta phi EPR.q2).z) } ∧
      EPR.timeThreeDescriptors theta phi EPR.q2 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q1).x *
            (EPR.timeTwoDescriptors theta phi EPR.q2).x
          y := (EPR.timeTwoDescriptors theta phi EPR.q1).x *
            (EPR.timeTwoDescriptors theta phi EPR.q2).y
          z := (EPR.timeTwoDescriptors theta phi EPR.q2).z } ∧
      EPR.timeThreeDescriptors theta phi EPR.q3 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q4).x *
            (EPR.timeTwoDescriptors theta phi EPR.q3).x
          y := (EPR.timeTwoDescriptors theta phi EPR.q4).x *
            (EPR.timeTwoDescriptors theta phi EPR.q3).y
          z := (EPR.timeTwoDescriptors theta phi EPR.q3).z } ∧
      EPR.timeThreeDescriptors theta phi EPR.q4 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q4).x
          y := -((EPR.timeTwoDescriptors theta phi EPR.q4).y *
            (EPR.timeTwoDescriptors theta phi EPR.q3).z)
          z := -((EPR.timeTwoDescriptors theta phi EPR.q4).z *
            (EPR.timeTwoDescriptors theta phi EPR.q3).z) } := by
  exact ⟨EPR.equation27_q1 theta phi, EPR.equation27_q2 theta phi,
    EPR.equation27_q3 theta phi, EPR.equation27_q4 theta phi⟩

end
end Paper
end Deutsch
