import Deutsch.Register.Pauli
import Deutsch.Register.State
import Mathlib.Tactic

/-!
# Register API verification

Focused Stage 3 tests for finite register size, paper-bit conventions, coordinate placement,
support, state preparation, and Heisenberg eigenvector transport.
-/

namespace DeutschTests
namespace RegisterVerification

open Deutsch Deutsch.Foundations Deutsch.Register
open scoped Matrix Kronecker

noncomputable section

/-! ## Register sizes and the paper-zero reference state -/

theorem card_basis_one : Fintype.card (Basis (Fin 1)) = 2 := by
  rw [card_basis]
  norm_num

theorem card_basis_two : Fintype.card (Basis (Fin 2)) = 4 := by
  rw [card_basis]
  norm_num

theorem card_basis_three : Fintype.card (Basis (Fin 3)) = 8 := by
  rw [card_basis]
  norm_num

theorem paper_zero_is_raw_one_on_three_qubits (q : Fin 3) :
    paperZeroAssignment (Fin 3) q = (1 : QubitIndex) := by
  rfl

theorem paper_zero_is_not_raw_zero :
    paperZeroAssignment (Fin 3) (0 : Fin 3) ≠ (0 : QubitIndex) := by
  decide

theorem referenceKet_three_qubits_normalized :
    ‖referenceKet (Fin 3)‖ = 1 := by
  exact norm_referenceKet

theorem identity_acts_on_reference :
    act (1 : Operator (Fin 3)) (referenceKet (Fin 3)) = referenceKet (Fin 3) := by
  exact act_one _

/-- Regression check for the public arbitrary-pure-state standardization theorem. -/
theorem every_pure_three_qubit_state_has_a_unitary_preparation
    (psi : PureState (Fin 3)) :
    exists U : Operator (Fin 3),
      U ∈ Matrix.unitaryGroup (Basis (Fin 3)) Complex ∧
        act U (referenceKet (Fin 3)) = psi.ket := by
  exact psi.exists_unitary_preparation

/-! ## Two-factor coordinate order -/

theorem coordinate_zero_is_left_kronecker_factor (A : QubitMatrix) :
    Matrix.reindexRingEquiv Complex twoQubitBasisEquiv
        (embedQubit (0 : Fin 2) A) =
      A ⊗ₖ identity₂ := by
  ext x y
  rcases x with ⟨x0, x1⟩
  rcases y with ⟨y0, y1⟩
  change embedQubit (0 : Fin 2) A ![x0, x1] ![y0, y1] =
    A x0 y0 * identity₂ x1 y1
  rw [embedQubit_apply_ite]
  by_cases h : x1 = y1
  · subst y1
    simp [identity₂]
  · simp [identity₂, h]

theorem coordinate_one_is_right_kronecker_factor (A : QubitMatrix) :
    Matrix.reindexRingEquiv Complex twoQubitBasisEquiv
        (embedQubit (1 : Fin 2) A) =
      identity₂ ⊗ₖ A := by
  ext x y
  rcases x with ⟨x0, x1⟩
  rcases y with ⟨y0, y1⟩
  change embedQubit (1 : Fin 2) A ![x0, x1] ![y0, y1] =
    identity₂ x0 y0 * A x1 y1
  rw [embedQubit_apply_ite]
  by_cases h : x0 = y0
  · subst y0
    simp [identity₂]
  · simp [identity₂, h]

/-! ## Exhaustive entry behavior on three qubits -/

theorem xAt_zero_all_three_qubit_entries (x y : Basis (Fin 3)) :
    xAt (0 : Fin 3) x y =
      if x 1 = y 1 ∧ x 2 = y 2 then pauliX (x 0) (y 0) else 0 := by
  rw [xAt, embedQubit_apply_ite]
  by_cases h : x 1 = y 1 ∧ x 2 = y 2
  · rw [if_pos h, if_pos]
    rintro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact h.1
    · exact h.2
  · rw [if_neg h, if_neg]
    intro hall
    exact h ⟨hall 1 (by decide), hall 2 (by decide)⟩

theorem xAt_two_all_three_qubit_entries (x y : Basis (Fin 3)) :
    xAt (2 : Fin 3) x y =
      if x 0 = y 0 ∧ x 1 = y 1 then pauliX (x 2) (y 2) else 0 := by
  rw [xAt, embedQubit_apply_ite]
  by_cases h : x 0 = y 0 ∧ x 1 = y 1
  · rw [if_pos h, if_pos]
    rintro j hj
    fin_cases j
    · exact h.1
    · exact h.2
    · exact (hj rfl).elim
  · rw [if_neg h, if_neg]
    intro hall
    exact h ⟨hall 0 (by decide), hall 1 (by decide)⟩

theorem nonadjacent_three_qubit_coordinates_commute :
    xAt (0 : Fin 3) * zAt (2 : Fin 3) =
      zAt (2 : Fin 3) * xAt (0 : Fin 3) := by
  exact embedQubit_commute_of_ne (by decide) pauliX pauliZ

/-! ## Ordered placements remember domain order -/

/-- Local coordinate `0` is sent to ambient coordinate `2`, and local `1` to ambient `0`. -/
def outerSwap : Fin 2 ↪ Fin 3 where
  toFun := ![2, 0]
  inj' := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp

/-- The same ambient range as `outerSwap`, with the opposite domain ordering. -/
def outerStraight : Fin 2 ↪ Fin 3 where
  toFun := ![0, 2]
  inj' := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp

theorem outer_placements_have_the_same_selected_set :
    placementFinset outerSwap = placementFinset outerStraight := by
  ext q
  fin_cases q <;> simp [placementFinset, outerSwap, outerStraight]

def raw111 : Basis (Fin 3) := ![1, 1, 1]

def raw110 : Basis (Fin 3) := ![1, 1, 0]

theorem ordered_placement_swaps_the_local_first_coordinate :
    embedAlong outerSwap (xAt (0 : Fin 2)) raw111 raw110 = 1 := by
  rw [embedAlong_apply_ite]
  rw [if_pos]
  · rw [xAt, embedQubit_apply_ite]
    change pauliX (1 : QubitIndex) (0 : QubitIndex) = 1
    norm_num [pauliX]
  · intro q hq
    fin_cases q <;> simp_all [outerSwap, raw111, raw110]

theorem opposite_order_does_not_swap_the_local_first_coordinate :
    embedAlong outerStraight (xAt (0 : Fin 2)) raw111 raw110 = 0 := by
  rw [embedAlong_apply_ite]
  norm_num [outerStraight, raw111, raw110, xAt, embedQubit_apply_ite, pauliX]

theorem the_two_ordered_placements_are_distinct :
    embedAlong outerSwap (xAt (0 : Fin 2)) ≠
      embedAlong outerStraight (xAt (0 : Fin 2)) := by
  intro h
  have hentry := congrFun (congrFun h raw111) raw110
  rw [ordered_placement_swaps_the_local_first_coordinate,
    opposite_order_does_not_swap_the_local_first_coordinate] at hentry
  norm_num at hentry

/-! ## Support closure -/

theorem supported_pauli_polynomial :
    IsSupportedOn ({1} : Finset (Fin 3))
      ((xAt (1 : Fin 3) + yAt (1 : Fin 3)) * zAt (1 : Fin 3)) := by
  exact ((xAt_isSupportedOn 1).add (yAt_isSupportedOn 1)).mul
    (zAt_isSupportedOn 1)

theorem supported_heisenberg_conjugate :
    IsSupportedOn ({1} : Finset (Fin 3))
      (heisenberg (xAt (1 : Fin 3)) (zAt (1 : Fin 3))) := by
  exact (xAt_isSupportedOn 1).heisenberg (zAt_isSupportedOn 1)

/-! ## Necessary unitary hypotheses and eigenvector transport -/

theorem zero_operator_does_not_preserve_reference_norm :
    ‖act (0 : Operator (Fin 1)) (referenceKet (Fin 1))‖ ≠
      ‖referenceKet (Fin 1)‖ := by
  have hzero :
      act (0 : Operator (Fin 1)) (referenceKet (Fin 1)) = 0 := by
    unfold act
    rw [map_zero]
    rfl
  rw [hzero, norm_zero, norm_referenceKet]
  norm_num

theorem zero_operator_does_not_preserve_the_identity_in_heisenberg_form :
    Deutsch.Register.heisenberg (0 : Operator (Fin 1)) 1 ≠ 1 := by
  simp [Deutsch.Register.heisenberg]

theorem xAt_mem_unitaryGroup (q : Fin 3) :
    xAt q ∈ Matrix.unitaryGroup (Basis (Fin 3)) Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (xAt q)ᴴ * xAt q = 1
  rw [xAt_isHermitian, xAt_mul_xAt]

theorem eigenvector_transport_by_xAt
    (A : Operator (Fin 3)) (v : Ket (Fin 3)) (lambda : Complex)
    (hv : act A v = lambda • v) :
    act (heisenberg (xAt (0 : Fin 3)) A)
        (act (xAt (0 : Fin 3))ᴴ v) =
      lambda • act (xAt (0 : Fin 3))ᴴ v := by
  exact heisenberg_eigenvector (xAt 0) A v lambda (xAt_mem_unitaryGroup 0) hv

end
end RegisterVerification
end DeutschTests
