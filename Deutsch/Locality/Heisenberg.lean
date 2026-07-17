import Deutsch.Locality.Basic
import Deutsch.Register.State

/-!
# Heisenberg locality for disjoint supported operations

Disjoint support first gives an operator commutation theorem.  A separate isometry/unitarity
hypothesis then supplies the cancellation needed for `Uᴴ * A * U = A`.  Prediction equalities are
derived only after that operator equality and quantify over arbitrary register kets.
-/

namespace Deutsch
namespace Locality

open Register
open scoped InnerProductSpace Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Without cancellation, conjugating a commuting operator leaves the Gram factor `UᴴU`. -/
theorem heisenberg_eq_gram_mul_of_commute (U A : Operator Q)
    (hcomm : U * A = A * U) :
    Register.heisenberg U A = (Uᴴ * U) * A := by
  calc
    Register.heisenberg U A = Uᴴ * (A * U) := by
      simp [Register.heisenberg, Matrix.mul_assoc]
    _ = Uᴴ * (U * A) := by rw [← hcomm]
    _ = (Uᴴ * U) * A := by simp [Matrix.mul_assoc]

/-- The precise cancellation assumption needed to fix a commuting observable. -/
theorem heisenberg_eq_self_of_commute_of_isometry (U A : Operator Q)
    (hcomm : U * A = A * U) (hU : Uᴴ * U = 1) :
    Register.heisenberg U A = A := by
  rw [heisenberg_eq_gram_mul_of_commute U A hcomm, hU, one_mul]

/-- An isometry supported on `s` fixes every observable supported on disjoint `t`. -/
theorem heisenberg_eq_self_of_disjoint_support_of_isometry
    {s t : Finset Q} {U A : Operator Q}
    (hst : Disjoint s t)
    (hU : Uᴴ * U = 1)
    (hUs : IsSupportedOn s U) (hAt : IsSupportedOn t A) :
    Register.heisenberg U A = A := by
  have hcomm : U * A = A * U :=
    supportedOperators_commute_of_disjoint hst hUs hAt
  exact heisenberg_eq_self_of_commute_of_isometry U A hcomm hU

/-- A unitary supported on `s` fixes every observable supported on disjoint `t`. -/
theorem heisenberg_eq_self_of_disjoint_support
    {s t : Finset Q} {U A : Operator Q}
    (hst : Disjoint s t)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hUs : IsSupportedOn s U) (hAt : IsSupportedOn t A) :
    Register.heisenberg U A = A := by
  have hIsometry : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1
  exact heisenberg_eq_self_of_disjoint_support_of_isometry
    hst hIsometry hUs hAt

/-- Bundled-unitary form of the disjoint-support Heisenberg locality theorem. -/
theorem evolve_eq_self_of_disjoint_support
    {s t : Finset Q} (U : UnitaryOperator Q) {A : Operator Q}
    (hst : Disjoint s t)
    (hUs : IsSupportedOn s U.1) (hAt : IsSupportedOn t A) :
    evolve U A = A := by
  exact heisenberg_eq_self_of_disjoint_support hst U.2 hUs hAt

/-- Operator locality gives expectation invariance for every ket, with no separability premise. -/
theorem expectation_heisenberg_eq_of_disjoint_support
    {s t : Finset Q} {U A : Operator Q}
    (hst : Disjoint s t)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hUs : IsSupportedOn s U) (hAt : IsSupportedOn t A)
    (psi : Ket Q) :
    expectation psi (Register.heisenberg U A) = expectation psi A := by
  rw [heisenberg_eq_self_of_disjoint_support hst hU hUs hAt]

/-- Schrödinger action by a local unitary preserves every disjoint observable expectation. -/
theorem expectation_after_local_unitary_eq
    {s t : Finset Q} {U A : Operator Q}
    (hst : Disjoint s t)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hUs : IsSupportedOn s U) (hAt : IsSupportedOn t A)
    (psi : Ket Q) :
    expectation (act U psi) A = expectation psi A := by
  rw [expectation_after_action,
    heisenberg_eq_self_of_disjoint_support hst hU hUs hAt]

end
end Locality
end Deutsch
