import Deutsch.Descriptor.Basic
import Deutsch.Information.State
import Deutsch.Register.State

/-!
# Paper façade: quantum computation in the Heisenberg picture

This module gives source-shaped entries for Equations (1)--(8).  Equations that introduce
notation are definitions; algebraic conditions are exposed as schemas; displayed consequences
are theorems.  In Equation (8), the next-time eigenkets are an explicitly chosen unitary
transport of a supplied simultaneous eigenfamily.  No canonical choice inside a degenerate
eigenspace is asserted.
-/

namespace Deutsch
namespace Paper

open Foundations Information Register
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Equation (1): assemble the three global observables describing one named qubit. -/
def equation01 (x y z : Operator Q) : Descriptor Q where
  x := x
  y := y
  z := z

/--
Equation (2) as a schema: each descriptor is a Hermitian Pauli triple and components belonging
to distinct qubits commute.  Reverse products and anticommutation follow from this predicate.
-/
def equation02 (D : DescriptorFamily Q) : Prop :=
  DescriptorFamily.Valid D

/-- Equation (3): the concrete Pauli triple in the source's matrix convention. -/
def equation03 : Axis → QubitMatrix
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ

/-- Equation (4): the logical-paper-one projector is `(I + Z) / 2`. -/
theorem equation04 (q : Q) :
    paperBitOneProjectorAt q = ((2 : ℂ)⁻¹) • (1 + zAt q) :=
  paperBitOneProjectorAt_eq q

/-- Equation (5): the initial descriptor is the Pauli triple embedded at one coordinate. -/
theorem equation05 (q : Q) :
    Descriptor.initial q = { x := xAt q, y := yAt q, z := zAt q } :=
  rfl

/-- Equation (6): expectation in the fixed all-paper-zero reference ket. -/
def equation06 (A : Operator Q) : ℂ :=
  expectation (referenceKet Q) A

/-- Equation (7): every component evolves by the same Heisenberg conjugation. -/
theorem equation07 (U : Operator Q) (D : DescriptorFamily Q) (q : Q) (a : Axis) :
    ((DescriptorFamily.evolve U D q).component a) =
      heisenberg U ((D q).component a) :=
  Descriptor.evolve_component U (D q) a

/--
Equation (8): simultaneous eigenkets transport contravariantly by `U†`.

The supplied family may include any phase convention and any basis choice inside degenerate
joint eigenspaces.  The result chooses the exact transported representatives, so its displayed
equality has no hidden phase assertion.
-/
theorem equation08
    {I Z : Type*}
    (U : Operator Q)
    (observables : I → Operator Q)
    (atTime : Z → Ket Q)
    (eigenvalue : Z → I → ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hEigen : ∀ z i,
      act (observables i) (atTime z) = eigenvalue z i • atTime z) :
    ∃ atNext : Z → Ket Q,
      (∀ z, atNext z = act Uᴴ (atTime z)) ∧
      ∀ z i,
        act (heisenberg U (observables i)) (atNext z) =
          eigenvalue z i • atNext z := by
  refine ⟨fun z => act Uᴴ (atTime z), fun _ => rfl, ?_⟩
  intro z i
  exact heisenberg_eigenvector U (observables i) (atTime z)
    (eigenvalue z i) hU (hEigen z i)

end
end Paper
end Deutsch
