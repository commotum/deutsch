import Deutsch.Descriptor.Basic
import Deutsch.Register.State

/-!
# Equality levels for descriptor families

Exact operator equality, simultaneous unitary conjugacy, and equality of the three component
expectations in the fixed reference ket are deliberately separate relations.  In particular, this
module does not turn a fixed-state expectation statement into operator equality.
-/

namespace Deutsch
namespace DescriptorFamily

open Register

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Two families are conjugate when one shared physical unitary evolves every component. -/
def IsUnitaryConjugate (D E : DescriptorFamily Q) : Prop :=
  ∃ U : UnitaryOperator Q, E = evolve U D

theorem isUnitaryConjugate_refl (D : DescriptorFamily Q) : IsUnitaryConjugate D D := by
  refine ⟨1, ?_⟩
  simp

theorem isUnitaryConjugate_symm {D E : DescriptorFamily Q}
    (h : IsUnitaryConjugate D E) : IsUnitaryConjugate E D := by
  rcases h with ⟨U, rfl⟩
  refine ⟨star U, ?_⟩
  rw [← evolve_chronology (U := (↑(star U) : Operator Q)) (V := (↑U : Operator Q))]
  simp

theorem isUnitaryConjugate_trans {D E F : DescriptorFamily Q}
    (hDE : IsUnitaryConjugate D E) (hEF : IsUnitaryConjugate E F) :
    IsUnitaryConjugate D F := by
  rcases hDE with ⟨U, rfl⟩
  rcases hEF with ⟨V, rfl⟩
  refine ⟨U * V, ?_⟩
  rw [← evolve_chronology (U := (↑V : Operator Q)) (V := (↑U : Operator Q))]
  rfl

theorem isUnitaryConjugate_equivalence :
    Equivalence (IsUnitaryConjugate (Q := Q)) :=
  ⟨isUnitaryConjugate_refl, isUnitaryConjugate_symm, isUnitaryConjugate_trans⟩

/-- Every physical family evolution is, by construction, a unitary conjugacy. -/
theorem isUnitaryConjugate_evolve (U : UnitaryOperator Q) (D : DescriptorFamily Q) :
    IsUnitaryConjugate D (evolve U D) :=
  ⟨U, rfl⟩

/-- Equality of the three descriptor-component expectations in the fixed reference ket. -/
def ReferenceExpectationEquivalent (D E : DescriptorFamily Q) : Prop :=
  ∀ q a,
    expectation (referenceKet Q) ((D q).component a) =
      expectation (referenceKet Q) ((E q).component a)

theorem referenceExpectationEquivalent_refl (D : DescriptorFamily Q) :
    ReferenceExpectationEquivalent D D := by
  intro q a
  rfl

theorem referenceExpectationEquivalent_symm {D E : DescriptorFamily Q}
    (h : ReferenceExpectationEquivalent D E) : ReferenceExpectationEquivalent E D := by
  intro q a
  exact (h q a).symm

theorem referenceExpectationEquivalent_trans {D E F : DescriptorFamily Q}
    (hDE : ReferenceExpectationEquivalent D E)
    (hEF : ReferenceExpectationEquivalent E F) :
    ReferenceExpectationEquivalent D F := by
  intro q a
  exact (hDE q a).trans (hEF q a)

theorem referenceExpectationEquivalent_equivalence :
    Equivalence (ReferenceExpectationEquivalent (Q := Q)) :=
  ⟨referenceExpectationEquivalent_refl,
    referenceExpectationEquivalent_symm,
    referenceExpectationEquivalent_trans⟩

/-- Exact family equality implies fixed-reference component-expectation equality. -/
theorem referenceExpectationEquivalent_of_eq {D E : DescriptorFamily Q} (h : D = E) :
    ReferenceExpectationEquivalent D E := by
  subst E
  exact referenceExpectationEquivalent_refl D

/--
A conjugation that fixes the reference ket preserves all fixed-reference descriptor-component
expectations.  This conclusion is intentionally weaker than equality of the operators.
-/
theorem referenceExpectationEquivalent_evolve_of_fixes_reference
    (U : UnitaryOperator Q) (D : DescriptorFamily Q)
    (hfix : act U (referenceKet Q) = referenceKet Q) :
    ReferenceExpectationEquivalent D (evolve U D) := by
  intro q a
  simp only [evolve_apply, Descriptor.evolve_component]
  rw [← fixed_reference_prediction (↑U) ((D q).component a), hfix]

end
end DescriptorFamily
end Deutsch
