import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.NormNum

/-!
# The Boolean bookkeeping in Equation (45)

This elementary module records the two sides of the printed Boolean formula and the
complementary partition used by the derivation.  It is intentionally independent of
the quantum and finite-probability libraries.
-/

namespace DeutschErrata
namespace Equation45

/-- Numeric zero-one representation of a Boolean source variable. -/
def boolValue : Bool → ℕ
  | false => 0
  | true => 1

@[simp]
theorem boolValue_false : boolValue false = 0 := rfl

@[simp]
theorem boolValue_true : boolValue true = 1 := rfl

/-- Arithmetic disjunction for zero-one values. -/
def numericOr (left right : Bool) : ℕ :=
  boolValue left + boolValue right - boolValue left * boolValue right

theorem numericOr_eq_boolValue_or (left right : Bool) :
    numericOr left right = boolValue (left || right) := by
  cases left <;> cases right <;> rfl

/-- Left side of printed Equation (45). -/
def equation45PrintedLeft (a₀ : Bool) : ℕ :=
  boolValue a₀

/--
Right side of printed Equation (45):
`a₀ (a₁ ∨ a₂) + a₀ (¬a₁ ∨ a₂)`.
-/
def equation45PrintedRight (a₀ a₁ a₂ : Bool) : ℕ :=
  boolValue a₀ * numericOr a₁ a₂ +
    boolValue a₀ * numericOr (!a₁) a₂

/-- Right side obtained by using the event complementary to `a₁ ∨ a₂`. -/
def equation45ComplementaryRight (a₀ a₁ a₂ : Bool) : ℕ :=
  boolValue a₀ * numericOr a₁ a₂ +
    boolValue a₀ * boolValue (!a₁) * boolValue (!a₂)

/-- At `(a₀,a₁,a₂) = (1,0,1)`, the two printed sides evaluate to `1` and `2`. -/
theorem equation45_printed_values_at_one_zero_one :
    equation45PrintedLeft true = 1 ∧
      equation45PrintedRight true false true = 2 := by
  norm_num [equation45PrintedLeft, equation45PrintedRight, numericOr, boolValue]

/-- The explicit values above make the printed form unequal at `(1,0,1)`. -/
theorem equation45_printed_form_fails_at_one_zero_one :
    equation45PrintedLeft true ≠ equation45PrintedRight true false true := by
  norm_num [equation45PrintedLeft, equation45PrintedRight, numericOr, boolValue]

/-- The complementary-event replacement partitions `a₀` for every Boolean triple. -/
theorem equation45_complementary_partition (a₀ a₁ a₂ : Bool) :
    equation45PrintedLeft a₀ =
      equation45ComplementaryRight a₀ a₁ a₂ := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;>
    norm_num [equation45PrintedLeft, equation45ComplementaryRight, numericOr, boolValue]

end Equation45
end DeutschErrata
