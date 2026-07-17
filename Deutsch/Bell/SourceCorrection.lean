import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.NormNum

/-!
# Source correction for Equation (45)

This module is a source regression for the paper's Boolean Equation (45).  It is intentionally
independent of `Deutsch.Bell.Finite`: the false printed identity is neither a premise nor a rewrite
rule in the finite Bell inequality.

Boolean values are encoded numerically in `ℕ` as zero and one.  The printed equation's second
term uses `(¬a₁ ∨ a₂)` and makes the identity false at `(a₀,a₁,a₂) = (1,0,1)`.  Replacing
that term by the complementary event `(¬a₁ ∧ ¬a₂)` gives a partition that holds for all eight
Boolean triples.
-/

namespace Deutsch
namespace Bell
namespace SourceCorrection

/-- Numeric zero/one representation of a Boolean source variable. -/
def boolValue : Bool → ℕ
  | false => 0
  | true => 1

@[simp]
theorem boolValue_false : boolValue false = 0 := rfl

@[simp]
theorem boolValue_true : boolValue true = 1 := rfl

/-- Numeric Boolean OR, written in the arithmetic form used by the source audit. -/
def numericOr (left right : Bool) : ℕ :=
  boolValue left + boolValue right - boolValue left * boolValue right

/-- The arithmetic definition of `numericOr` agrees with Boolean disjunction. -/
theorem numericOr_eq_boolValue_or (left right : Bool) :
    numericOr left right = boolValue (left || right) := by
  cases left <;> cases right <;> rfl

/-- Left-hand side of the paper's printed Equation (45). -/
def equation45PrintedLeft (a₀ : Bool) : ℕ :=
  boolValue a₀

/--
Right-hand side of the paper's printed Equation (45):
`a₀ (a₁ ∨ a₂) + a₀ (¬a₁ ∨ a₂)`.
-/
def equation45PrintedRight (a₀ a₁ a₂ : Bool) : ℕ :=
  boolValue a₀ * numericOr a₁ a₂ +
    boolValue a₀ * numericOr (!a₁) a₂

/-- The two printed sides evaluate to `1` and `2` at the source-audit counterexample. -/
theorem equation45_printed_counterexample_values :
    equation45PrintedLeft true = 1 ∧
      equation45PrintedRight true false true = 2 := by
  norm_num [equation45PrintedLeft, equation45PrintedRight, numericOr, boolValue]

/-- The printed Equation (45) fails at the Boolean triple `(1,0,1)`. -/
theorem equation45_printed_fails_at_one_zero_one :
    equation45PrintedLeft true ≠ equation45PrintedRight true false true := by
  norm_num [equation45PrintedLeft, equation45PrintedRight, numericOr, boolValue]

/--
Corrected right-hand side: the second term is the event complementary to `(a₁ ∨ a₂)`,
namely `(¬a₁ ∧ ¬a₂)`.
-/
def equation45CorrectedRight (a₀ a₁ a₂ : Bool) : ℕ :=
  boolValue a₀ * numericOr a₁ a₂ +
    boolValue a₀ * boolValue (!a₁) * boolValue (!a₂)

/-- The corrected complementary-event partition holds for all eight Boolean triples. -/
theorem equation45_corrected_complementary_partition (a₀ a₁ a₂ : Bool) :
    equation45PrintedLeft a₀ = equation45CorrectedRight a₀ a₁ a₂ := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;>
    norm_num [equation45PrintedLeft, equation45CorrectedRight, numericOr, boolValue]

/-- Assignment-table form of the corrected partition. -/
theorem equation45_corrected_partition_for_assignment
    (assignment : Fin 3 → Bool) :
    equation45PrintedLeft (assignment 0) =
      equation45CorrectedRight (assignment 0) (assignment 1) (assignment 2) :=
  equation45_corrected_complementary_partition
    (assignment 0) (assignment 1) (assignment 2)

end SourceCorrection
end Bell
end Deutsch
