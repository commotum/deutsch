import Deutsch.Register.Embedding

/-!
# Locality of disjoint register subsystems

Operators embedded on disjoint finite sets of named qubits commute.  The proof first computes an
exact matrix-product entry using the unique intermediate basis assignment compatible with both
embedded operators, then observes that the remaining complex scalars commute.
-/

namespace Deutsch
namespace Locality

open Foundations Register
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The unique intermediate assignment selected by successive actions on disjoint subsystems. -/
private def intermediateAssignment (s : Finset Q) (x y : Basis Q) : Basis Q :=
  fun q => if q ∈ s then y q else x q

/-- Exact entry formula for a product of operators embedded on disjoint subsystems. -/
theorem embedSubsystem_mul_embedSubsystem_apply_of_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (A : SubsystemOperator s) (B : SubsystemOperator t) (x y : Basis Q) :
    (embedSubsystem s A * embedSubsystem t B) x y =
      if ∀ q, q ∉ s → q ∉ t → x q = y q then
        A (fun q => x q.1) (fun q => y q.1) *
          B (fun q => x q.1) (fun q => y q.1)
      else 0 := by
  rw [Matrix.mul_apply]
  let z0 : Basis Q := intermediateAssignment s x y
  by_cases hxy : ∀ q, q ∉ s → q ∉ t → x q = y q
  · rw [if_pos hxy, Finset.sum_eq_single z0]
    · have hs0 : ∀ q, q ∉ s → x q = z0 q := by
        intro q hqs
        simp [z0, intermediateAssignment, hqs]
      have ht0 : ∀ q, q ∉ t → z0 q = y q := by
        intro q hqt
        by_cases hqs : q ∈ s
        · simp [z0, intermediateAssignment, hqs]
        · simp [z0, intermediateAssignment, hqs, hxy q hqs hqt]
      rw [embedSubsystem_apply_ite, embedSubsystem_apply_ite,
        if_pos hs0, if_pos ht0]
      have hz0s :
          (fun q : {q : Q // q ∈ s} => z0 q.1) =
            (fun q => y q.1) := by
        funext q
        simp [z0, intermediateAssignment, q.2]
      have hz0t :
          (fun q : {q : Q // q ∈ t} => z0 q.1) =
            (fun q => x q.1) := by
        funext q
        have hnot : q.1 ∉ s := Finset.disjoint_left.mp hst.symm q.2
        simp [z0, intermediateAssignment, hnot]
      rw [hz0s, hz0t]
    · intro z _ hzne
      rw [embedSubsystem_apply_ite, embedSubsystem_apply_ite]
      by_cases hsz : ∀ q, q ∉ s → x q = z q
      · by_cases hzt : ∀ q, q ∉ t → z q = y q
        · exfalso
          apply hzne
          funext q
          by_cases hqs : q ∈ s
          · have hqt : q ∉ t := Finset.disjoint_left.mp hst hqs
            calc
              z q = y q := hzt q hqt
              _ = z0 q := by simp [z0, intermediateAssignment, hqs]
          · calc
              z q = x q := (hsz q hqs).symm
              _ = z0 q := by simp [z0, intermediateAssignment, hqs]
        · rw [if_neg hzt]
          simp
      · rw [if_neg hsz]
        simp
    · simp
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro z _
    rw [embedSubsystem_apply_ite, embedSubsystem_apply_ite]
    by_cases hsz : ∀ q, q ∉ s → x q = z q
    · by_cases hzt : ∀ q, q ∉ t → z q = y q
      · exfalso
        apply hxy
        intro q hqs hqt
        exact (hsz q hqs).trans (hzt q hqt)
      · rw [if_neg hzt]
        simp
    · rw [if_neg hsz]
      simp

/-- Arbitrary operators embedded on disjoint named subsystems commute. -/
theorem embedSubsystem_commute_of_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (A : SubsystemOperator s) (B : SubsystemOperator t) :
    embedSubsystem s A * embedSubsystem t B =
      embedSubsystem t B * embedSubsystem s A := by
  ext x y
  rw [embedSubsystem_mul_embedSubsystem_apply_of_disjoint hst A B x y,
    embedSubsystem_mul_embedSubsystem_apply_of_disjoint hst.symm B A x y]
  by_cases hxy : ∀ q, q ∉ s → q ∉ t → x q = y q
  · rw [if_pos hxy, if_pos]
    · exact mul_comm _ _
    · intro q hqt hqs
      exact hxy q hqs hqt
  · rw [if_neg hxy, if_neg]
    intro hreverse
    exact hxy fun q hqs hqt => hreverse q hqt hqs

/-- Operators with disjoint exact support witnesses commute. -/
theorem supportedOperators_commute_of_disjoint
    {s t : Finset Q} {A B : Operator Q} (hst : Disjoint s t)
    (hA : IsSupportedOn s A) (hB : IsSupportedOn t B) :
    A * B = B * A := by
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  exact embedSubsystem_commute_of_disjoint hst a b

end
end Locality
end Deutsch
