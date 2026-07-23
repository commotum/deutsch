import Deutsch.Information.State
import Deutsch.Register.Embedding
import Mathlib.Analysis.Matrix.PosDef

/-!
# Selected-subsystem reduction

The global register basis is reindexed into selected and complementary coordinates, after which
the complement is traced out explicitly. Positivity and trace preservation are derived from this
entrywise definition. The central duality theorem identifies local expectations in the reduced
state with global expectations of an embedded local operator.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped Matrix Kronecker BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Express a global operator in the selected/complement product basis. -/
def splitOperator (s : Finset Q) (rho : Operator Q) :
    Matrix (SubsystemBasis s × ComplementBasis s)
      (SubsystemBasis s × ComplementBasis s) ℂ :=
  Matrix.reindexRingEquiv ℂ (splitBasis s) rho

@[simp]
theorem splitOperator_apply (s : Finset Q) (rho : Operator Q)
    (i j : SubsystemBasis s × ComplementBasis s) :
    splitOperator s rho i j =
      rho ((splitBasis s).symm i) ((splitBasis s).symm j) := rfl

/-- Trace out the complement of `s`. -/
def partialTrace (s : Finset Q) (rho : Operator Q) : SubsystemOperator s :=
  fun i j => ∑ k : ComplementBasis s, splitOperator s rho (i, k) (j, k)

theorem partialTrace_add (s : Finset Q) (A B : Operator Q) :
    partialTrace s (A + B) = partialTrace s A + partialTrace s B := by
  ext i j
  simp [partialTrace, splitOperator, Finset.sum_add_distrib]

theorem partialTrace_smul (s : Finset Q) (c : ℂ) (A : Operator Q) :
    partialTrace s (c • A) = c • partialTrace s A := by
  ext i j
  simp [partialTrace, splitOperator, Finset.mul_sum]

@[simp]
theorem partialTrace_zero (s : Finset Q) :
    partialTrace s (0 : Operator Q) = 0 := by
  ext i j
  simp [partialTrace, splitOperator]

/-- Reducing a computational-basis density restricts its basis assignment. -/
theorem partialTrace_basisDensity (s : Finset Q) (bits : Basis Q) :
    partialTrace s (basisDensity bits).op =
      Matrix.diagonal
        (Pi.single (fun q : {q : Q // q ∈ s} ↦ bits q.1) 1) := by
  classical
  ext i j
  simp only [partialTrace, splitOperator_apply, basisDensity, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    let selectedBits : SubsystemBasis s := fun q ↦ bits q.1
    let rest : ComplementBasis s := fun q ↦ bits q.1
    have hsplit (x : ComplementBasis s) :
        (splitBasis s).symm (i, x) = bits ↔ i = selectedBits ∧ x = rest := by
      rw [Equiv.symm_apply_eq]
      change (i, x) = (selectedBits, rest) ↔ _
      simp
    by_cases hi : i = selectedBits
    · subst i
      rw [Fintype.sum_eq_single rest]
      · have hglobal :
            (splitBasis s).symm (selectedBits, rest) = bits :=
            by exact (hsplit rest).2 ⟨rfl, rfl⟩
        rw [hglobal]
        simp [Pi.single, selectedBits]
      · intro x hx
        simp [Pi.single, hsplit, selectedBits, rest, hx]
    · rw [Finset.sum_eq_zero]
      · simp [Pi.single, selectedBits, hi]
      · intro x hx
        simp [Pi.single, hsplit, selectedBits, rest, hi]
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro x hx
      rw [if_neg]
      intro h
      apply hij
      have hs := congrArg (fun assignments ↦ (splitBasis s assignments).1) h
      simpa using hs

/-- The operator obtained by restricting a global operator to `s`. -/
abbrev reducedOperator (s : Finset Q) (rho : Operator Q) : SubsystemOperator s :=
  partialTrace s rho

theorem partialTrace_eq_sum_submatrix (s : Finset Q) (rho : Operator Q) :
    partialTrace s rho =
      ∑ k : ComplementBasis s,
        (splitOperator s rho).submatrix (fun i => (i, k)) (fun i => (i, k)) := by
  ext i j
  simp [partialTrace, Matrix.sum_apply]

theorem partialTrace_posSemidef (s : Finset Q) {rho : Operator Q}
    (hrho : rho.PosSemidef) : (partialTrace s rho).PosSemidef := by
  rw [partialTrace_eq_sum_submatrix]
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  apply Matrix.PosSemidef.submatrix
  exact (Matrix.posSemidef_submatrix_equiv (splitBasis s).symm).2 hrho

theorem splitOperator_trace (s : Finset Q) (rho : Operator Q) :
    (splitOperator s rho).trace = rho.trace := by
  unfold splitOperator Matrix.trace Matrix.diag
  exact Equiv.sum_comp (splitBasis s).symm (fun i => rho i i)

theorem partialTrace_trace (s : Finset Q) (rho : Operator Q) :
    (partialTrace s rho).trace = rho.trace := by
  rw [← splitOperator_trace s rho]
  simp only [Matrix.trace, Matrix.diag, partialTrace]
  rw [Fintype.sum_prod_type]

@[simp]
theorem splitOperator_embedSubsystem (s : Finset Q) (A : SubsystemOperator s) :
    splitOperator s (embedSubsystem s A) =
      A ⊗ₖ (1 : Matrix (ComplementBasis s) (ComplementBasis s) ℂ) := by
  unfold splitOperator embedSubsystem
  simp

theorem splitOperator_mul (s : Finset Q) (A B : Operator Q) :
    splitOperator s (A * B) = splitOperator s A * splitOperator s B := by
  exact map_mul (Matrix.reindexRingEquiv ℂ (splitBasis s)) A B

private def partialTraceProduct
    {S C : Type*} [Fintype C]
    (rho : Matrix (S × C) (S × C) ℂ) : Matrix S S ℂ :=
  fun i j => ∑ k : C, rho (i, k) (j, k)

private theorem partialTraceProduct_duality
    {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (rho : Matrix (S × C) (S × C) ℂ) (A : Matrix S S ℂ) :
    Matrix.trace (partialTraceProduct rho * A) =
      Matrix.trace (rho * (A ⊗ₖ (1 : Matrix C C ℂ))) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, partialTraceProduct]
  have hinner (i : S) (k : C) :
      (∑ q : S × C, rho (i, k) q * (A q.1 i * (1 : Matrix C C ℂ) q.2 k)) =
        ∑ j : S, rho (i, k) (j, k) * A j i := by
    rw [Fintype.sum_prod_type]
    change (∑ j : S, ∑ l : C,
      rho (i, k) (j, l) * (A j i * (1 : Matrix C C ℂ) l k)) = _
    apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.sum_eq_single k]
    · simp
    · intro l hl
      simp [hl]
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Partial trace is dual to embedding a local observable. -/
theorem partialTrace_trace_mul (s : Finset Q) (rho : Operator Q)
    (A : SubsystemOperator s) :
    Matrix.trace (partialTrace s rho * A) =
      Matrix.trace (rho * embedSubsystem s A) := by
  rw [← splitOperator_trace s (rho * embedSubsystem s A)]
  rw [splitOperator_mul, splitOperator_embedSubsystem]
  exact partialTraceProduct_duality (splitOperator s rho) A

/-- Restrict a density state to a selected subsystem. -/
def Density.reduce (rho : Density Q) (s : Finset Q) : Density {q : Q // q ∈ s} where
  op := partialTrace s rho.op
  positive := partialTrace_posSemidef s rho.positive
  trace_one := by rw [partialTrace_trace, rho.trace_one]

@[simp]
theorem Density.reduce_op (rho : Density Q) (s : Finset Q) :
    (rho.reduce s).op = partialTrace s rho.op := rfl

/-- Embedding preserves positive semidefiniteness. -/
theorem embedSubsystem_posSemidef (s : Finset Q) {A : SubsystemOperator s}
    (hA : A.PosSemidef) : (embedSubsystem s A).PosSemidef := by
  unfold embedSubsystem
  exact (Matrix.posSemidef_submatrix_equiv (splitBasis s)).2
    (hA.kronecker Matrix.PosSemidef.one)

theorem embedSubsystem_sub (s : Finset Q) (A B : SubsystemOperator s) :
    embedSubsystem s (A - B) = embedSubsystem s A - embedSubsystem s B := by
  exact map_sub (embedSubsystemAlgHom s) A B

/-- Embed a selected-subsystem effect into the full register. -/
def Effect.embedSubsystem (s : Finset Q) (effect : Effect {q : Q // q ∈ s}) : Effect Q where
  op := Register.embedSubsystem s effect.op
  positive := embedSubsystem_posSemidef s effect.positive
  complement_positive := by
    rw [← embedSubsystem_one s, ← embedSubsystem_sub]
    exact embedSubsystem_posSemidef s effect.complement_positive

@[simp]
theorem Effect.embedSubsystem_op (s : Finset Q)
    (effect : Effect {q : Q // q ∈ s}) :
    (effect.embedSubsystem s).op = Register.embedSubsystem s effect.op := rfl

private theorem reindexAlong_posSemidef
    {K R : Type*} [Fintype K] [DecidableEq K] [DecidableEq R]
    (p : K ↪ R) {A : Operator K} (hA : A.PosSemidef) :
    (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) A).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (alongBasisEquiv p)).1
  simpa [Matrix.reindexAlgEquiv] using hA

/-- Place an effect along an ordered injection of finite registers. -/
def Effect.embedAlong {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (effect : Effect K) : Effect Q where
  op := Register.embedAlong p effect.op
  positive :=
    embedSubsystem_posSemidef (placementFinset p)
      (reindexAlong_posSemidef p effect.positive)
  complement_positive := by
    rw [← embedAlong_one p]
    change (embedAlongAlgHom p 1 - embedAlongAlgHom p effect.op).PosSemidef
    rw [← map_sub]
    exact
      embedSubsystem_posSemidef (placementFinset p)
        (reindexAlong_posSemidef p effect.complement_positive)

@[simp]
theorem Effect.embedAlong_op {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (effect : Effect K) :
    (effect.embedAlong p).op = Register.embedAlong p effect.op := rfl

/--
Placing an operator on named coordinates does not change its expectation in the all-paper-zero
reference state.
-/
theorem referenceDensity_expectation_embedAlong
    {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (A : Operator K) :
    densityExpectation (referenceDensity Q) (embedAlong p A) =
      densityExpectation (referenceDensity K) A := by
  rw [referenceDensity, referenceDensity,
    basisDensity_expectation, basisDensity_expectation,
    embedAlong_apply_ite]
  simp only [paperZeroAssignment]
  rw [if_pos]
  · rfl
  · intro q hq
    trivial

/-- Reduced and embedded local effects give exactly the same complex Born weight. -/
theorem bornWeight_reduce (rho : Density Q) (s : Finset Q)
    (effect : Effect {q : Q // q ∈ s}) :
    bornWeight (rho.reduce s) effect = bornWeight rho (effect.embedSubsystem s) := by
  exact partialTrace_trace_mul s rho.op effect.op

/-- Reduced and embedded local effects give exactly the same real probability. -/
theorem bornProbability_reduce (rho : Density Q) (s : Finset Q)
    (effect : Effect {q : Q // q ∈ s}) :
    bornProbability (rho.reduce s) effect =
      bornProbability rho (effect.embedSubsystem s) := by
  exact congrArg Complex.re (bornWeight_reduce rho s effect)

/-- Selected-subsystem density equality is exactly agreement of all embedded local effects. -/
theorem reduced_density_eq_iff_embedded_effect_probabilities
    (s : Finset Q) (rho sigma : Density Q) :
    rho.reduce s = sigma.reduce s ↔
      ∀ effect : Effect {q : Q // q ∈ s},
        bornProbability rho (effect.embedSubsystem s) =
          bornProbability sigma (effect.embedSubsystem s) := by
  rw [density_eq_iff_effect_probabilities]
  constructor
  · intro h effect
    rw [← bornProbability_reduce rho s effect,
      ← bornProbability_reduce sigma s effect]
    exact h effect
  · intro h effect
    rw [bornProbability_reduce rho s effect,
      bornProbability_reduce sigma s effect]
    exact h effect

end
end Information
end Deutsch
