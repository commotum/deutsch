import Deutsch.Information.State

/-!
# Finite Kraus channels

A channel from register `Q` to register `R` is represented by a finite typed Kraus family
`K a : Matrix (Basis R) (Basis Q) ℂ` satisfying `∑ a, K aᴴ K a = I`. This constructive
representation makes positivity and trace preservation direct finite-matrix theorems and avoids
postulating a separate complete-positivity field.

The dual action on effects is proved compatible with Born probabilities. These are state/effect
transformations only; no outcome-conditioned instrument or decoherence process is implied.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped ComplexOrder Matrix MatrixOrder BigOperators

noncomputable section

variable {Q R K : Type*}
variable [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R] [Fintype K]

/-- A finite Kraus channel with explicitly typed input, output, and Kraus labels. -/
structure KrausChannel (Q R K : Type*)
    [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R] [Fintype K] where
  kraus : K → Matrix (Basis R) (Basis Q) ℂ
  complete : ∑ k, (kraus k)ᴴ * kraus k = 1

/-- Schrödinger action of a Kraus channel on an input operator. -/
def KrausChannel.mapOperator (channel : KrausChannel Q R K) (A : Operator Q) :
    Operator R :=
  ∑ k, channel.kraus k * A * (channel.kraus k)ᴴ

/-- Heisenberg dual action of a Kraus channel on an output operator. -/
def KrausChannel.dualOperator (channel : KrausChannel Q R K) (A : Operator R) :
    Operator Q :=
  ∑ k, (channel.kraus k)ᴴ * A * channel.kraus k

theorem KrausChannel.mapOperator_add (channel : KrausChannel Q R K)
    (A B : Operator Q) :
    channel.mapOperator (A + B) =
      channel.mapOperator A + channel.mapOperator B := by
  classical
  simp [KrausChannel.mapOperator, Matrix.mul_add, Matrix.add_mul,
    Finset.sum_add_distrib]

theorem KrausChannel.mapOperator_smul (channel : KrausChannel Q R K)
    (c : ℂ) (A : Operator Q) :
    channel.mapOperator (c • A) = c • channel.mapOperator A := by
  classical
  simp [KrausChannel.mapOperator, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]

@[simp]
theorem KrausChannel.mapOperator_zero (channel : KrausChannel Q R K) :
    channel.mapOperator (0 : Operator Q) = 0 := by
  classical
  simp [KrausChannel.mapOperator]

theorem KrausChannel.mapOperator_posSemidef (channel : KrausChannel Q R K)
    {A : Operator Q} (hA : A.PosSemidef) :
    (channel.mapOperator A).PosSemidef := by
  classical
  unfold KrausChannel.mapOperator
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  exact hA.mul_mul_conjTranspose_same (channel.kraus k)

theorem KrausChannel.dualOperator_posSemidef (channel : KrausChannel Q R K)
    {A : Operator R} (hA : A.PosSemidef) :
    (channel.dualOperator A).PosSemidef := by
  classical
  unfold KrausChannel.dualOperator
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  exact hA.conjTranspose_mul_mul_same (channel.kraus k)

/-- The Schrödinger operator action is trace preserving. -/
theorem KrausChannel.trace_mapOperator (channel : KrausChannel Q R K)
    (A : Operator Q) : Matrix.trace (channel.mapOperator A) = Matrix.trace A := by
  classical
  unfold KrausChannel.mapOperator
  rw [Matrix.trace_sum]
  calc
    (∑ k, Matrix.trace (channel.kraus k * A * (channel.kraus k)ᴴ)) =
        ∑ k, Matrix.trace (A * ((channel.kraus k)ᴴ * channel.kraus k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.trace_mul_cycle]
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (A * ∑ k, (channel.kraus k)ᴴ * channel.kraus k) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = Matrix.trace A := by rw [channel.complete, Matrix.mul_one]

/-- A Kraus channel maps density states to density states. -/
def KrausChannel.mapDensity (channel : KrausChannel Q R K) (rho : Density Q) :
    Density R where
  op := channel.mapOperator rho.op
  positive := channel.mapOperator_posSemidef rho.positive
  trace_one := by rw [channel.trace_mapOperator, rho.trace_one]

/-- Schrödinger and Heisenberg channel actions are trace-dual. -/
theorem KrausChannel.trace_duality (channel : KrausChannel Q R K)
    (rho : Operator Q) (A : Operator R) :
    Matrix.trace (channel.mapOperator rho * A) =
      Matrix.trace (rho * channel.dualOperator A) := by
  classical
  simp only [KrausChannel.mapOperator, KrausChannel.dualOperator,
    Finset.sum_mul, Matrix.trace_sum, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    Matrix.trace ((channel.kraus k * rho * (channel.kraus k)ᴴ) * A) =
        Matrix.trace (channel.kraus k * (rho * ((channel.kraus k)ᴴ * A))) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((channel.kraus k)ᴴ * A) * (channel.kraus k * rho)) :=
      Matrix.trace_mul_cycle' (channel.kraus k) rho ((channel.kraus k)ᴴ * A)
    _ = Matrix.trace ((((channel.kraus k)ᴴ * A) * channel.kraus k) * rho) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho * ((channel.kraus k)ᴴ * A * channel.kraus k)) :=
      Matrix.trace_mul_comm (((channel.kraus k)ᴴ * A) * channel.kraus k) rho

theorem KrausChannel.one_sub_dualOperator (channel : KrausChannel Q R K)
    (A : Operator R) :
    1 - channel.dualOperator A = channel.dualOperator (1 - A) := by
  classical
  unfold KrausChannel.dualOperator
  rw [← channel.complete]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]

/-- The dual of an output effect is a valid input effect. -/
def KrausChannel.dualEffect (channel : KrausChannel Q R K) (effect : Effect R) :
    Effect Q where
  op := channel.dualOperator effect.op
  positive := channel.dualOperator_posSemidef effect.positive
  complement_positive := by
    rw [channel.one_sub_dualOperator]
    exact channel.dualOperator_posSemidef effect.complement_positive

/-- Channel/effect duality stated directly for complex Born weights. -/
theorem KrausChannel.bornWeight_mapDensity (channel : KrausChannel Q R K)
    (rho : Density Q) (effect : Effect R) :
    bornWeight (channel.mapDensity rho) effect =
      bornWeight rho (channel.dualEffect effect) :=
  channel.trace_duality rho.op effect.op

/-- Channel/effect duality stated directly for real Born probabilities. -/
theorem KrausChannel.bornProbability_mapDensity (channel : KrausChannel Q R K)
    (rho : Density Q) (effect : Effect R) :
    bornProbability (channel.mapDensity rho) effect =
      bornProbability rho (channel.dualEffect effect) :=
  congrArg Complex.re (channel.bornWeight_mapDensity rho effect)

/-- The identity channel, using one Kraus operator. -/
def identityChannel (Q : Type*) [Fintype Q] [DecidableEq Q] :
    KrausChannel Q Q Unit where
  kraus := fun _ => 1
  complete := by simp

@[simp]
theorem identityChannel_mapOperator (A : Operator Q) :
    (identityChannel Q).mapOperator A = A := by
  simp [identityChannel, KrausChannel.mapOperator]

/-- The channel induced by Schrödinger conjugation with a physical unitary. -/
def unitaryChannel (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) : KrausChannel Q Q Unit where
  kraus := fun _ => U
  complete := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1

@[simp]
theorem unitaryChannel_mapOperator (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) (A : Operator Q) :
    (unitaryChannel U hU).mapOperator A = U * A * Uᴴ := by
  simp [unitaryChannel, KrausChannel.mapOperator]

@[simp]
theorem identityChannel_mapDensity (rho : Density Q) :
    (identityChannel Q).mapDensity rho = rho := by
  apply Density.ext
  exact identityChannel_mapOperator rho.op

@[simp]
theorem unitaryChannel_mapDensity (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) (rho : Density Q) :
    (unitaryChannel U hU).mapDensity rho = rho.evolve U hU := by
  apply Density.ext
  exact unitaryChannel_mapOperator U hU rho.op

section Composition

variable {S L : Type*} [Fintype S] [DecidableEq S] [Fintype L]

/-- Composition of two chosen Kraus representations. -/
def KrausChannel.comp (after : KrausChannel R S L) (before : KrausChannel Q R K) :
    KrausChannel Q S (K × L) where
  kraus kl := after.kraus kl.2 * before.kraus kl.1
  complete := by
    classical
    rw [Fintype.sum_prod_type]
    simp_rw [Matrix.conjTranspose_mul]
    calc
      ∑ k, ∑ l,
          ((before.kraus k)ᴴ * (after.kraus l)ᴴ) *
            (after.kraus l * before.kraus k) =
          ∑ k, (before.kraus k)ᴴ *
            (∑ l, (after.kraus l)ᴴ * after.kraus l) * before.kraus k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp only [Matrix.mul_assoc]
      _ = ∑ k, (before.kraus k)ᴴ * before.kraus k := by
        rw [after.complete]
        simp
      _ = 1 := before.complete

/-- Composition acts by ordinary composition on arbitrary operators. -/
theorem KrausChannel.comp_mapOperator (after : KrausChannel R S L)
    (before : KrausChannel Q R K) (A : Operator Q) :
    (after.comp before).mapOperator A = after.mapOperator (before.mapOperator A) := by
  classical
  simp only [KrausChannel.comp, KrausChannel.mapOperator, Fintype.sum_prod_type]
  calc
    ∑ k, ∑ l,
        (after.kraus l * before.kraus k) * A *
          (after.kraus l * before.kraus k)ᴴ =
        ∑ l, after.kraus l *
          (∑ k, before.kraus k * A * (before.kraus k)ᴴ) *
          (after.kraus l)ᴴ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ l, after.kraus l *
          (before.mapOperator A) * (after.kraus l)ᴴ := rfl

/-- Composition acts by ordinary composition on density states. -/
theorem KrausChannel.comp_mapDensity (after : KrausChannel R S L)
    (before : KrausChannel Q R K) (rho : Density Q) :
    (after.comp before).mapDensity rho = after.mapDensity (before.mapDensity rho) := by
  apply Density.ext
  exact after.comp_mapOperator before rho.op

end Composition

end
end Information
end Deutsch
