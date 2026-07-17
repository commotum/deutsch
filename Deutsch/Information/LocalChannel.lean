import Deutsch.Information.Channel
import Deutsch.Information.Reduction
import Deutsch.Locality.Basic

/-!
# Channels on selected subsystems

A same-subsystem Kraus channel can be embedded into a larger named register by embedding each
Kraus operator. Its dual fixes every effect on a disjoint subsystem, so its Schrödinger action
preserves the entire disjoint reduced density for arbitrary, possibly entangled, inputs.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped Matrix BigOperators

noncomputable section

variable {Q K : Type*} [Fintype Q] [DecidableEq Q] [Fintype K]

/-- Embed a trace-preserving channel on `s` into the full register, acting identically off `s`. -/
def KrausChannel.onSubsystem (s : Finset Q)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K) :
    KrausChannel Q Q K where
  kraus k := Register.embedSubsystem s (channel.kraus k)
  complete := by
    classical
    calc
      ∑ k, (Register.embedSubsystem s (channel.kraus k))ᴴ *
          Register.embedSubsystem s (channel.kraus k) =
          ∑ k, Register.embedSubsystem s
            ((channel.kraus k)ᴴ * channel.kraus k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [embedSubsystem_conjTranspose, ← embedSubsystem_mul]
      _ = Register.embedSubsystem s
          (∑ k, (channel.kraus k)ᴴ * channel.kraus k) := by
        exact (map_sum (embedSubsystemAlgHom s)
          (fun k ↦ (channel.kraus k)ᴴ * channel.kraus k) Finset.univ).symm
      _ = 1 := by rw [channel.complete, embedSubsystem_one]

/-- The embedded local channel's dual fixes every operator on a disjoint subsystem. -/
theorem KrausChannel.onSubsystem_dualOperator_embedSubsystem_of_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K)
    (A : SubsystemOperator t) :
    (channel.onSubsystem s).dualOperator (Register.embedSubsystem t A) =
      Register.embedSubsystem t A := by
  classical
  unfold KrausChannel.dualOperator
  change (∑ k, (Register.embedSubsystem s (channel.kraus k))ᴴ *
      Register.embedSubsystem t A * Register.embedSubsystem s (channel.kraus k)) =
    Register.embedSubsystem t A
  have hcomplete := (channel.onSubsystem s).complete
  change (∑ k, (Register.embedSubsystem s (channel.kraus k))ᴴ *
      Register.embedSubsystem s (channel.kraus k)) = 1 at hcomplete
  calc
    ∑ k, (Register.embedSubsystem s (channel.kraus k))ᴴ *
          Register.embedSubsystem t A * Register.embedSubsystem s (channel.kraus k) =
        ∑ k, Register.embedSubsystem t A *
          ((Register.embedSubsystem s (channel.kraus k))ᴴ *
            Register.embedSubsystem s (channel.kraus k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [embedSubsystem_conjTranspose]
      rw [Locality.embedSubsystem_commute_of_disjoint hst
        (channel.kraus k)ᴴ A]
      simp only [Matrix.mul_assoc]
    _ = Register.embedSubsystem t A *
        ∑ k, (Register.embedSubsystem s (channel.kraus k))ᴴ *
          Register.embedSubsystem s (channel.kraus k) := by
      rw [Matrix.mul_sum]
    _ = Register.embedSubsystem t A := by
      rw [hcomplete, Matrix.mul_one]

/-- The embedded local channel's dual fixes every effect on a disjoint subsystem. -/
theorem KrausChannel.onSubsystem_dualEffect_embedSubsystem_of_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K)
    (effect : Effect {q : Q // q ∈ t}) :
    (channel.onSubsystem s).dualEffect (effect.embedSubsystem t) =
      effect.embedSubsystem t := by
  apply Effect.ext
  exact channel.onSubsystem_dualOperator_embedSubsystem_of_disjoint hst effect.op

/-- A local channel leaves every disjoint embedded effect probability unchanged. -/
theorem KrausChannel.onSubsystem_bornProbability_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K)
    (rho : Density Q) (effect : Effect {q : Q // q ∈ t}) :
    bornProbability ((channel.onSubsystem s).mapDensity rho)
        (effect.embedSubsystem t) =
      bornProbability rho (effect.embedSubsystem t) := by
  rw [(channel.onSubsystem s).bornProbability_mapDensity]
  rw [channel.onSubsystem_dualEffect_embedSubsystem_of_disjoint hst effect]

/-- A local channel preserves the full density state on every disjoint selected subsystem. -/
theorem KrausChannel.onSubsystem_reduce_disjoint
    {s t : Finset Q} (hst : Disjoint s t)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K)
    (rho : Density Q) :
    ((channel.onSubsystem s).mapDensity rho).reduce t = rho.reduce t := by
  rw [density_eq_iff_effect_probabilities]
  intro effect
  rw [bornProbability_reduce, bornProbability_reduce]
  exact channel.onSubsystem_bornProbability_disjoint hst rho effect

end
end Information
end Deutsch
