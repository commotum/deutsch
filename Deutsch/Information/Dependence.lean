import Deutsch.Information.Reduction
import Deutsch.Information.Channel
import Deutsch.Descriptor.Basic

/-!
# Semantic information dependence

This module keeps several notions deliberately separate:

* equality of all effect probabilities and weak operational distinguishability;
* local independence/detectability after selected-subsystem reduction;
* exact recovery by a named state transformer;
* nonconstancy of a descriptor family; and
* explicit preparation/factorization history.

Weak distinguishability means that some effect has unequal probability. It does not mean perfect
single-shot discrimination. `DensityMap` is an extensional state transformer with no physicality
claim; physical transformations should normally be supplied by `KrausChannel.toDensityMap`.
-/

namespace Deutsch
namespace Information

open Register

noncomputable section

variable {Q R S Theta : Type*}
variable [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]
variable [Fintype S] [DecidableEq S]

/-- A parameter-indexed density-state family. -/
abbrev DensityFamily (Theta Q : Type*) [Fintype Q] [DecidableEq Q] :=
  Theta → Density Q

/-- Equality of every effect probability on a register. -/
def EffectStatisticallyEquivalent (rho sigma : Density Q) : Prop :=
  ∀ effect : Effect Q, bornProbability rho effect = bornProbability sigma effect

/-- Weak operational distinguishability: one effect has unequal probability. -/
def WeaklyDistinguishable (rho sigma : Density Q) : Prop :=
  ∃ effect : Effect Q, bornProbability rho effect ≠ bornProbability sigma effect

theorem weaklyDistinguishable_iff_not_effectStatisticallyEquivalent
    (rho sigma : Density Q) :
    WeaklyDistinguishable rho sigma ↔ ¬ EffectStatisticallyEquivalent rho sigma := by
  simp [WeaklyDistinguishable, EffectStatisticallyEquivalent]

theorem effectStatisticallyEquivalent_of_eq {rho sigma : Density Q}
    (h : rho = sigma) : EffectStatisticallyEquivalent rho sigma := by
  subst sigma
  intro effect
  rfl

theorem effectStatisticallyEquivalent_refl (rho : Density Q) :
    EffectStatisticallyEquivalent rho rho := by
  intro effect
  rfl

theorem effectStatisticallyEquivalent_symm {rho sigma : Density Q}
    (h : EffectStatisticallyEquivalent rho sigma) :
    EffectStatisticallyEquivalent sigma rho := by
  intro effect
  exact (h effect).symm

theorem effectStatisticallyEquivalent_trans {rho sigma tau : Density Q}
    (hrs : EffectStatisticallyEquivalent rho sigma)
    (hst : EffectStatisticallyEquivalent sigma tau) :
    EffectStatisticallyEquivalent rho tau := by
  intro effect
  exact (hrs effect).trans (hst effect)

/-- In finite dimension, statistical equivalence over all effects is exactly density equality. -/
theorem effectStatisticallyEquivalent_iff_eq (rho sigma : Density Q) :
    EffectStatisticallyEquivalent rho sigma ↔ rho = sigma := by
  exact (density_eq_iff_effect_probabilities rho sigma).symm

/-- Weak distinguishability over all effects is exactly inequality of density states. -/
theorem weaklyDistinguishable_iff_ne (rho sigma : Density Q) :
    WeaklyDistinguishable rho sigma ↔ rho ≠ sigma := by
  rw [weaklyDistinguishable_iff_not_effectStatisticallyEquivalent,
    effectStatisticallyEquivalent_iff_eq]

/-- Equality of density operators after restriction to `s`. -/
def ReducedStateEquivalent (s : Finset Q) (rho sigma : Density Q) : Prop :=
  rho.reduce s = sigma.reduce s

/-- Equality of all local effect probabilities after restriction to `s`. -/
def LocalEffectStatisticallyEquivalent (s : Finset Q)
    (rho sigma : Density Q) : Prop :=
  EffectStatisticallyEquivalent (rho.reduce s) (sigma.reduce s)

theorem localEffectStatisticallyEquivalent_of_reducedStateEquivalent
    (s : Finset Q) {rho sigma : Density Q}
    (h : ReducedStateEquivalent s rho sigma) :
    LocalEffectStatisticallyEquivalent s rho sigma :=
  effectStatisticallyEquivalent_of_eq h

/-- Reduced-state equality and equality of every local effect statistic coincide. -/
theorem reducedStateEquivalent_iff_localEffectStatisticallyEquivalent
    (s : Finset Q) (rho sigma : Density Q) :
    ReducedStateEquivalent s rho sigma ↔
      LocalEffectStatisticallyEquivalent s rho sigma := by
  exact (density_eq_iff_effect_probabilities (rho.reduce s) (sigma.reduce s)).trans
    (by rfl)

/-- Local statistics can equivalently be evaluated using globally embedded local effects. -/
theorem localEffectStatisticallyEquivalent_iff_embedded
    (s : Finset Q) (rho sigma : Density Q) :
    LocalEffectStatisticallyEquivalent s rho sigma ↔
      ∀ effect : Effect {q : Q // q ∈ s},
        bornProbability rho (effect.embedSubsystem s) =
          bornProbability sigma (effect.embedSubsystem s) := by
  constructor
  · intro h effect
    rw [← bornProbability_reduce rho s effect,
      ← bornProbability_reduce sigma s effect]
    exact h effect
  · intro h effect
    rw [bornProbability_reduce rho s effect,
      bornProbability_reduce sigma s effect]
    exact h effect

/-- A parameter family has the same statistics at every parameter value. -/
def StatisticsIndependent (family : Theta → Density Q) : Prop :=
  ∀ theta theta', EffectStatisticallyEquivalent (family theta) (family theta')

/-- Some pair of parameter values is weakly distinguishable. -/
def StatisticallyDetectable (family : Theta → Density Q) : Prop :=
  ∃ theta theta', WeaklyDistinguishable (family theta) (family theta')

theorem statisticallyDetectable_iff_not_statisticsIndependent
    (family : Theta → Density Q) :
    StatisticallyDetectable family ↔ ¬ StatisticsIndependent family := by
  simp [StatisticallyDetectable, StatisticsIndependent, WeaklyDistinguishable,
    EffectStatisticallyEquivalent]

theorem statisticsIndependent_iff_constant (family : Theta → Density Q) :
    StatisticsIndependent family ↔
      ∀ theta theta', family theta = family theta' := by
  constructor
  · intro h theta theta'
    exact (effectStatisticallyEquivalent_iff_eq _ _).mp (h theta theta')
  · intro h theta theta'
    exact effectStatisticallyEquivalent_of_eq (h theta theta')

theorem statisticallyDetectable_iff_exists_ne (family : Theta → Density Q) :
    StatisticallyDetectable family ↔
      ∃ theta theta', family theta ≠ family theta' := by
  constructor
  · rintro ⟨theta, theta', h⟩
    exact ⟨theta, theta', (weaklyDistinguishable_iff_ne _ _).mp h⟩
  · rintro ⟨theta, theta', h⟩
    exact ⟨theta, theta', (weaklyDistinguishable_iff_ne _ _).mpr h⟩

/-- Every selected-subsystem effect statistic is independent of the parameter. -/
def LocallyStatisticsIndependent (s : Finset Q) (family : Theta → Density Q) : Prop :=
  ∀ theta theta', LocalEffectStatisticallyEquivalent s (family theta) (family theta')

/-- Some effect on the reduced state of `s` detects a parameter difference. -/
def LocallyDetectable (s : Finset Q) (family : Theta → Density Q) : Prop :=
  ∃ theta theta', WeaklyDistinguishable ((family theta).reduce s) ((family theta').reduce s)

/-- Joint detectability on the union of two named subsystem sets. -/
def JointlyDetectable (s t : Finset Q) (family : Theta → Density Q) : Prop :=
  LocallyDetectable (s ∪ t) family

/-- A conservative operational reading of “locally inaccessible.” -/
def LocallyInaccessibleOn (localSubsystem jointSubsystem : Finset Q)
    (family : Theta → Density Q) : Prop :=
  LocallyStatisticsIndependent localSubsystem family ∧
    LocallyDetectable jointSubsystem family

/-- A detectable local change is also detectable on the full register by effect embedding. -/
theorem LocallyDetectable.statisticallyDetectable {s : Finset Q}
    {family : Theta → Density Q} (h : LocallyDetectable s family) :
    StatisticallyDetectable family := by
  rcases h with ⟨theta, theta', effect, hne⟩
  refine ⟨theta, theta', effect.embedSubsystem s, ?_⟩
  simpa only [bornProbability_reduce] using hne

/-- Joint statistical independence implies independence on every selected subsystem. -/
theorem StatisticsIndependent.locallyStatisticsIndependent
    {family : Theta → Density Q} (h : StatisticsIndependent family) (s : Finset Q) :
    LocallyStatisticsIndependent s family := by
  intro theta theta' effect
  simpa only [bornProbability_reduce] using
    h theta theta' (effect.embedSubsystem s)

/-- A fixed channel preserves equality of every effect statistic. -/
theorem KrausChannel.effectStatisticallyEquivalent_mapDensity
    {K : Type*} [Fintype K] (channel : KrausChannel Q R K)
    {rho sigma : Density Q} (h : EffectStatisticallyEquivalent rho sigma) :
    EffectStatisticallyEquivalent (channel.mapDensity rho) (channel.mapDensity sigma) := by
  intro effect
  rw [channel.bornProbability_mapDensity, channel.bornProbability_mapDensity]
  exact h (channel.dualEffect effect)

/-- Output detectability through a fixed channel pulls back to input detectability. -/
theorem KrausChannel.weaklyDistinguishable_input_of_output
    {K : Type*} [Fintype K] (channel : KrausChannel Q R K)
    {rho sigma : Density Q}
    (h : WeaklyDistinguishable (channel.mapDensity rho) (channel.mapDensity sigma)) :
    WeaklyDistinguishable rho sigma := by
  rcases h with ⟨effect, heffect⟩
  refine ⟨channel.dualEffect effect, ?_⟩
  simpa only [channel.bornProbability_mapDensity] using heffect

/-- Parameter independence is preserved by a fixed parameter-independent channel. -/
theorem KrausChannel.statisticsIndependent_mapDensity
    {K : Type*} [Fintype K] (channel : KrausChannel Q R K)
    {family : Theta → Density Q} (h : StatisticsIndependent family) :
    StatisticsIndependent (fun theta => channel.mapDensity (family theta)) := by
  intro theta theta'
  exact channel.effectStatisticallyEquivalent_mapDensity (h theta theta')

/-- An arbitrary extensional state transformer; no physicality is asserted by this type alone. -/
abbrev DensityMap (Q R : Type*) [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] := Density Q → Density R

def DensityMap.identity : DensityMap Q Q := id

def DensityMap.comp (after : DensityMap R S) (before : DensityMap Q R) : DensityMap Q S :=
  after ∘ before

/-- Forget a channel's selected Kraus representation while retaining its physical state action. -/
def KrausChannel.toDensityMap {K : Type*} [Fintype K]
    (channel : KrausChannel Q R K) : DensityMap Q R :=
  channel.mapDensity

/-- Exact recovery by a specified decoder/state transformer. -/
def Recovers (decoder : DensityMap R S)
    (encoded : Theta → Density R) (target : Theta → Density S) : Prop :=
  ∀ theta, decoder (encoded theta) = target theta

theorem Recovers.encoded_ne_of_target_ne
    {decoder : DensityMap R S} {encoded : Theta → Density R}
    {target : Theta → Density S} (h : Recovers decoder encoded target)
    {theta theta' : Theta} (hne : target theta ≠ target theta') :
    encoded theta ≠ encoded theta' := by
  intro hencoded
  apply hne
  rw [← h theta, ← h theta', hencoded]

/-- Physical exact recovery of a detectable target implies detectability of the encoding. -/
theorem StatisticallyDetectable.of_recovers_channel
    {K : Type*} [Fintype K]
    {encoded : Theta → Density Q} {target : Theta → Density R}
    (channel : KrausChannel Q R K)
    (hrec : Recovers channel.mapDensity encoded target)
    (hdetect : StatisticallyDetectable target) :
    StatisticallyDetectable encoded := by
  rcases hdetect with ⟨theta, theta', effect, hne⟩
  refine ⟨theta, theta', ?_⟩
  apply channel.weaklyDistinguishable_input_of_output
  refine ⟨effect, ?_⟩
  simpa only [hrec theta, hrec theta'] using hne

/-- Representation-dependent nonconstancy of a family of global descriptor operators. -/
def DescriptorFamilyNonconstant (family : Theta → DescriptorFamily Q) : Prop :=
  ∃ theta theta', family theta ≠ family theta'

/-- A parameterized descriptor family changes in a witnessed named component. -/
def DescriptorNonconstant (family : Theta → DescriptorFamily Q) : Prop :=
  ∃ theta theta' q axis,
    ((family theta) q).component axis ≠ ((family theta') q).component axis

theorem DescriptorNonconstant.not_constant
    {family : Theta → DescriptorFamily Q} (h : DescriptorNonconstant family) :
    ¬ (∀ theta theta', family theta = family theta') := by
  rcases h with ⟨theta, theta', q, axis, hne⟩
  intro hconstant
  apply hne
  rw [hconstant theta theta']

/--
Explicit preparation/factorization data. Equality of the final family does not identify or erase
the input and process fields.
-/
structure ProcessPreparation (Theta Q R : Type*)
    [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R] where
  input : Theta → Density Q
  process : DensityMap Q R
  output : Theta → Density R
  realizes : ∀ theta, process (input theta) = output theta

/-- Two possibly different preparation factorizations have the same final state family. -/
def ProcessPreparation.SameOutput
    {Q₁ Q₂ R : Type*} [Fintype Q₁] [DecidableEq Q₁]
    [Fintype Q₂] [DecidableEq Q₂] [Fintype R] [DecidableEq R]
    (first : ProcessPreparation Theta Q₁ R)
    (second : ProcessPreparation Theta Q₂ R) : Prop :=
  first.output = second.output

/--
An explicitly supplied history realizing a fixed final density family. The final family alone does
not manufacture the history, and `realize` carries no physicality claim without extra hypotheses.
-/
structure Preparation (family : DensityFamily Theta Q) (History : Type*) where
  history : Theta → History
  realize : History → Density Q
  realizes : ∀ theta, realize (history theta) = family theta

/-- The supplied provenance varies with the parameter. -/
def Preparation.ProvenanceNonconstant
    {History : Type*} {family : DensityFamily Theta Q}
    (preparation : Preparation family History) : Prop :=
  ∃ theta theta', preparation.history theta ≠ preparation.history theta'

/-- Any explicit history can accompany a constant final family via constant realization. -/
def constantPreparation {History : Type*} (rho : Density Q)
    (history : Theta → History) :
    Preparation (Theta := Theta) (fun _ : Theta => rho) History where
  history := history
  realize := fun _ => rho
  realizes := by intro theta; rfl

@[simp]
theorem constantPreparation_history {History : Type*} (rho : Density Q)
    (history : Theta → History) (theta : Theta) :
    (constantPreparation rho history).history theta = history theta := rfl

theorem constantPreparation_provenanceNonconstant {History : Type*}
    (rho : Density Q) (history : Theta → History)
    (h : ∃ theta theta', history theta ≠ history theta') :
    (constantPreparation rho history).ProvenanceNonconstant := by
  simpa [Preparation.ProvenanceNonconstant] using h

/-- Two arbitrary explicit histories can realize exactly the same constant final family. -/
theorem constantPreparations_same_final_family {History History' : Type*}
    (rho : Density Q) (left : Theta → History) (right : Theta → History') :
    ∀ theta,
      (constantPreparation rho left).realize
          ((constantPreparation rho left).history theta) =
        (constantPreparation rho right).realize
          ((constantPreparation rho right).history theta) := by
  intro theta
  rfl

end
end Information
end Deutsch
