import Deutsch.Information
import Mathlib.Tactic

/-!
# Information verification

Focused Stage 7 regressions for general Born bounds, computational-basis measurements, selected
subsystem reduction, one-qubit tomography, mixed-state fixed-reference obstruction, finite
channels, semantic detectability, exact recovery, and explicit provenance.
-/

namespace DeutschTests
namespace InformationVerification

open Deutsch Deutsch.Foundations Deutsch.Information Deutsch.Register
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

/-! ## Born probabilities and computational-basis effects -/

theorem arbitrary_born_probability_is_bounded
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (effect : Effect Q) :
    bornProbability rho effect ∈ Set.Icc 0 1 :=
  bornProbability_mem_Icc rho effect

def rawZeroOne : Basis (Fin 1) := fun _ => 0

def rawOneOne : Basis (Fin 1) := fun _ => 1

theorem rawZeroOne_ne_rawOneOne : rawZeroOne ≠ rawOneOne := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  norm_num [rawZeroOne, rawOneOne] at h0

theorem computational_basis_hit_is_certain :
    bornProbability (basisDensity rawZeroOne) (basisEffect rawZeroOne) = 1 := by
  simpa using basisDensity_basisEffect_probability rawZeroOne rawZeroOne

theorem computational_basis_miss_is_impossible :
    bornProbability (basisDensity rawZeroOne) (basisEffect rawOneOne) = 0 := by
  simpa [rawZeroOne_ne_rawOneOne] using
    basisDensity_basisEffect_probability rawZeroOne rawOneOne

theorem computational_basis_measurement_normalizes
    {Q : Type*} [Fintype Q] [DecidableEq Q] (rho : Density Q) :
    ∑ bits, bornProbability rho ((computationalBasisPOVM Q).effect bits) = 1 :=
  bornProbabilities_normalize rho (computationalBasisPOVM Q)

theorem binary_effect_measurement_normalizes
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (effect : Effect Q) :
    ∑ outcome, bornProbability rho (effect.binaryPOVM.effect outcome) = 1 :=
  bornProbabilities_normalize rho effect.binaryPOVM

theorem paper_bit_one_is_the_z_plus_effect
    {Q : Type*} [Fintype Q] [DecidableEq Q] (q : Q) :
    (zPlusEffect q).op = paperBitOneProjectorAt q :=
  zPlusEffect_op_eq_paperBitOneProjectorAt q

theorem pure_density_uses_existing_expectation
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (psi : PureState Q) (A : Operator Q) :
    densityExpectation (pureDensity psi) A = Register.expectation psi.ket A :=
  densityExpectation_pureDensity psi A

/-! ## Reduction and one-qubit tomography -/

theorem partial_trace_preserves_trace
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (s : Finset Q) (A : Operator Q) :
    (partialTrace s A).trace = A.trace :=
  partialTrace_trace s A

theorem partial_trace_preserves_positivity
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (s : Finset Q) {A : Operator Q} (hA : A.PosSemidef) :
    (partialTrace s A).PosSemidef :=
  partialTrace_posSemidef s hA

theorem reduced_local_effect_has_global_probability
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (s : Finset Q)
    (effect : Effect {q : Q // q ∈ s}) :
    bornProbability (rho.reduce s) effect =
      bornProbability rho (effect.embedSubsystem s) :=
  bornProbability_reduce rho s effect

theorem one_qubit_all_effects_determine_density
    {rho sigma : Density (Fin 1)} :
    rho = sigma ↔
      ∀ effect : Effect (Fin 1),
        bornProbability rho effect = bornProbability sigma effect :=
  density_eq_iff_effect_probabilities rho sigma

theorem arbitrary_register_all_effects_determine_density
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho sigma : Density Q) :
    rho = sigma ↔
      ∀ effect : Effect Q,
        bornProbability rho effect = bornProbability sigma effect :=
  density_eq_iff_effect_probabilities rho sigma

theorem one_qubit_pauli_statistics_determine_density
    {rho sigma : Density (Fin 1)}
    (hX : bornProbability rho (xPlusEffect 0) =
      bornProbability sigma (xPlusEffect 0))
    (hY : bornProbability rho (yPlusEffect 0) =
      bornProbability sigma (yPlusEffect 0))
    (hZ : bornProbability rho (zPlusEffect 0) =
      bornProbability sigma (zPlusEffect 0)) :
    rho = sigma :=
  density_eq_of_pauliPlus_probabilities 0 hX hY hZ

theorem singleton_reduction_is_exactly_all_local_statistics
    {Q : Type*} [Fintype Q] [DecidableEq Q] (q : Q)
    {rho sigma : Density Q} :
    rho.reduce {q} = sigma.reduce {q} ↔
      ∀ effect : Effect {r : Q // r ∈ ({q} : Finset Q)},
        bornProbability rho (effect.embedSubsystem {q}) =
          bornProbability sigma (effect.embedSubsystem {q}) :=
  reduce_singleton_eq_iff_embedded_effect_probabilities q

theorem arbitrary_reduction_is_exactly_all_local_statistics
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (s : Finset Q) (rho sigma : Density Q) :
    rho.reduce s = sigma.reduce s ↔
      ∀ effect : Effect {q : Q // q ∈ s},
        bornProbability rho (effect.embedSubsystem s) =
          bornProbability sigma (effect.embedSubsystem s) :=
  reduced_density_eq_iff_embedded_effect_probabilities s rho sigma

/-! ## Mixed-state boundary -/

theorem maximally_mixed_not_fixed_pure_reference
    (U : Operator (Fin 1))
    (hU : U ∈ Matrix.unitaryGroup (Basis (Fin 1)) ℂ) :
    maximallyMixedQubit.evolve U hU ≠ referenceDensity (Fin 1) :=
  maximallyMixedQubit_cannot_evolve_to_reference U hU

/-! ## Channels and data processing -/

theorem identity_channel_fixes_every_density
    {Q : Type*} [Fintype Q] [DecidableEq Q] (rho : Density Q) :
    (identityChannel Q).mapDensity rho = rho :=
  identityChannel_mapDensity rho

theorem channel_duality_preserves_born_probability
    {Q R K : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] [Fintype K]
    (channel : KrausChannel Q R K) (rho : Density Q) (effect : Effect R) :
    bornProbability (channel.mapDensity rho) effect =
      bornProbability rho (channel.dualEffect effect) :=
  channel.bornProbability_mapDensity rho effect

theorem channel_composition_has_expected_density_action
    {Q R S K L : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype K] [Fintype L]
    (after : KrausChannel R S L) (before : KrausChannel Q R K)
    (rho : Density Q) :
    (after.comp before).mapDensity rho =
      after.mapDensity (before.mapDensity rho) :=
  after.comp_mapDensity before rho

theorem fixed_channel_preserves_parameter_independence
    {Q R K Theta : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] [Fintype K]
    (channel : KrausChannel Q R K) (family : Theta → Density Q)
    (h : StatisticsIndependent family) :
    StatisticsIndependent (fun theta => channel.mapDensity (family theta)) :=
  channel.statisticsIndependent_mapDensity h

theorem local_channel_preserves_every_disjoint_reduced_state
    {Q K : Type*} [Fintype Q] [DecidableEq Q] [Fintype K]
    {s t : Finset Q} (hst : Disjoint s t)
    (channel : KrausChannel {q : Q // q ∈ s} {q : Q // q ∈ s} K)
    (rho : Density Q) :
    ((channel.onSubsystem s).mapDensity rho).reduce t = rho.reduce t :=
  channel.onSubsystem_reduce_disjoint hst rho

/-! ## Semantic detectability, recovery, and provenance -/

theorem different_basis_states_are_weakly_distinguishable :
    WeaklyDistinguishable (basisDensity rawZeroOne) (basisDensity rawOneOne) := by
  refine ⟨basisEffect rawZeroOne, ?_⟩
  rw [computational_basis_hit_is_certain]
  have h := basisDensity_basisEffect_probability rawOneOne rawZeroOne
  rw [if_neg (Ne.symm rawZeroOne_ne_rawOneOne)] at h
  rw [h]
  norm_num

theorem all_effect_statistics_equal_iff_density_equal
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho sigma : Density Q) :
    EffectStatisticallyEquivalent rho sigma ↔ rho = sigma :=
  effectStatisticallyEquivalent_iff_eq rho sigma

def basisBitFamily : Bool → Density (Fin 1)
  | false => basisDensity rawZeroOne
  | true => basisDensity rawOneOne

theorem basis_bit_family_is_detectable : StatisticallyDetectable basisBitFamily := by
  exact ⟨false, true, different_basis_states_are_weakly_distinguishable⟩

theorem constant_family_is_statistically_independent
    {Q Theta : Type*} [Fintype Q] [DecidableEq Q] (rho : Density Q) :
    StatisticsIndependent (fun _ : Theta => rho) := by
  intro theta theta'
  exact effectStatisticallyEquivalent_refl rho

theorem identity_channel_recovers_exactly
    {Q Theta : Type*} [Fintype Q] [DecidableEq Q]
    (family : Theta → Density Q) :
    Recovers (identityChannel Q).mapDensity family family := by
  intro theta
  exact identityChannel_mapDensity (family theta)

theorem constant_final_family_can_have_nonconstant_provenance
    {Q : Type*} [Fintype Q] [DecidableEq Q] (rho : Density Q) :
    (constantPreparation (Theta := Bool) rho id).ProvenanceNonconstant := by
  apply constantPreparation_provenanceNonconstant
  exact ⟨false, true, by decide⟩

/-! ## Classical one-time-pad boundary -/

theorem one_time_pad_each_singleton_is_secret_independent (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2)) oneTimePadDensity :=
  oneTimePad_locallyStatisticsIndependent q

theorem one_time_pad_parity_reads_secret_with_certainty (secret : QubitIndex) :
    bornProbability (oneTimePadDensity secret) (parityEffect secret) = 1 := by
  rw [oneTimePadDensity_parity_probability]
  simp

theorem one_time_pad_encodings_are_jointly_detectable :
    StatisticallyDetectable oneTimePadDensity :=
  oneTimePad_statisticallyDetectable

theorem one_time_pad_physical_decoder_recovers :
    Recovers parityDecoder.mapDensity oneTimePadDensity
      (fun secret ↦ basisDensity (oneTimePadDecodedBasis secret)) :=
  parityDecoder_recovers

theorem one_time_pad_histories_are_pointwise_distinct (secret : QubitIndex) :
    oneTimePadPreparationLeft.history secret ≠
      oneTimePadPreparationRight.history secret :=
  oneTimePad_preparation_histories_distinct secret

theorem one_time_pad_distinct_histories_have_same_final_density
    (secret : QubitIndex) :
    oneTimePadPreparationLeft.realize
        (oneTimePadPreparationLeft.history secret) =
      oneTimePadPreparationRight.realize
        (oneTimePadPreparationRight.history secret) :=
  oneTimePad_preparations_same_final_density secret

end
end InformationVerification
end DeutschTests
