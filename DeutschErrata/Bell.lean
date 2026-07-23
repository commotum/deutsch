import Deutsch.Bell.Moments
import DeutschErrata.Equation45

/-!
# Equation (45) and the endpoint of Equation (46)

The elementary comparison lives in `DeutschErrata.Equation45`.  This module records
that the complementary form is the one used by the direct finite-moment derivation,
whose displayed Equation-(46) chain ends in a contradiction.
-/

namespace DeutschErrata
namespace Bell

open Deutsch

/-- The real zero-one form used by the finite-moment derivation is a universal partition. -/
theorem equation45_derived_real_partition (a₀ a₁ a₂ : Bool) :
    Deutsch.Bell.booleanIndicator a₀ =
      Deutsch.Bell.booleanIndicator a₀ *
          Deutsch.Bell.disjunctionIndicator a₁ a₂ +
        Deutsch.Bell.booleanIndicator a₀ *
          (1 - Deutsch.Bell.disjunctionIndicator a₁ a₂) :=
  Deutsch.Bell.equation45_complementary_partition a₀ a₁ a₂

/--
With that partition, the direct corrected Equations (42)--(46) moment contract is
inconsistent.  This uses the displayed finite-moment chain, not the independent
agreement/pigeonhole proof.
-/
theorem equation46_derived_form_contradiction
    {Ω : Type*} [Fintype Ω]
    (space : Deutsch.Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces :
      Deutsch.Bell.ReproducesThreeSettingEPRMoments space alice bob) :
    False :=
  Deutsch.Bell.equation46_contradiction space alice bob reproduces

end Bell
end DeutschErrata
