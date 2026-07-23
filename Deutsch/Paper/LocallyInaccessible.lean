import Deutsch.EPR.Provenance

/-!
# Paper façade: locally inaccessible information

Source-shaped entries for Equations (38) and (39).
-/

namespace Deutsch
namespace Paper

open EPR Foundations

noncomputable section

/--
Equation (38): the displayed two-qubit ket is the circuit output with the explicit global phase
relating the source coordinates to the normalized physical state.
-/
theorem equation38 (theta : ℝ) :
    equation38Ket theta = (-Complex.I) • (pairPureState theta 0).ket :=
  equation38Ket_eq_globalPhase_pairPureState theta

/-- Equation (39): the two local rotation routes produce exactly the same physical ket. -/
theorem equation39 (theta : ℝ) :
    (leftRoutePureState theta).ket = (rightRoutePureState theta).ket :=
  equation39_route_pure_kets_eq theta

end
end Paper
end Deutsch
