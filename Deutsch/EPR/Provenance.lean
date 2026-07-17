import Deutsch.EPR.Pair
import Deutsch.EPR.Statistics
import Deutsch.Information.Dependence

/-!
# EPR preparation provenance

Equation (39) identifies two distinct local preparation routes on the EPR resource.  This module
turns those routes into physical pure and density outputs, proves that their final density family
is the same, and retains the chosen route as explicit history data rather than attempting to infer
it from the final density operator.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Information Register

noncomputable section

/-- Physical pure output obtained by rotating the first EPR coordinate by `theta`. -/
def leftRoutePureState (theta : ℝ) : PureState (Fin 2) :=
  referencePairPureState.evolve (leftRotationRoute theta)
    (leftRotationRoute_unitary theta)

/-- Physical pure output obtained by rotating the second EPR coordinate by `-theta`. -/
def rightRoutePureState (theta : ℝ) : PureState (Fin 2) :=
  referencePairPureState.evolve (rightRotationRoute theta)
    (rightRotationRoute_unitary theta)

/-- Density output of the left Equation (39) route. -/
def leftRouteDensity (theta : ℝ) : Density (Fin 2) :=
  pureDensity (leftRoutePureState theta)

/-- Density output of the right Equation (39) route. -/
def rightRouteDensity (theta : ℝ) : Density (Fin 2) :=
  pureDensity (rightRoutePureState theta)

theorem equation39_route_pure_kets_eq (theta : ℝ) :
    (leftRoutePureState theta).ket = (rightRoutePureState theta).ket :=
  equation39_route_kets_eq theta

private theorem pureDensity_eq_of_ket_eq
    {psi chi : PureState (Fin 2)} (h : psi.ket = chi.ket) :
    pureDensity psi = pureDensity chi := by
  apply Density.ext
  simp only [pureDensity, densityOfVector]
  rw [h]

/-- Density form of Equation (39): the two physical routes have exactly the same output. -/
theorem equation39_route_densities_eq (theta : ℝ) :
    leftRouteDensity theta = rightRouteDensity theta := by
  exact pureDensity_eq_of_ket_eq (equation39_route_pure_kets_eq theta)

theorem pairCircuit_theta_zero_eq_leftRotationRoute (theta : ℝ) :
    pairCircuit theta 0 = leftRotationRoute theta := by
  simp [pairCircuit, pairRotations, leftRotationRoute, rotationXAt,
    rotationX_zero, Foundations.identity₂]

theorem leftRoutePureState_ket_eq_pairPureState (theta : ℝ) :
    (leftRoutePureState theta).ket = (pairPureState theta 0).ket := by
  change act (leftRotationRoute theta) (referenceKet (Fin 2)) =
    act (pairCircuit theta 0) (referenceKet (Fin 2))
  rw [pairCircuit_theta_zero_eq_leftRotationRoute]

/-- The left route is the `phi = 0` member of the public EPR density family. -/
theorem leftRouteDensity_eq_pairDensity (theta : ℝ) :
    leftRouteDensity theta = pairDensity theta 0 := by
  exact pureDensity_eq_of_ket_eq (leftRoutePureState_ket_eq_pairPureState theta)

/-- Equation (39) puts the right route in that same public `phi = 0` density family. -/
theorem rightRouteDensity_eq_pairDensity (theta : ℝ) :
    rightRouteDensity theta = pairDensity theta 0 := by
  exact (equation39_route_densities_eq theta).symm.trans
    (leftRouteDensity_eq_pairDensity theta)

/-- Explicit construction history retained independently of the final density operator. -/
inductive RouteHistory where
  | left (theta : ℝ)
  | right (theta : ℝ)

/-- Physical realization of either explicit history. -/
def routeHistoryDensity : RouteHistory → Density (Fin 2)
  | .left theta => leftRouteDensity theta
  | .right theta => rightRouteDensity theta

/-- The preparation whose supplied history chooses the first-coordinate route. -/
def leftRoutePreparation :
    Preparation (fun theta : ℝ ↦ pairDensity theta 0) RouteHistory where
  history := RouteHistory.left
  realize := routeHistoryDensity
  realizes := leftRouteDensity_eq_pairDensity

/-- The preparation whose supplied history chooses the second-coordinate route. -/
def rightRoutePreparation :
    Preparation (fun theta : ℝ ↦ pairDensity theta 0) RouteHistory where
  history := RouteHistory.right
  realize := routeHistoryDensity
  realizes := rightRouteDensity_eq_pairDensity

/-- The route tags remain pointwise distinct even though their final density family agrees. -/
theorem routePreparation_histories_distinct (theta : ℝ) :
    leftRoutePreparation.history theta ≠
      rightRoutePreparation.history theta := by
  simp [leftRoutePreparation, rightRoutePreparation]

/-- Both explicit histories physically realize the same final EPR density at every angle. -/
theorem routePreparations_same_final_density (theta : ℝ) :
    leftRoutePreparation.realize (leftRoutePreparation.history theta) =
      rightRoutePreparation.realize (rightRoutePreparation.history theta) := by
  exact (leftRoutePreparation.realizes theta).trans
    (rightRoutePreparation.realizes theta).symm

end
end EPR
end Deutsch
