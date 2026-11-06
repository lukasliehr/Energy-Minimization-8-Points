import AllS.Units.N_G.N_upstream_bridge
import Lean_Code.Stationarity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem stationary_chart_sphere_stationarity (p a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hF : F (2*p) a=0) : Stationary p (X a) ∧
      ∀ Y : Fin 8 → Point, Thomson.Congruent Y (X a) → Stationary p Y := by
  constructor
  · intro γ hγ0 hd hu
    have h := SquareAntiprismVerification.antiprism_curve_stationary p a ha hF γ
      (hγ0.trans (Blueprint.antiprism_coordinates a).symm) hd hu
    simpa only [squaredEnergy_eq_upstream] using h
  · intro Y hcong γ hγ0 hd hu
    have hc : SquareAntiprismVerification.Congruent (γ 0) (SquareAntiprismVerification.X a) := by
      rw [hγ0,Blueprint.antiprism_coordinates]
      exact (upstream_bridge_congruence Y (X a)).2.mp hcong
    have h := SquareAntiprismVerification.congruent_curve_stationary p a ha hF γ hc hd hu
    simpa only [squaredEnergy_eq_upstream] using h

#check stationary_chart_sphere_stationarity
#print axioms stationary_chart_sphere_stationarity
end Blueprint.Thomson.Tail.Implementation
