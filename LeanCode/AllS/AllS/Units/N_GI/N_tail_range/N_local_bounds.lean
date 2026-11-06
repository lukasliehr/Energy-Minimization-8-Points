import AllS.Units.N_GI.N_outer_annulus.N_energy_bridge
import AllS.Units.N_GI.N_continuous_annulus.N_contraction_helpers
import AllS.Units.N_GI.N_packing_entry.N_exclude_small_distance
import AllS.Units.N_GI.N_localization.N_from_boundary
import AllS.Units.N_GI.N_convex_domain.N_sublevel_bridge
import AllS.Units.N_G.N_nearest_chart
import AllS.Units.N_GI.N_upstream_bridge.N_energy

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

/-- The three remaining local estimates. This structure is a hypothesis bundle,
not a certificate or an assertion that the estimates have been proved. -/
structure TailLocalBounds : Prop where
  quadratic : ∀ q : TangentCoordinates, q∈rotationSlice → ‖q‖≤3/10 →
    contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2
  variance : ∀ q : TangentCoordinates, q∈rotationSlice → ‖q‖≤3/10 →
    outerF ‖q‖≤contactNorm (contactCenter (contactDeltaArray q))
  mean : ∀ p : ℝ, (97:ℝ)/2≤p → ∀ q : TangentCoordinates, q∈rotationSlice → ‖q‖≤3/10 →
    balancedMean p q≤p*‖q‖^2/(5*tau)

theorem squaredEnergy_congruent (p : ℝ) {Y Z : Fin 8→Point} (h : Thomson.Congruent Y Z) :
    squaredEnergy p Y=squaredEnergy p Z := by
  rw [squaredEnergy_eq_upstream,squaredEnergy_eq_upstream]
  exact SquareAntiprismVerification.congruent_energy ((Blueprint.congruence_bridge Y Z).mp h)

theorem stationary_orbit_bound_of_boundary (hcap : BoundarySOSInfeasible)
    (p : ℝ) (hp : (97:ℝ)/2≤p) (Y : Fin 8→Point) (hY : IsConfiguration Y)
    (hstat : Stationary p Y) (henergy : tau^p*squaredEnergy p Y≤ceiling) : chordOrbitRadius Y<3/10 := by
  have hsep := stationary_sublevel_separation p hp Y hY hstat henergy
  have hd : ∀ i j : Fin 8,i≠j → tau-gap ≤ squaredDistance Y i j := by
    intro i j hij
    have hh := hsep i j hij
    dsimp [entryDistance,gap] at hh ⊢
    linarith
  obtain ⟨U,σ,hclose⟩ := localization_from_checked_polynomials hcap Y hY.1 hd
  have hmin := chordOrbitSquare_le_gaugeChordSquare Y
    (U.toLinearIsometry.toContinuousLinearMap,σ) ⟨U.norm_map,Set.mem_univ _⟩
  change chordOrbitSquare Y≤∑ i : Fin 8,‖U (Y (σ i))-packingReference i‖^2 at hmin
  have hs := chordOrbitRadius_sq Y hY.1
  have hrad : 0≤chordOrbitRadius Y := Real.sqrt_nonneg _
  dsimp [radius] at hclose
  nlinarith

theorem stationary_chart_of_local_bounds (hcap : BoundarySOSInfeasible) (hb : TailLocalBounds)
    (p : ℝ) (hp : (97:ℝ)/2≤p) (Y : Fin 8→Point) (hY : IsConfiguration Y)
    (hstat : Stationary p Y) (henergy : tau^p*squaredEnergy p Y≤ceiling) :
    ∃ q : TangentCoordinates, q∈convexTailDomain p ∧ Thomson.Congruent (orthographicChart q) Y ∧
      squaredEnergy p (orthographicChart q)=squaredEnergy p Y := by
  have hrad := stationary_orbit_bound_of_boundary hcap p hp Y hY hstat henergy
  obtain ⟨U,σ,q,hqV,hq1,hal,hch,hnlo,hnhi⟩ := (nearest_chart Y hY.1 (by linarith)).1
  have hc : Thomson.Congruent (orthographicChart q) Y := ⟨U,σ,hal⟩
  have he := squaredEnergy_congruent p hc
  have hrad0 : 0≤chordOrbitRadius Y := Real.sqrt_nonneg _
  have hq3 : ‖q‖≤3/10 := by nlinarith [norm_nonneg q]
  have hEq : tau^p*squaredEnergy p (orthographicChart q)≤ceiling := by rwa [he]
  have hmean := hb.mean p hp q hqV hq3
  have hsharp := hb.variance q hqV hq3
  have hM := hb.quadratic q hqV hq3
  have hr6 := outer_annulus_of_sharp_mean p hp q hq3 hsharp hmean hEq
  have hrK := continuous_annulus_of_quadratic_mean p hp q hqV hq3 hr6 hM hmean hEq
  exact ⟨q,convexDomain_of_small_sublevel p hp q hqV hrK.le hEq,hc,he⟩

#print axioms squaredEnergy_congruent
#print axioms stationary_chart_of_local_bounds
end Blueprint.Thomson.Tail.Implementation
