import AllS.Units.N_GI.N_tail_range.N_local_bounds
import AllS.Units.N_GI.N_tail_range.N_strict_segment
import AllS.Units.N_G.N_minimizer_exists
import AllS.Units.N_G.N_trial_ceiling
import AllS.Units.N_GI.N_product_gauge.N_orbit

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

/-- Exact tail-range assembly. Its two explicit premises remain separate proof
obligations; this is not the unconditional target theorem. -/
theorem tail_range_of_boundary_and_local_bounds (hcap : BoundarySOSInfeasible)
    (hb : TailLocalBounds) : TailRangeSpec := by
  intro s hs a ha hFa
  let p : ℝ := s/2
  have hp : (97:ℝ)/2≤ p := by dsimp [p];linarith
  have hpP : 0< p := by linarith
  have h2p : 2*p=s := by dsimp [p];ring
  have hF : F (2*p) a=0 := by rwa [h2p]
  have hXa := Blueprint.antiprism_is_configuration a ha
  have hstatXa := (stationary_chart p a ha hF).1
  have hceiling := (trial_ceiling p hp).2.2.1 a ha hF
  obtain ⟨qh,hqh,hch,hEh⟩ := stationary_chart_of_local_bounds hcap hb p hp (X a) hXa hstatXa hceiling.le
  obtain ⟨Z,hZ,hstatZ,hZX,hglobZ,hZsep,hZmin,hZdist⟩ := minimizer_exists p (X a) hpP hXa
  have hZE := (trial_ceiling p hp).2.2.2 Z hglobZ
  obtain ⟨qZ,hqZ,hcZ,hEZ⟩ := stationary_chart_of_local_bounds hcap hb p hp Z hZ hstatZ hZE.le
  have hcandidate : squaredEnergy p (X a)≤ squaredEnergy p Z := by
    have h := (tail_range_strict_segment p a hp ha hF qh qZ hqh hqZ hch).1
    rwa [hEh,hEZ] at h
  have hglobal (Y : Fin 8→Point) (hY : IsConfiguration Y) :
      squaredEnergy p (X a)≤ squaredEnergy p Y := hcandidate.trans (hglobZ Y hY)
  have heq (Y : Fin 8→Point) (hY : IsConfiguration Y) :
      squaredEnergy p Y=squaredEnergy p (X a) ↔ Thomson.Congruent Y (X a) := by
    constructor
    · intro hEq
      have hYglob (W : Fin 8→Point) (hW : IsConfiguration W) : squaredEnergy p Y≤ squaredEnergy p W := by
        rw [hEq]
        exact hglobal W hW
      have hYstat := minimizer_exists_stationarity p Y hY hYglob
      have hYE : tau^p*squaredEnergy p Y≤ ceiling := by rw [hEq];exact hceiling.le
      obtain ⟨q,hq,hc,hE⟩ := stationary_chart_of_local_bounds hcap hb p hp Y hY hYstat hYE
      have hcompare := (tail_range_strict_segment p a hp ha hF qh q hqh hq hch).2
      have hqq : q=qh := hcompare.mp (by rw [hEh,hE,hEq])
      apply gauge_congruent_trans (gauge_congruent_symm hc)
      rw [hqq]
      exact hch
    · intro hc
      exact squaredEnergy_congruent p hc
  refine ⟨hXa,?_⟩
  intro Y hY
  have hEs (W : Fin 8→Point) : E s W=squaredEnergy p W :=
    (upstream_bridge_energy s (by linarith) W).1
  rw [hEs (X a),hEs Y]
  exact ⟨hglobal Y hY,heq Y hY⟩

#print axioms tail_range_of_boundary_and_local_bounds
end Blueprint.Thomson.Tail.Implementation
