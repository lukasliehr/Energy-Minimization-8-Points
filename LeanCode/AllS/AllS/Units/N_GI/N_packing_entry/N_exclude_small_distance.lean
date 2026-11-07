import AllS.Units.N_GI.N_packing_entry.N_force_threshold

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem packing_entry_exclude_small_distance (p : ℝ) (hp : (97:ℝ)/2≤p)
    (Y : Fin 8→Point) (hY : IsConfiguration Y) (hstat : Stationary p Y)
    (henergy : tau^p*squaredEnergy p Y≤ceiling)
    (m : ℝ) (hm : 0< m) (hlower : ∀ i j : Fin 8, i≠j → m≤ squaredDistance Y i j)
    (hatt : ∃ i j : Fin 8, i≠j ∧ squaredDistance Y i j=m) : entryDistance< m := by
  by_contra hnot
  have hsmall : m≤entryDistance := le_of_not_gt hnot
  have hforce := force_bound.2 p m entryDistance Y hY (by linarith) hstat hm hsmall entryDistance_bounds.2.le hlower hatt
  have hE := mul_le_mul_of_nonneg_left hforce (Real.rpow_nonneg tau_pos.le p)
  have he : tau^p*(forceFactor entryDistance*entryDistance^(-p))=forceFactor entryDistance*(tau/entryDistance)^p := by
    have hh : tau^p*entryDistance^(-p)=(tau/entryDistance)^p := by
      rw [Real.rpow_def_of_pos tau_pos,Real.rpow_def_of_pos entryDistance_bounds.1,Real.rpow_def_of_pos (div_pos tau_pos entryDistance_bounds.1),
        ←Real.exp_add,Real.log_div tau_pos.ne' entryDistance_bounds.1.ne']
      congr 1
      ring
    calc
      _ = forceFactor entryDistance*(tau^p*entryDistance^(-p)) := by ring
      _ = _ := by rw [hh]
  rw [he] at hE
  have hbound := hE.trans henergy
  have hstrict := force_entry_strict p hp
  dsimp [ceiling] at hbound
  linarith

theorem stationary_sublevel_separation (p : ℝ) (hp : (97:ℝ)/2≤p)
    (Y : Fin 8→Point) (hY : IsConfiguration Y) (hstat : Stationary p Y)
    (henergy : tau^p*squaredEnergy p Y≤ceiling) :
    ∀ i j : Fin 8, i≠j → entryDistance<squaredDistance Y i j := by
  obtain ⟨m,hm,hlower,hatt,_,_⟩ := packing_entry_minimum_attained Y hY
  have h := packing_entry_exclude_small_distance p hp Y hY hstat henergy m hm hlower hatt
  exact fun i j hij=>h.trans_le (hlower i j hij)

#print axioms packing_entry_exclude_small_distance
#print axioms stationary_sublevel_separation
end Blueprint.Thomson.Tail.Implementation
