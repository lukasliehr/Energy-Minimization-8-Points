import AllS.Units.N_GI.N_localization.N_chord_from_product
import AllS.Units.N_GI.N_nearest_chart.N_assemble
import AllS.Units.N_AI.N_elementary_series.N_log_geometric

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem product_threshold_log_bound :
    -2*log (239/250:ℝ)≤4032919/44812500 ∧ (4032919/44812500:ℝ)<9/100 := by
  have h := (Blueprint.CAP.elementary_series_log_geometric (11/489) 0 (by norm_num) (by norm_num)).2
  have ha : ((1+(11/489:ℝ))/(1-11/489))=(239/250:ℝ)⁻¹ := by norm_num
  rw [ha,Real.log_inv] at h
  norm_num [Blueprint.CAP.logOddPartial,Finset.sum_range_succ] at h
  constructor
  · linarith
  · norm_num

theorem localization_rational_log_bound (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hg : (239/250:ℝ)≤productGauge Y) : chordOrbitRadius Y<3/10 := by
  have hp : 0<productGauge Y := lt_of_lt_of_le (by norm_num) hg
  obtain ⟨U,σ,hch,hmin⟩ := localization_chord_from_product Y hY hp
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<239/250) hg
  have hsq := chordOrbitRadius_sq Y hY
  have hconst := product_threshold_log_bound
  have hrad : 0≤chordOrbitRadius Y := Real.sqrt_nonneg _
  nlinarith [hch,hmin,hlog,hsq,hconst.1,hconst.2]

#print axioms product_threshold_log_bound
#print axioms localization_rational_log_bound
end Blueprint.Thomson.Tail.Implementation
