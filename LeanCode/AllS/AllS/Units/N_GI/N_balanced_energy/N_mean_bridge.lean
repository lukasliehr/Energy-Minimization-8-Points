import AllS.Units.N_GI.N_balanced_energy.N_energy_inequality
import AllS.Units.N_GI.N_signed_mean.N_scalar_mean

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem balancedMean_eq_scaled (p : ℝ) (q : TangentCoordinates) :
    balancedMean p q=(p/tau)*contactMeanDelta q := by
  unfold balancedMean balancedX contactMeanDelta contactWeightedDelta
  simp only [mul_sub,Finset.sum_sub_distrib,balancedZ_mean,sub_zero]
  have hh : (∑ e : ContactIndex,contactWeight e*((p/tau)*contactDelta q e.1 (contactNext e)))=
      (p/tau)*(∑ e : ContactIndex,contactWeight e*contactDelta q e.1 (contactNext e)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hh]
  ring

theorem balancedMean_bound_of_cubic (hC : MeanCubicAbsorption) (p : ℝ) (hp : 0≤p)
    (q : TangentCoordinates) (hq : ‖q‖≤3/10) : balancedMean p q≤p*‖q‖^2/(5*tau) := by
  have h := mul_le_mul_of_nonneg_left (signed_mean_bound_of_cubic hC q hq).1 (div_nonneg hp tau_pos.le)
  rw [balancedMean_eq_scaled]
  convert! h using 1 <;> ring

#print axioms balancedMean_bound_of_cubic
end Blueprint.Thomson.Tail.Implementation
