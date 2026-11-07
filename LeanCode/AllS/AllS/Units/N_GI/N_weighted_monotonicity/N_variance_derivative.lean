import AllS.Units.N_GI.N_weighted_monotonicity.N_mass_derivative

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def twoValueVarianceDeriv (W v z : ℝ) : ℝ :=
  √(z*(W-z)/W)*(exp (v*twoValueB W z)-exp (-v*twoValueA W z))

theorem weighted_monotonicity_variance_derivative (W v z : ℝ) (hv : 0 < v)
    (hz : 0 < z) (hzW : z < W) :
    HasDerivAt (fun t => twoValueExp W t z) (twoValueVarianceDeriv W v z) v ∧
      0 < twoValueVarianceDeriv W v z := by
  obtain ⟨hA,hB,hbal,h1,h2,hC⟩ := twoValue_coefficients W z hz hzW
  have hW : 0 < W := lt_trans hz hzW
  have hk : 0 < W-z := sub_pos.mpr hzW
  have hkC : (W-z)*twoValueB W z=√(z*(W-z)/W) := hbal.symm.trans hC
  refine ⟨?_,?_⟩
  · have hdx : HasDerivAt (fun t : ℝ => -t*twoValueA W z) (-twoValueA W z) v := by
      convert! ((hasDerivAt_id v).neg.mul_const (twoValueA W z)) using 1 <;> ring
    have hdy : HasDerivAt (fun t : ℝ => t*twoValueB W z) (twoValueB W z) v := by
      simpa using (hasDerivAt_id v).mul_const (twoValueB W z)
    have h := (hdx.exp.const_mul z).add (hdy.exp.const_mul (W-z))
    convert! h using 1
    dsimp [twoValueVarianceDeriv]
    linear_combination exp (-v*twoValueA W z)*hC-exp (v*twoValueB W z)*hkC
  · have hxy : -v*twoValueA W z < v*twoValueB W z := by
      nlinarith [mul_pos hv hA,mul_pos hv hB]
    have he : 0 < exp (v*twoValueB W z)-exp (-v*twoValueA W z) :=
      sub_pos.mpr (Real.exp_lt_exp.mpr hxy)
    exact mul_pos (Real.sqrt_pos.mpr (by positivity)) he

theorem twoValueExp_strictMono_variance (W z : ℝ) (hz : 0 < z) (hzW : z < W) :
    StrictMonoOn (fun v => twoValueExp W v z) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro v hv
    exact (weighted_monotonicity_variance_derivative W v z hv hz hzW).1.continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    obtain ⟨hd,hp⟩ := weighted_monotonicity_variance_derivative W v z hv hz hzW
    rwa [hd.deriv]

#check weighted_monotonicity_variance_derivative
#print axioms weighted_monotonicity_variance_derivative
#print axioms twoValueExp_strictMono_variance
end Blueprint.Thomson.Tail.Implementation
