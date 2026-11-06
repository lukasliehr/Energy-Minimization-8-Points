import AllS.Units.N_G.N_weighted_two_value

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def twoValueA (W z : ℝ) : ℝ := √((W-z)/(W*z))
def twoValueB (W z : ℝ) : ℝ := √(z/(W*(W-z)))

theorem twoValue_coefficients (W z : ℝ) (hz : 0 < z) (hzW : z < W) :
    0 < twoValueA W z ∧ 0 < twoValueB W z ∧
    z*twoValueA W z=(W-z)*twoValueB W z ∧
    twoValueA W z*z*(twoValueA W z+twoValueB W z)=1 ∧
    twoValueB W z*(W-z)*(twoValueA W z+twoValueB W z)=1 ∧
    z*twoValueA W z=√(z*(W-z)/W) := by
  have hW : 0 < W := lt_trans hz hzW
  have hk : 0 < W-z := sub_pos.mpr hzW
  have hA : 0 < twoValueA W z := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < twoValueB W z := Real.sqrt_pos.mpr (by positivity)
  have hAs : (twoValueA W z)^2=(W-z)/(W*z) := Real.sq_sqrt (by positivity)
  have hBs : (twoValueB W z)^2=z/(W*(W-z)) := Real.sq_sqrt (by positivity)
  have hbal2 : (z*twoValueA W z)^2=((W-z)*twoValueB W z)^2 := by
    rw [mul_pow,mul_pow,hAs,hBs]
    field_simp
    <;> ring
  have hbal : z*twoValueA W z=(W-z)*twoValueB W z := by
    nlinarith [mul_pos hz hA,mul_pos hk hB]
  have hsum : z*(twoValueA W z)^2+(W-z)*(twoValueB W z)^2=1 := by
    rw [hAs,hBs]
    field_simp
    <;> ring
  have h1 : twoValueA W z*z*(twoValueA W z+twoValueB W z)=1 := by
    linear_combination hsum+twoValueB W z*hbal
  have h2 : twoValueB W z*(W-z)*(twoValueA W z+twoValueB W z)=1 := by
    linear_combination hsum-twoValueA W z*hbal
  refine ⟨hA,hB,hbal,h1,h2,?_⟩
  have hcs := Real.sq_sqrt (show 0 ≤ z*(W-z)/W by positivity)
  have hcc : (z*twoValueA W z)^2=z*(W-z)/W := by
    rw [mul_pow,hAs]
    field_simp
  nlinarith [Real.sqrt_nonneg (z*(W-z)/W),mul_pos hz hA]

theorem twoValueA_hasDerivAt (W z : ℝ) (hz : 0 < z) (hzW : z < W) :
    HasDerivAt (twoValueA W) (-1/(2*twoValueA W z*z^2)) z := by
  have hW : 0 < W := lt_trans hz hzW
  have hk : 0 < W-z := sub_pos.mpr hzW
  have hbase : 0 < (W-z)/(W*z) := by positivity
  have hg : HasDerivAt (fun t : ℝ => (W-t)/(W*t)) (-1/z^2) z := by
    have h := ((hasDerivAt_const z W).sub (hasDerivAt_id z)).div
      ((hasDerivAt_id z).const_mul W) (by positivity : W*z ≠ 0)
    convert! h using 1 <;> dsimp <;> field_simp <;> ring
  have h := hg.sqrt hbase.ne'
  have hA := (twoValue_coefficients W z hz hzW).1
  convert! h using 1
  dsimp [twoValueA]
  field_simp
  <;> ring

theorem twoValueB_hasDerivAt (W z : ℝ) (hz : 0 < z) (hzW : z < W) :
    HasDerivAt (twoValueB W) (1/(2*twoValueB W z*(W-z)^2)) z := by
  have hW : 0 < W := lt_trans hz hzW
  have hk : 0 < W-z := sub_pos.mpr hzW
  have hbase : 0 < z/(W*(W-z)) := by positivity
  have hg : HasDerivAt (fun t : ℝ => t/(W*(W-t))) (1/(W-z)^2) z := by
    have h := (hasDerivAt_id z).div
      (((hasDerivAt_const z W).sub (hasDerivAt_id z)).const_mul W) (by positivity : W*(W-z) ≠ 0)
    convert! h using 1 <;> dsimp <;> field_simp <;> ring
  have h := hg.sqrt hbase.ne'
  have hB := (twoValue_coefficients W z hz hzW).2.1
  convert! h using 1
  dsimp [twoValueB]
  field_simp
  <;> ring

#print axioms twoValue_coefficients
#print axioms twoValueA_hasDerivAt
#print axioms twoValueB_hasDerivAt
end Blueprint.Thomson.Tail.Implementation
