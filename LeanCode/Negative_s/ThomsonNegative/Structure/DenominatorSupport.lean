import ThomsonNegative.Reduction.Denominators

noncomputable section
namespace ThomsonNegative.Structure

/-- The additional degree-six pivot factor of the uncomposed scalar stage. -/
def lowExtraFactor (a : ℝ) : ℝ :=
  -1+18*a-91*a^2-532*a^3+6009*a^4-17310*a^5+16003*a^6

theorem lowExtraFactor_pos (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < lowExtraFactor a := by
  have hx : 0 ≤ 16*a-5 := by linarith
  have hy : 0 < 1-3*a := by linarith
  have he : (1:ℝ)*lowExtraFactor a = 2103099*(16*a-5)^0*(1-3*a)^6 + 2335640*(16*a-5)^1*(1-3*a)^5 + 1064684*(16*a-5)^2*(1-3*a)^4 + 254496*(16*a-5)^3*(1-3*a)^3 + 33552*(16*a-5)^4*(1-3*a)^2 + 2304*(16*a-5)^5*(1-3*a)^1 + 64*(16*a-5)^6*(1-3*a)^0 := by unfold lowExtraFactor; ring
  have hp : 0 < 2103099*(16*a-5)^0*(1-3*a)^6 + 2335640*(16*a-5)^1*(1-3*a)^5 + 1064684*(16*a-5)^2*(1-3*a)^4 + 254496*(16*a-5)^3*(1-3*a)^3 + 33552*(16*a-5)^4*(1-3*a)^2 + 2304*(16*a-5)^5*(1-3*a)^1 + 64*(16*a-5)^6*(1-3*a)^0 := by positivity
  nlinarith

end ThomsonNegative.Structure
