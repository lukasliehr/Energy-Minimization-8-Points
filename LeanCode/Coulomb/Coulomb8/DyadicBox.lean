import Coulomb8.Dyadic

namespace Coulomb8.Dyadic

theorem contains_of_box {b : Thomson8.Box} {c : Dyadic} {x : ℝ}
    (hx : b.Contains x)
    (hl : (c.lo : ℚ) ≤ (scale : ℚ)*b.lo)
    (hu : (scale : ℚ)*b.hi ≤ (c.hi : ℚ)) : c.Contains x := by
  have hl' : (c.lo : ℝ) ≤ (scale : ℝ)*(b.lo : ℝ) := by exact_mod_cast hl
  have hu' : (scale : ℝ)*(b.hi : ℝ) ≤ (c.hi : ℝ) := by exact_mod_cast hu
  exact ⟨hl'.trans (mul_le_mul_of_nonneg_left hx.1 scale_pos.le),
    (mul_le_mul_of_nonneg_left hx.2 scale_pos.le).trans hu'⟩

theorem contains_of_box_div_three {b : Thomson8.Box} {c : Dyadic} {x : ℝ}
    (hx : b.Contains x)
    (hl : (c.lo : ℚ) ≤ (scale : ℚ)*(b.lo/3))
    (hu : (scale : ℚ)*(b.hi/3) ≤ (c.hi : ℚ)) : c.Contains (x/3) := by
  apply contains_of_box (b:=⟨b.lo/3,b.hi/3⟩) _ hl hu
  constructor
  · exact_mod_cast (div_le_div_of_nonneg_right hx.1 (by norm_num : (0 : ℝ) ≤ 3))
  · exact_mod_cast (div_le_div_of_nonneg_right hx.2 (by norm_num : (0 : ℝ) ≤ 3))

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.contains_of_box_div_three
