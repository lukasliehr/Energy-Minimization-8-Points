import Coulomb8.DyadicBox

namespace Coulomb8.Dyadic

def integer (n : ℤ) : Dyadic := ⟨n*scale,n*scale⟩
def mul (b c : Dyadic) : Dyadic :=
  ⟨min (min (b.lo*c.lo) (b.lo*c.hi)) (min (b.hi*c.lo) (b.hi*c.hi))/scale,
   max (max (b.lo*c.lo) (b.lo*c.hi)) (max (b.hi*c.lo) (b.hi*c.hi))/scale+1⟩
def sub (b c : Dyadic) : Dyadic := add b (neg c)

theorem contains_integer (n : ℤ) : (integer n).Contains (n : ℝ) := by
  simp [Contains,integer,mul_comm]

theorem contains_add_exact {b c : Dyadic} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (add b c).Contains (x+y) := contains_add hx hy ⟨le_rfl,le_rfl⟩

theorem contains_neg {b : Dyadic} {x : ℝ} (hx : b.Contains x) : (neg b).Contains (-x) := by
  constructor
  · simpa only [neg,Int.cast_neg,mul_neg,neg_le_neg_iff] using hx.2
  · simpa only [neg,Int.cast_neg,mul_neg,neg_le_neg_iff] using hx.1

theorem contains_sub {b c : Dyadic} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (sub b c).Contains (x-y) := by
  simpa only [sub,sub_eq_add_neg] using contains_add_exact hx (contains_neg hy)

theorem contains_mul_exact {b c : Dyadic} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (mul b c).Contains (x*y) := by
  apply contains_mul hx hy
  have hp : (0 : ℤ)<scale := by norm_num [scale]
  exact ⟨Int.ediv_mul_le _ hp.ne',(Int.lt_ediv_add_one_mul_self _ hp).le⟩

def Separated (b : Dyadic) : Prop := 0<b.lo ∨ b.hi<0
instance (b : Dyadic) : Decidable b.Separated := inferInstanceAs (Decidable (_ ∨ _))

theorem nonzero_of_contains {b : Dyadic} {x : ℝ} (hx : b.Contains x) (hb : b.Separated) : x ≠ 0 := by
  intro he
  subst x
  have hl := hx.1
  have hu := hx.2
  simp only [mul_zero] at hl hu
  rcases hb with h | h
  · have hp : (0 : ℝ)<b.lo := by exact_mod_cast h
    linarith
  · have hp : (b.hi : ℝ)<0 := by exact_mod_cast h
    linarith

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.contains_mul_exact
