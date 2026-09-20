import Coulomb8.Setup

namespace Thomson8.Box

def separated (b : Box) : Prop := 0 < b.lo ∨ b.hi < 0
instance (b : Box) : Decidable (separated b) := inferInstanceAs (Decidable (_ ∨ _))

def signedInverse (b : Box) : Box :=
  if 0 < b.lo then inverse b else neg (inverse (neg b))

theorem contains_signedInverse {b : Box} {x : ℝ}
    (hb : b.separated) (hx : b.Contains x) : (signedInverse b).Contains x⁻¹ := by
  by_cases hp : 0 < b.lo
  · simpa [signedInverse,hp] using contains_inverse hp hx
  · have hn : b.hi < 0 := hb.resolve_left hp
    have hn' : 0 < (neg b).lo := by simpa [neg] using neg_pos.mpr hn
    have h := contains_neg (contains_inverse hn' (contains_neg hx))
    simpa [signedInverse,hp,inv_neg] using h

theorem contains_sqrt_interval {b c : Box} {x : ℝ} (hx : b.Contains x)
    (hb : 0 ≤ b.lo) (hl : c.lo^2 ≤ b.lo) (hu : b.hi ≤ c.hi^2)
    (hcu : 0 ≤ c.hi) : c.Contains (Real.sqrt x) := by
  have hxp : 0 ≤ x := (Rat.cast_nonneg.mpr hb).trans hx.1
  have hs := Real.sq_sqrt hxp
  have hp := Real.sqrt_nonneg x
  have hl' : (c.lo : ℝ)^2 ≤ (b.lo : ℝ) := by exact_mod_cast hl
  have hu' : (b.hi : ℝ) ≤ (c.hi : ℝ)^2 := by exact_mod_cast hu
  have hcu' : (0 : ℝ) ≤ c.hi := Rat.cast_nonneg.mpr hcu
  constructor <;> nlinarith [hx.1,hx.2]

theorem contains_widen {b c : Box} {x : ℝ} (hx : b.Contains x)
    (hl : c.lo ≤ b.lo) (hu : b.hi ≤ c.hi) : c.Contains x :=
  ⟨(Rat.cast_le.mpr hl).trans hx.1,hx.2.trans (Rat.cast_le.mpr hu)⟩

theorem positive_of_contains {b : Box} {x : ℝ} (hx : b.Contains x)
    (hb : 0 < b.lo) : 0 < x := (Rat.cast_pos.mpr hb).trans_le hx.1

theorem negative_of_contains {b : Box} {x : ℝ} (hx : b.Contains x)
    (hb : b.hi < 0) : x < 0 := hx.2.trans_lt (by exact_mod_cast hb)

theorem nonzero_of_contains {b : Box} {x : ℝ} (hx : b.Contains x)
    (hb : b.separated) : x ≠ 0 := by
  rcases hb with hp | hn
  · exact ne_of_gt (positive_of_contains hx hp)
  · exact ne_of_lt (negative_of_contains hx hn)

end Thomson8.Box

#print axioms Thomson8.Box.contains_signedInverse
#print axioms Thomson8.Box.contains_sqrt_interval
