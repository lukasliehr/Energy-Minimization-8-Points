import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Thomson8

theorem positive_bump {f f' : ℝ → ℝ} {a r b : ℝ}
    (har : a < r) (hrb : r < b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo a r, 0 < f' x)
    (hneg : ∀ x ∈ Set.Ioo r b, f' x < 0)
    (ha : f a=0) (hb : f b=0) {x : ℝ} (hx : x ∈ Set.Ioo a b) : 0 < f x := by
  have hinc : StrictMonoOn f (Set.Icc a r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a r)
    · exact hc.mono (by intro y hy; exact ⟨hy.1,hy.2.trans hrb.le⟩)
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hd y ⟨hy.1,hy.2.trans hrb⟩).deriv]
      exact hpos y hy
  have hdec : StrictAntiOn f (Set.Icc r b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc r b)
    · exact hc.mono (by intro y hy; exact ⟨har.le.trans hy.1,hy.2⟩)
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hd y ⟨har.trans hy.1,hy.2⟩).deriv]
      exact hneg y hy
  by_cases hxr : x ≤ r
  · simpa [ha] using hinc ⟨le_rfl,har.le⟩ ⟨hx.1.le,hxr⟩ hx.1
  · simpa [hb] using hdec ⟨(lt_of_not_ge hxr).le,hx.2.le⟩ ⟨hrb.le,le_rfl⟩ hx.2

end Thomson8
