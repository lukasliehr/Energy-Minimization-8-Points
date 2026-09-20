import Thomson8.ContactOrder
import Thomson8.GeometryBasics

namespace Thomson8

open scoped InnerProductSpace

theorem nodes_no_opposites (i j : Fin 4) :
    (nodes.getD i K.zero).eval+(nodes.getD j K.zero).eval ≠ 0 := by
  let z := K.add (nodes.getD i K.zero) (nodes.getD j K.zero)
  have h : (encloseK z).hi < (0 : ℚ) ∨ (0 : ℚ) < (encloseK z).lo := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hc := encloseK_contains z
  have hz : z.eval ≠ 0 := by
    rcases h with hn | hp
    · exact ne_of_lt (hc.2.trans_lt (by exact_mod_cast hn))
    · exact ne_of_gt ((Rat.cast_pos.mpr hp).trans_le hc.1)
  simpa only [z,K.eval_add] using hz

theorem unit_antipodal (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hxy : ⟪x,y⟫_ℝ = -1) : y = -x := by
  have h := norm_add_sq_real x y
  rw [hx,hy,hxy] at h
  have hn : ‖x+y‖=0 := by nlinarith [norm_nonneg (x+y)]
  have hz := norm_eq_zero.mp hn
  exact eq_neg_of_add_eq_zero_right hz

theorem third_index (i j : Fin 8) : ∃ k : Fin 8, k≠i ∧ k≠j := by
  have h : ∀ i j : Fin 8, ∃ k : Fin 8, k≠i ∧ k≠j := by decide +kernel
  exact h i j

end Thomson8
