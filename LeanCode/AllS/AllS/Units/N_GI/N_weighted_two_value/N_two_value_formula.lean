import AllS.Units.N_GI.N_weighted_two_value.N_two_level_algebra

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem weighted_two_value_two_value_formula {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) (x : Fin n → ℝ)
    (hx : x ∈ weightedFeasible w v) (a b : ℝ) (haff : ∀ i, exp (x i)=a+b*x i) :
    ∃ z : ℝ, 0 < z ∧ z < ∑ i,w i ∧ z=weightedNegativeMass w x ∧
      (∀ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z)) ∨
        x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      (∃ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z))) ∧
      (∃ i, x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      weightedExp w x=twoValueExp (∑ i,w i) v z := by
  classical
  obtain ⟨il,ih,hle,hvals⟩ := exp_affine_two_extrema hn x a b haff
  have hW := weighted_total_pos hn w hw
  have hlh : x il < x ih := by
    apply lt_of_le_of_ne hle
    intro he
    have hall (i : Fin n) : x i=x il := by
      rcases hvals i with h|h
      · exact h
      · exact h.trans he.symm
    have hm : (∑ i,w i)*x il=0 := by
      simpa only [weightedMean,hall,Finset.sum_mul] using hx.1
    have hl0 : x il=0 := (mul_eq_zero.mp hm).resolve_left hW.ne'
    have hq : v^2=0 := by
      rw [← hx.2]
      simp [weightedSquare,hall,hl0]
    nlinarith
  let z := weightedLevelMass w x (x il)
  obtain ⟨hz,hk⟩ := level_masses_positive w x hw il ih hlh.ne
  have hm : z*x il+((∑ i,w i)-z)*x ih=0 := by
    have he := sum_of_two_levels w x (x il) (x ih) hlh.ne hvals id
    exact he.symm.trans hx.1
  have hq : z*(x il)^2+((∑ i,w i)-z)*(x ih)^2=v^2 := by
    have he := sum_of_two_levels w x (x il) (x ih) hlh.ne hvals (fun t => t^2)
    exact he.symm.trans hx.2
  obtain ⟨hl,hh,hlf,hhf⟩ := two_level_values (∑ i,w i) z v (x il) (x ih) hz hk hv hlh hm hq
  have hzneg : z=weightedNegativeMass w x := by
    unfold z weightedLevelMass weightedNegativeMass
    apply Finset.sum_congr rfl
    intro i _
    rcases hvals i with hi|hi
    · simp [hi,hl]
    · simp [hi,Ne.symm hlh.ne,not_lt_of_ge hh.le]
  refine ⟨z,hz,by linarith,hzneg,?_,⟨il,hlf⟩,⟨ih,hhf⟩,?_⟩
  · intro i
    rcases hvals i with hi|hi
    · exact Or.inl (hi.trans hlf)
    · exact Or.inr (hi.trans hhf)
  · have he := sum_of_two_levels w x (x il) (x ih) hlh.ne hvals exp
    change weightedExp w x=z*exp (x il)+((∑ i,w i)-z)*exp (x ih) at he
    rw [hlf,hhf] at he
    exact he

#check weighted_two_value_two_value_formula
#print axioms weighted_two_value_two_value_formula
end Blueprint.Thomson.Tail.Implementation
