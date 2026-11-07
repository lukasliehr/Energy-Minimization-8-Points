import AllS.Units.N_GI.N_weighted_two_value.N_minimum_and_tangents
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem exp_affine_no_three (a b l m h : ℝ) (hlm : l < m) (hmh : m < h)
    (hl : exp l=a+b*l) (hm : exp m=a+b*m) (hh : exp h=a+b*h) : False := by
  let A := (h-m)/(h-l)
  let B := (m-l)/(h-l)
  have hden : 0 < h-l := by linarith
  have hA : 0 < A := div_pos (sub_pos.mpr hmh) hden
  have hB : 0 < B := div_pos (sub_pos.mpr hlm) hden
  have hAB : A+B=1 := by dsimp [A,B]; field_simp; ring
  have hmid : A*l+B*h=m := by dsimp [A,B]; field_simp; ring
  have hc := strictConvexOn_exp.2 (Set.mem_univ l) (Set.mem_univ h)
    (show l ≠ h by linarith) hA hB hAB
  simp only [smul_eq_mul] at hc
  rw [hmid,hl,hm,hh] at hc
  have he : A*(a+b*l)+B*(a+b*h)=a+b*m := by
    linear_combination a*hAB+b*hmid
  linarith

theorem exp_affine_two_extrema {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (a b : ℝ) (h : ∀ i, exp (x i)=a+b*x i) :
    ∃ il ih : Fin n, x il ≤ x ih ∧ ∀ i, x i=x il ∨ x i=x ih := by
  have hnon : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨il,_,hlo⟩ := Finset.exists_min_image Finset.univ x hnon
  obtain ⟨ih,_,hhi⟩ := Finset.exists_max_image Finset.univ x hnon
  refine ⟨il,ih,hlo ih (Finset.mem_univ _),?_⟩
  intro i
  by_cases hl : x i=x il
  · exact Or.inl hl
  right
  by_contra hh
  have hl' : x il < x i := lt_of_le_of_ne (hlo i (Finset.mem_univ _)) (Ne.symm hl)
  have hh' : x i < x ih := lt_of_le_of_ne (hhi i (Finset.mem_univ _)) hh
  exact exp_affine_no_three a b (x il) (x i) (x ih) hl' hh' (h il) (h i) (h ih)

theorem weighted_two_value_at_most_two {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (a b : ℝ) (h : ∀ i, exp (x i)=a+b*x i) :
    (Finset.univ.image x).card ≤ 2 := by
  classical
  obtain ⟨il,ih,_,hvals⟩ := exp_affine_two_extrema hn x a b h
  have hs : Finset.univ.image x ⊆ {x il,x ih} := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hvals i
  exact (Finset.card_le_card hs).trans Finset.card_le_two

#check weighted_two_value_at_most_two
#print axioms weighted_two_value_at_most_two
end Blueprint.Thomson.Tail.Implementation
