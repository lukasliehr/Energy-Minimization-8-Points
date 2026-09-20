import Coulomb8.SquaredFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
open scoped BigOperators
open Polynomial

def bernsteinMatrix : Fin 13 → Fin 13 → ℚ := ![![1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1],
![1,(-5/6),(2/3),(-1/2),(1/3),(-1/6),0,(1/6),(-1/3),(1/2),(-2/3),(5/6),-1],
![1,(-2/3),(13/33),(-2/11),(1/33),(2/33),(-1/11),(2/33),(1/33),(-2/11),(13/33),(-2/3),1],
![1,(-1/2),(2/11),(-1/110),(-3/55),(1/22),0,(-1/22),(3/55),(1/110),(-2/11),(1/2),-1],
![1,(-1/3),(1/33),(3/55),(-17/495),(-1/99),(1/33),(-1/99),(-17/495),(3/55),(1/33),(-1/3),1],
![1,(-1/6),(-2/33),(1/22),(1/99),(-5/198),0,(5/198),(-1/99),(-1/22),(2/33),(1/6),-1],
![1,0,(-1/11),0,(1/33),0,(-5/231),0,(1/33),0,(-1/11),0,1],
![1,(1/6),(-2/33),(-1/22),(1/99),(5/198),0,(-5/198),(-1/99),(1/22),(2/33),(-1/6),-1],
![1,(1/3),(1/33),(-3/55),(-17/495),(1/99),(1/33),(1/99),(-17/495),(-3/55),(1/33),(1/3),1],
![1,(1/2),(2/11),(1/110),(-3/55),(-1/22),0,(1/22),(3/55),(-1/110),(-2/11),(-1/2),-1],
![1,(2/3),(13/33),(2/11),(1/33),(-2/33),(-1/11),(-2/33),(1/33),(2/11),(13/33),(2/3),1],
![1,(5/6),(2/3),(1/2),(1/3),(1/6),0,(-1/6),(-1/3),(-1/2),(-2/3),(-5/6),-1],
![1,1,1,1,1,1,1,1,1,1,1,1,1]]

def bernsteinBinomial : Fin 13 → ℚ := ![1,12,66,220,495,792,924,792,495,220,66,12,1]

noncomputable def bernsteinWeight (i : Fin 13) (t : ℝ) : ℝ :=
  (bernsteinBinomial i : ℝ)*((t+1)/2)^i.val*((1-t)/2)^(12-i.val)

theorem bernstein_monomial (j : Fin 13) (t : ℝ) :
    t^j.val=∑ i : Fin 13, (bernsteinMatrix i j : ℝ)*bernsteinWeight i t := by
  fin_cases j <;> norm_num [bernsteinMatrix,bernsteinWeight,bernsteinBinomial,Fin.sum_univ_succ,Fin.succ] <;> ring

noncomputable def bernsteinCoefficients (p : Polynomial ℝ) (i : Fin 13) : ℝ :=
  ∑ j : Fin 13, (bernsteinMatrix i j : ℝ)*p.coeff j.val

theorem bernsteinWeight_nonneg (i : Fin 13) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ bernsteinWeight i t := by
  unfold bernsteinWeight
  have h1 : 0 ≤ (t+1)/2 := by linarith [ht.1]
  have h2 : 0 ≤ (1-t)/2 := by linarith [ht.2]
  have hb : 0 < (bernsteinBinomial i : ℝ) := by fin_cases i <;> norm_num [bernsteinBinomial]
  positivity

theorem bernstein_sum_pos (b : Fin 13 → ℝ) (hb : ∀ i, 0 < b i)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < ∑ i : Fin 13, b i*bernsteinWeight i t := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hb i).le (bernsteinWeight_nonneg i ht)
  · by_cases he : t=1
    · refine ⟨12,Finset.mem_univ _,?_⟩
      simpa [bernsteinWeight,bernsteinBinomial,he] using hb 12
    · refine ⟨0,Finset.mem_univ _,?_⟩
      have h : 0 < (1-t)/2 := by
        have hlt : t < 1 := lt_of_le_of_ne ht.2 he
        linarith
      exact mul_pos (hb 0) (by simpa [bernsteinWeight,bernsteinBinomial] using pow_pos h 12)

end Coulomb8

#print axioms Coulomb8.bernstein_monomial
