import AllS.Units.N_F.N_contact_order

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def baselineCounts : Fin 4 → ℕ := ![2,1,2,2]

theorem contact_counts_baseline (a : ℝ) :
    (∑ k, baselineCounts k)=7 ∧
    1+(∑ k, (baselineCounts k : ℝ)*contacts a k)=0 ∧
    1+(∑ k, (baselineCounts k : ℝ)*(contacts a k)^3)=0 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  simp only [baselineCounts,contacts,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Fin.sum_univ_zero,add_zero,Nat.cast_ofNat]
  refine ⟨by norm_num,by ring,?_⟩
  rw [div_eq_mul_inv,hinv]
  linear_combination -3*a*(a-1)^2*hs

#check contact_counts_baseline
#print axioms contact_counts_baseline
end Blueprint.Thomson.Finite
