import Blueprint.TailContactData

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contactKappa_formula : contactKappa=1+√2/2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  unfold contactKappa
  field_simp
  nlinarith [hs]

theorem contactWeight_ge_one (e : ContactIndex) : 1 ≤ contactWeight e := by
  unfold contactWeight
  split_ifs
  · rfl
  · rw [contactKappa_formula]
    linarith [Real.sqrt_nonneg (2:ℝ)]

theorem contactWeight_sum : ∑ e : ContactIndex, contactWeight e=contactTotalWeight := by
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,contactWeight,contactKappa_formula,contactTotalWeight]
  ring

theorem contactWeight_incident (i : Fin 8) :
    (∑ e : ContactIndex, if e.1=i ∨ contactNext e=i then contactWeight e else 0)=contactTotalWeight/4 := by
  have hcount : ∀ i : Fin 8,
      (Finset.univ.filter (fun e : ContactIndex => (e.1=i ∨ contactNext e=i) ∧ e.2=0)).card=2 ∧
      (Finset.univ.filter (fun e : ContactIndex => (e.1=i ∨ contactNext e=i) ∧ e.2≠0)).card=2 := by decide
  have he : (∑ e : ContactIndex, if e.1=i ∨ contactNext e=i then contactWeight e else 0)=
      (∑ e ∈ Finset.univ.filter (fun e : ContactIndex => (e.1=i ∨ contactNext e=i) ∧ e.2=0), (1:ℝ))+
      (∑ e ∈ Finset.univ.filter (fun e : ContactIndex => (e.1=i ∨ contactNext e=i) ∧ e.2≠0), contactKappa) := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold contactWeight
    by_cases h : e.1=i ∨ contactNext e=i <;> by_cases hk : e.2=0 <;> simp [h,hk]
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,(hcount i).1,(hcount i).2]
  rw [contactKappa_formula]
  unfold contactTotalWeight
  norm_num
  ring

theorem constants_weights :
    contactKappa=1+1/√2 ∧ contactTotalWeight=8*(contactKappa+1) ∧
    contactTotalWeight=16+4*√2 ∧
    (∀ e : ContactIndex, 1 ≤ contactWeight e) ∧
    (∑ e : ContactIndex, contactWeight e)=contactTotalWeight ∧
    (∀ i : Fin 8, (∑ e : ContactIndex, if e.1=i ∨ contactNext e=i then contactWeight e else 0)=contactTotalWeight/4) := by
  refine ⟨rfl,?_,rfl,contactWeight_ge_one,contactWeight_sum,contactWeight_incident⟩
  rw [contactKappa_formula]
  unfold contactTotalWeight
  ring

#print axioms constants_weights
end Blueprint.Thomson.Tail.Implementation
