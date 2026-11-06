import ThomsonNegative.Geometry.Contacts

noncomputable section
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 1000000
namespace ThomsonNegative.Geometry

/-- Off-diagonal A,B,C,D labels of the candidate. -/
def candidateContactLabel : Fin 8 → Fin 8 → Fin 4 :=
  ![![0,0,1,0,2,3,3,2],![0,0,0,1,2,2,3,3],
    ![1,0,0,0,3,2,2,3],![0,1,0,0,3,3,2,2],
    ![2,2,3,3,0,0,1,0],![3,2,2,3,0,0,0,1],
    ![3,3,2,2,1,0,0,0],![2,3,3,2,0,1,0,0]]

/-- All 64 candidate Gram entries are exact algebraic identities. -/
theorem candidate_gram_entry (a : ℝ) (ha : physical a) (i j : Fin 8) :
    inner ℝ (X a i) (X a j)=if i=j then 1 else contacts a (candidateContactLabel i j) := by
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hr : (Real.sqrt (1-a))^2=1-a := Real.sq_sqrt (by linarith)
  have hh : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hq : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hqn : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hdiag (i : Fin 8) : inner ℝ (X a i) (X a i)=1 := by
    rw [PiLp.inner_apply]
    fin_cases i <;> norm_num [X,Fin.sum_univ_succ,RCLike.inner_apply]
    all_goals field_simp
    all_goals nlinarith [hr,hh,hq]
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact hdiag i
  fin_cases i <;> fin_cases j <;>
    norm_num [X,candidateContactLabel,contacts,PiLp.inner_apply,Fin.sum_univ_succ] at *
  all_goals try dsimp
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hr,hh,Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  all_goals ring

theorem candidate_is_configuration (a : ℝ) (ha : physical a) : IsConfiguration (X a) := by
  have hnorm (i : Fin 8) : ‖X a i‖=1 := by
    have hh := candidate_gram_entry a ha i i
    rw [real_inner_self_eq_norm_sq,if_pos rfl] at hh
    nlinarith [norm_nonneg (X a i)]
  refine ⟨hnorm,?_⟩
  intro i j hij
  by_contra hne
  have hh := candidate_gram_entry a ha i j
  rw [if_neg hne,hij,real_inner_self_eq_norm_sq,hnorm] at hh
  have hc := (contacts_bounds a ha (candidateContactLabel i j)).2
  norm_num at hh
  linarith

/-- Every candidate pair is one of the four H7 contacts. -/
theorem candidate_pair_contact (a : ℝ) (ha : physical a) (i j : Fin 8) (hij : i ≠ j) :
    inner ℝ (X a i) (X a j) ∈ Set.range (contacts a) := by
  exact ⟨candidateContactLabel i j,(candidate_gram_entry a ha i j).trans (if_neg hij) |>.symm⟩

/-- Eight A pairs, four B pairs, eight C pairs and eight D pairs. -/
theorem candidate_pair_sum (a : ℝ) (ha : physical a) (f : ℝ → ℝ) :
    PairSum (fun i j => f (inner ℝ (X a i) (X a j)))=
      8*f (contacts a 0)+4*f (contacts a 1)+8*f (contacts a 2)+8*f (contacts a 3) := by
  simp_rw [candidate_gram_entry a ha]
  simp [PairSum,pairSum,candidateContactLabel,Fin.sum_univ_succ,Finset.sum_filter]
  ring

#print axioms candidate_gram_entry
#print axioms candidate_is_configuration
#print axioms candidate_pair_sum
end ThomsonNegative.Geometry
