import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions

noncomputable section
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 0
namespace Blueprint.Thomson.Finite

/-- Off-diagonal A,B,C,D labels; diagonal entries are ignored. -/
def candidateContactLabel : Fin 8 → Fin 8 → Fin 4 :=
  ![![0,0,1,0,2,3,3,2], ![0,0,0,1,2,2,3,3],
    ![1,0,0,0,3,2,2,3], ![0,1,0,0,3,3,2,2],
    ![2,2,3,3,0,0,1,0], ![3,2,2,3,0,0,0,1],
    ![3,3,2,2,1,0,0,0], ![2,3,3,2,0,1,0,0]]

def CandidateGramContract : Prop := ∀ a : ℝ, physical a →
  (∀ i, ‖X a i‖ = 1) ∧
  ∀ i j, inner ℝ (X a i) (X a j) =
    if i = j then 1 else contacts a (candidateContactLabel i j)

theorem physical_mem_Ioo (a : ℝ) (ha : physical a) : a ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hl,hu⟩ := ha
  have hb := packing_endpoint_bounds.1
  constructor <;> linarith

theorem candidate_gram_entry (a : ℝ) (ha : physical a) (i j : Fin 8) :
    inner ℝ (X a i) (X a j) =
      if i = j then 1 else contacts a (candidateContactLabel i j) := by
  by_cases hij : i = j
  · subst j
    simp [inner_self_eq_norm_sq_to_K, (candidate_is_configuration a (physical_mem_Ioo a ha)).1 i]
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hr : (Real.sqrt (1-a))^2 = 1-a := Real.sq_sqrt (by linarith)
  have hh : (Real.sqrt a)^2 = a := Real.sq_sqrt ha0.le
  have hq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hqn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  fin_cases i <;> fin_cases j <;>
    norm_num [X, candidateContactLabel, contacts, PiLp.inner_apply, Fin.sum_univ_succ] at *
  all_goals try dsimp
  all_goals field_simp
  all_goals ring_nf
  all_goals try simp only [hr, hh, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  all_goals ring

theorem geometry_gram_entries : CandidateGramContract := by
  intro a ha
  exact ⟨(candidate_is_configuration a (physical_mem_Ioo a ha)).1,
    candidate_gram_entry a ha⟩

#check geometry_gram_entries
#print axioms geometry_gram_entries
#check CandidateGramContract
#print axioms CandidateGramContract
end Blueprint.Thomson.Finite
