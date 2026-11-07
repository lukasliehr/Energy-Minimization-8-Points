import AllS.Units.N_FI.N_bpair_cases.N_cubic_equation
import AllS.Units.N_FI.N_bpair_cases.N_enumeration

noncomputable section
namespace Blueprint.Thomson.Finite

theorem bpair_two_integer_patterns {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    (bpairCounts a Y r t 0 1=0 ∧ bpairCounts a Y r t 0 2=0 ∧ bpairCounts a Y r t 1 2=2) ∨
    (bpairCounts a Y r t 0 1=1 ∧ bpairCounts a Y r t 0 2=1 ∧ bpairCounts a Y r t 1 2=1) := by
  obtain ⟨_,_,_,_,_,_,hij,hik,hjk⟩ := bpair_contact_matrix_symmetric h h3 r t hrt hB
  obtain ⟨_,hW,hUV,hc⟩ := bpair_cases_cubic_equation h h3 r t hrt hB
  obtain ⟨_,he0,he1⟩ := bpair_cases_eta_interval a h.physical
  apply bpair_cases_enumeration _ _ _ (bpairEta a) hij hik hjk he0 he1
  unfold bpairEta
  field_simp [hW.ne']
  linear_combination hc-(bpairCounts a Y r t 0 2:ℝ)*hUV

#check bpair_two_integer_patterns
#print axioms bpair_two_integer_patterns
end Blueprint.Thomson.Finite
