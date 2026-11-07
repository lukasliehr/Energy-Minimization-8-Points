import AllS.Units.N_FI.N_exclude_six.N_exclude

namespace Blueprint.Thomson.Finite

theorem exclude_six_contact_types {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    bpairCounts a Y r t 0 1=0 ∧ bpairCounts a Y r t 0 2=0 ∧ bpairCounts a Y r t 1 2=2 := by
  rcases bpair_two_integer_patterns h h3 r t hrt hB with hg | ⟨h01,h02,h12⟩
  · exact hg
  · exact (exclude_six_counted h h1 h3 r t hrt hB h01 h02 h12).elim

#check exclude_six_contact_types
#print axioms exclude_six_contact_types
end Blueprint.Thomson.Finite
