import AllS.Units.N_FI.N_two_squares.N_opposite_centers

noncomputable section
namespace Blueprint.Thomson.Finite

theorem recover_two_squares {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) :
    ∃ S T : SquareRealization a Y, T.labels=S.labelsᶜ ∧ T.center= -S.center ∧
      ‖S.center‖^2=a ∧ ‖T.center‖^2=a ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3 := by
  have hbcard : (contactNeighbors a Y 0 1).card=1 := congrFun (h.counts 0) 1
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (contactNeighbors a Y 0 1).card by omega)
  obtain ⟨htr,hB⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨S,_,_,_,_⟩ := two_squares_first_square h h1 h3 0 t (Ne.symm htr) hB
  obtain ⟨T,hcomp,_,_⟩ := two_squares_second_square h h1 h3 S
  obtain ⟨hc,hcross⟩ := two_squares_opposite_centers h h1 S T hcomp
  have ha0 := (physical_mem_Ioo a h.physical).1.le
  exact ⟨S,T,hcomp,hc,S.center_norm ha0,T.center_norm ha0,hcross⟩

#check recover_two_squares
#print axioms recover_two_squares
end Blueprint.Thomson.Finite
