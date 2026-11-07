import AllS.Units.N_FI.N_two_squares.N_first_square

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem SquareRealization.offdiag {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : physical a) (i j : Fin 4) (hij : i ≠ j) :
    inner ℝ (Y (S.label i)) (Y (S.label j))=contacts a 0 ∨
      inner ℝ (Y (S.label i)) (Y (S.label j))=contacts a 1 := by
  rw [S.gram ha,if_neg hij]
  have ht : ∀ i j : Fin 4, i ≠ j →
      candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=0 ∨
      candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=1 := by decide
  exact (ht i j hij).imp (congrArg (contacts a)) (congrArg (contacts a))

theorem two_squares_second_square {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (S : SquareRealization a Y) :
    ∃ T : SquareRealization a Y, T.labels=S.labelsᶜ ∧ T.labels.card=4 ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j) ≠ contacts a 0 ∧ inner ℝ (Y i) (Y j) ≠ contacts a 1 := by
  classical
  have hcomp : S.labelsᶜ.card=4 := by rw [Finset.card_compl,S.card]; decide
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < S.labelsᶜ.card by omega)
  have hrS : r ∉ S.labels := Finset.mem_compl.mp hr
  have hbcard : (contactNeighbors a Y r 1).card=1 := congrFun (h.counts r) 1
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (contactNeighbors a Y r 1).card by omega)
  obtain ⟨htr,hB⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨T,hTr,_,_,_⟩ := two_squares_first_square h h1 h3 r t (Ne.symm htr) hB
  have hsub : T.labels ⊆ S.labelsᶜ := by
    intro l hl
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hl
    apply Finset.mem_compl.mpr
    intro hkS
    by_cases hk : k=0
    · subst k
      exact hrS (hTr ▸ hkS)
    · have hkr : T.label k ≠ r := by rw [← hTr]; exact T.injective.ne hk
      have hprod := T.offdiag h.physical k 0 hk
      rw [hTr] at hprod
      exact hrS (S.closed_AB h _ r hkS hkr hprod)
  have he : T.labels=S.labelsᶜ := Finset.eq_of_subset_of_card_le hsub (by rw [hcomp,T.card])
  refine ⟨T,he,T.card,?_⟩
  intro i hi j hj
  have hjS : j ∉ S.labels := by rw [he] at hj; exact Finset.mem_compl.mp hj
  have hij : i ≠ j := by rintro rfl; exact hjS hi
  exact ⟨fun hc => hjS (S.closed_AB h i j hi hij (Or.inl hc)),
    fun hc => hjS (S.closed_AB h i j hi hij (Or.inr hc))⟩

#check two_squares_second_square
#print axioms two_squares_second_square
end Blueprint.Thomson.Finite
