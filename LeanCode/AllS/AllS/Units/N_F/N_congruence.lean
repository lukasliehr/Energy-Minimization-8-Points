import AllS.Units.N_FI.N_congruence.N_relabel

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem two_squares_congruent {a : ℝ} {Y : Fin 8 → Point} (hY : IsConfiguration Y)
    (ha : physical a) (S T : SquareRealization a Y) (hcomp : T.labels=S.labelsᶜ)
    (hcent : T.center= -S.center)
    (hcross : ∀ i ∈ S.labels, ∀ j ∈ T.labels,
      inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3) :
    Congruent Y (X a) := by
  classical
  apply congruence_relabel a Y hY S.isometry
  intro j
  by_cases hj : j ∈ S.labels
  · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨Fin.castAdd 4 k,S.points k⟩
  · have hjT : j ∈ T.labels := by rw [hcomp]; exact Finset.mem_compl.mpr hj
    obtain ⟨h2,h0,h1⟩ := congruence_lower_diagonals ha S T hcent hcross j hjT
    let y := S.isometry.symm (Y j)
    have hc : ∃ k : Fin 8, y=X a k := by
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · refine ⟨4,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨7,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨5,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨6,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
    obtain ⟨k,hk⟩ := hc
    refine ⟨k,?_⟩
    calc
      Y j=S.isometry y := (S.isometry.apply_symm_apply _).symm
      _ = S.isometry (X a k) := congrArg S.isometry hk

theorem odd_moment_congruence (a : ℝ) (Y : Fin 8 → Point) (ha : physical a)
    (hY : IsConfiguration Y) (hc : AllowedContacts a Y)
    (hodd : ∀ i, (∑ j, inner ℝ (Y i) (Y j))=0 ∧ (∑ j, (inner ℝ (Y i) (Y j))^3)=0) :
    Congruent Y (X a) := by
  have h : ContactCountData a Y := ⟨ha,hY,(vertex_contact_counts a ha).2 Y hY hc hodd⟩
  obtain ⟨h1,h3⟩ := (zero_tensors_equivalence Y).mp hodd
  obtain ⟨S,T,hcomp,hcent,_,_,hcross⟩ := recover_two_squares h h1 h3
  exact two_squares_congruent hY ha S T hcomp hcent hcross

#check odd_moment_congruence
#print axioms odd_moment_congruence
end Blueprint.Thomson.Finite
