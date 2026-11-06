import AllS.Units.N_FI.N_two_squares.N_second_square

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem two_squares_opposite_centers {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (S T : SquareRealization a Y) (hcomp : T.labels=S.labelsᶜ) :
    T.center= -S.center ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3 := by
  classical
  have hsum := Finset.sum_add_sum_compl S.labels Y
  rw [← hcomp,S.sum,T.sum,h1] at hsum
  have hc : T.center= -S.center := by
    calc
      T.center = (1/4:ℝ) • ((4:ℝ) • S.center+(4:ℝ) • T.center)-S.center := by module
      _ = -S.center := by rw [hsum]; simp
  refine ⟨hc,?_⟩
  intro i hi j hj
  have hjS : j ∉ S.labels := by rw [hcomp] at hj; exact Finset.mem_compl.mp hj
  have hij : i ≠ j := by rintro rfl; exact hjS hi
  have hnA : inner ℝ (Y i) (Y j) ≠ contacts a 0 :=
    fun hh => hjS (S.closed_AB h i j hi hij (Or.inl hh))
  have hnB : inner ℝ (Y i) (Y j) ≠ contacts a 1 :=
    fun hh => hjS (S.closed_AB h i j hi hij (Or.inr hh))
  obtain ⟨k,hk⟩ := h.allowed_contact i j hij
  fin_cases k
  · exact (hnA hk.symm).elim
  · exact (hnB hk.symm).elim
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

#check two_squares_opposite_centers
#print axioms two_squares_opposite_centers
end Blueprint.Thomson.Finite
