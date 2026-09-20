import Lean_Code.ContactChainConvexity

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma short_cyclic_offsets (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 5)
    (i j : Fin (n + 1)) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    j = i + 1 + 1 ∨ j = i + 1 + 1 + 1 ∨ j = i - 1 ∨ j = i - 1 - 1 := by
  interval_cases n <;> revert i j <;> decide

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

/-- Cycles of length at most six satisfy strict support outright. For
lengths four through six, four-vertex convexity reaches every vertex from
either end of a directed edge. -/
theorem support_of_length_le_six (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hlength : C.size + 1 ≤ 6) : C.StrictSupport := by
  have hlow := C.length_ge_three hirr
  by_cases hthree : C.size = 2
  · rcases C with ⟨n, point, hinj, hstep⟩
    change n = 2 at hthree
    subst n
    let C : ContactBoundaryCycle Y c hY hc := ⟨2, point, hinj, hstep⟩
    change C.StrictSupport
    intro i j hji hjnext
    have hj : j = i + 1 + 1 := by
      have h : ∀ i j : Fin 3, j ≠ i → j ≠ i + 1 → j = i + 1 + 1 := by decide
      exact h i j hji hjnext
    rw [hj]
    exact C.strict_turn hirr i
  · have hlarge : 3 < C.size + 1 := by omega
    intro i j hji hjnext
    rcases short_cyclic_offsets C.size (by omega) (by omega) i j hji hjnext with
      h | h | h | h
    · rw [h]
      exact C.strict_turn hirr i
    · rw [h]
      exact (C.four_chain_orientations hirr hbound hlarge i).1
    · rw [h, ← triple_cyclic]
      simpa only [sub_add_cancel] using C.strict_turn hirr (i - 1)
    · rw [h, ← triple_cyclic]
      have hprev : i - 1 - 1 + 1 + 1 = i := by simp only [sub_add_cancel]
      have hprev' : i - 1 - 1 + 1 + 1 + 1 = i + 1 := by rw [hprev]
      simpa only [hprev, hprev'] using
        (C.four_chain_orientations hirr hbound hlarge (i - 1 - 1)).2

/-- No actual boundary has five or six sides in the packing range. This
does not assume convexity of longer boundary cycles. -/
theorem length_three_four_or_ge_seven (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hcupper : c ≤ aInf) :
    C.size + 1 = 3 ∨ C.size + 1 = 4 ∨ 7 ≤ C.size + 1 := by
  by_cases h : C.size + 1 ≤ 6
  · rcases C.three_or_four_of_support hirr hcupper (C.support_of_length_le_six hirr hbound h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

end ContactBoundaryCycle
end SquareAntiprismVerification
