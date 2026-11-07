import AllS.Units.N_GI.N_cycle_decomposition.N_subtract_minimum

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def FlowDecomposition (f : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∃ L : List (ℝ × FlowCycle),
    (∀ b ∈ L, 0 < b.1 ∧ b.2.Positive f) ∧
    (∀ i j, f i j=(L.map (fun b => b.1*b.2.unitFlow i j)).sum)

theorem FlowCycle.unitFlow_nonneg (C : FlowCycle) (i j : Fin 8) : 0 ≤ C.unitFlow i j := by
  unfold FlowCycle.unitFlow
  split_ifs <;> norm_num

theorem cycle_decomposition_decompose (f : Fin 8 → Fin 8 → ℝ)
    (hf : NonnegativeCirculation f) : FlowDecomposition f := by
  suffices ∀ n, ∀ f : Fin 8 → Fin 8 → ℝ, NonnegativeCirculation f →
      (flowSupport f).card=n → FlowDecomposition f from this _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hf hn
    by_cases hpos : ∃ i j, 0 < f i j
    · obtain ⟨C,hC⟩ := cycle_decomposition_find_cycle f hf hpos
      obtain ⟨β,g,hβ,hg,hcard,hfg⟩ := cycle_decomposition_subtract_minimum f hf C hC
      obtain ⟨L,hL,hcoords⟩ := ih (flowSupport g).card (by rwa [hn] at hcard) g hg rfl
      have hgle (i j) : g i j ≤ f i j := by
        rw [hfg i j]
        exact le_add_of_nonneg_right (mul_nonneg hβ.le (C.unitFlow_nonneg i j))
      refine ⟨(β,C)::L,?_,?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hβ,hC⟩
        · refine ⟨(hL b hb).1,?_⟩
          intro i
          exact ((hL b hb).2 i).trans_le (hgle _ _)
      · intro i j
        simp only [List.map_cons,List.sum_cons]
        rw [← hcoords i j,hfg i j]
        ring
    · refine ⟨[],by simp,?_⟩
      intro i j
      simp only [List.map_nil,List.sum_nil]
      exact le_antisymm (le_of_not_gt (fun h => hpos ⟨i,j,h⟩)) (hf.1 i j)

#check cycle_decomposition_decompose
#print axioms cycle_decomposition_decompose
end Blueprint.Thomson.Tail.Implementation
