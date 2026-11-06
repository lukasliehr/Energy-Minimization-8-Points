import AllS.Units.N_GI.N_cycle_decomposition.N_find_cycle

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def FlowCycle.unitFlow (C : FlowCycle) (i j : Fin 8) : ℝ :=
  if ∃ k, C.point k=i ∧ C.point (k+1)=j then 1 else 0

def flowSupport (f : Fin 8 → Fin 8 → ℝ) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun e => 0 < f e.1 e.2)

theorem FlowCycle.unitFlow_sum (C : FlowCycle) (i j : Fin 8) :
    C.unitFlow i j=∑ k, if C.point k=i then (if C.point (k+1)=j then (1:ℝ) else 0) else 0 := by
  classical
  by_cases he : ∃ k, C.point k=i ∧ C.point (k+1)=j
  · obtain ⟨k,hki,hkj⟩ := he
    rw [FlowCycle.unitFlow,if_pos ⟨k,hki,hkj⟩,Finset.sum_eq_single k]
    · simp [hki,hkj]
    · intro b hb hbk
      have hbne : C.point b ≠ i := fun h => hbk (C.injective (h.trans hki.symm))
      simp [hbne]
    · simp
  · rw [FlowCycle.unitFlow,if_neg he]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki : C.point k=i
    · have hkj : C.point (k+1) ≠ j := fun h => he ⟨k,hki,h⟩
      simp [hki,hkj]
    · simp [hki]

theorem FlowCycle.unitFlow_balance (C : FlowCycle) (i : Fin 8) :
    (∑ j : Fin 8, C.unitFlow i j)=∑ j : Fin 8, C.unitFlow j i := by
  simp_rw [FlowCycle.unitFlow_sum]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun j k =>
    if C.point k=j then (if C.point (k+1)=i then (1:ℝ) else 0) else 0)]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  exact (Equiv.sum_comp (Equiv.addRight (1 : Fin (C.size+1)))
    (fun k => if C.point k=i then (1:ℝ) else 0)).symm

theorem FlowCycle.unitFlow_edge (C : FlowCycle) (k : Fin (C.size+1)) :
    C.unitFlow (C.point k) (C.point (k+1))=1 := by
  rw [FlowCycle.unitFlow,if_pos ⟨k,rfl,rfl⟩]

theorem cycle_decomposition_subtract_minimum (f : Fin 8 → Fin 8 → ℝ)
    (hf : NonnegativeCirculation f) (C : FlowCycle) (hC : C.Positive f) :
    ∃ (β : ℝ) (g : Fin 8 → Fin 8 → ℝ), 0 < β ∧ NonnegativeCirculation g ∧
      (flowSupport g).card < (flowSupport f).card ∧
      (∀ i j, f i j=g i j+β*C.unitFlow i j) := by
  classical
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => f (C.point k) (C.point (k+1))) Finset.univ_nonempty
  let β := f (C.point k) (C.point (k+1))
  let g := fun i j => f i j-β*C.unitFlow i j
  have hβ : 0 < β := hC k
  have hβle (i) : β ≤ f (C.point i) (C.point (i+1)) := hmin i (Finset.mem_univ i)
  have hgle (i j) : g i j ≤ f i j := by
    dsimp [g,FlowCycle.unitFlow]
    split_ifs <;> linarith
  have hg0 (i j) : 0 ≤ g i j := by
    dsimp [g,FlowCycle.unitFlow]
    split_ifs with h
    · obtain ⟨l,rfl,rfl⟩ := h
      simpa using sub_nonneg.mpr (hβle l)
    · simpa using hf.1 i j
  have hgn : NonnegativeCirculation g := by
    refine ⟨hg0,?_,?_,?_⟩
    · intro i
      exact le_antisymm (by simpa [hf.2.1 i] using hgle i i) (hg0 i i)
    · intro i j hij
      exact hf.2.2.1 i j ⟨hij.1.trans_le (hgle i j),hij.2.trans_le (hgle j i)⟩
    · intro i
      simp only [g,Finset.sum_sub_distrib,← Finset.mul_sum]
      rw [hf.2.2.2 i,C.unitFlow_balance i]
  have hsub : flowSupport g ⊆ flowSupport f := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp he).2.trans_le (hgle _ _)⟩
  have hstrict : flowSupport g ⊂ flowSupport f := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro he
    have hin : (C.point k,C.point (k+1)) ∈ flowSupport f :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hβ⟩
    rw [← he] at hin
    have hp := (Finset.mem_filter.mp hin).2
    simpa [g,β,C.unitFlow_edge] using hp
  refine ⟨β,g,hβ,hgn,Finset.card_lt_card hstrict,?_⟩
  intro i j
  dsimp [g]
  ring

#check cycle_decomposition_subtract_minimum
#print axioms cycle_decomposition_subtract_minimum
end Blueprint.Thomson.Tail.Implementation
