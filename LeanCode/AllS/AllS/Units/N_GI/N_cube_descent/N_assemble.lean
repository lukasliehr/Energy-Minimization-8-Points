import AllS.Units.N_GI.N_cube_descent.N_lower_branch

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def CubeAntiprismParameters (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  c=packingHeight ∧ ∃e : Equiv.Perm (Fin 3),q ∘ e=![cubeUpper c,cubeLower c,c]

theorem cube_double_active_parameters (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q)
    (hc : c<7/25) (i j : Fin 3) (hi : q i=cubeUpper c) (hj : q j=cubeLower c) :
    CubeAntiprismParameters c q := by
  have hij : i≠j := by
    intro he;subst j
    have hh := cube_bounds_strict c h.1.1 (by linarith)
    rw [←hi,←hj] at hh
    exact lt_irrefl _ hh
  obtain ⟨e,he0,he1⟩ := fin3_equiv_pair i j hij
  have h0 : (q ∘ e) 0=cubeUpper c := by rw [Function.comp_apply,he0,hi]
  have h1 : (q ∘ e) 1=cubeLower c := by rw [Function.comp_apply,he1,hj]
  obtain ⟨ha,h2⟩ := cube_double_active_ordered c (q ∘ e) (cube_equations_reindex c q e h.1) h0 h1
  refine ⟨ha,e,?_⟩
  ext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem cube_descent_assemble (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25) :
    CubeAntiprismParameters c q ∨ (CubeDescentCurve c q ∧ HasCubeDescent c q) := by
  by_cases hu : ∃i,q i=cubeUpper c
  · obtain ⟨i,hi⟩ := hu
    by_cases hl : ∃j,q j=cubeLower c
    · obtain ⟨j,hj⟩ := hl
      exact Or.inl (cube_double_active_parameters c q h hc i j hi hj)
    · apply Or.inr
      apply cube_descent_upper_branch c q h hc i hi
      intro k
      rcases lt_or_eq_of_le (h.2 k).1 with ht | he
      · exact ht
      · exact False.elim (hl ⟨k,he.symm⟩)
  · have hhi : ∀k,q k<cubeUpper c := by
      intro k
      rcases lt_or_eq_of_le (h.2 k).2 with ht | he
      · exact ht
      · exact False.elim (hu ⟨k,he⟩)
    by_cases hl : ∃j,q j=cubeLower c
    · obtain ⟨j,hj⟩ := hl
      exact Or.inr (cube_descent_lower_branch c q h hc j hj hhi)
    · apply Or.inr
      apply cube_descent_interior_descent c q h hc
      intro k
      refine ⟨?_,hhi k⟩
      rcases lt_or_eq_of_le (h.2 k).1 with ht | he
      · exact ht
      · exact False.elim (hl ⟨k,he.symm⟩)

#print axioms cube_descent_assemble
end Blueprint.Thomson.Tail.Implementation
