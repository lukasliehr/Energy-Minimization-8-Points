import AllS.Units.N_GI.N_cube_descent.N_upper_branch

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

theorem CubeDescentCurve.dual {c : ℝ} {q : Fin 3 → ℝ} (h : CubeDescentCurve c q)
    (hfeas : CubeFeasible c q) : CubeDescentCurve c (cubeDual c q) := by
  obtain ⟨γ,hγ,h0,hm⟩ := h
  let D : ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ) := fun z => (z.1,cubeDual z.1 z.2)
  have hD : ContinuousAt D (c,q) := by
    apply ContinuousAt.prodMk continuousAt_fst
    apply continuousAt_pi.mpr
    intro k
    unfold cubeDual
    exact (continuousAt_fst.pow 2).div
      ((continuous_apply k).continuousAt.comp continuousAt_snd) (hfeas.1.2.1 k).ne'
  refine ⟨D ∘ γ,(h0 ▸ hD).comp hγ,by simp only [Function.comp_apply,h0,D],?_⟩
  filter_upwards [hm] with t ht
  exact ⟨(cube_parameters_duality _ _ ht.1).1,ht.2⟩

theorem cube_descent_lower_branch (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25)
    (i : Fin 3) (hi : q i=cubeLower c) (hhi : ∀k,q k<cubeUpper c) :
    CubeDescentCurve c q ∧ HasCubeDescent c q := by
  obtain ⟨hd,hinv,hu,hl⟩ := cube_parameters_duality c q h
  have hdu : cubeDual c q i=cubeUpper c := (hu i).mpr hi
  have hdl : ∀k,cubeLower c<cubeDual c q k := by
    intro k
    rcases lt_or_eq_of_le (hd.2 k).1 with ht | he
    · exact ht
    · have he' : q k=cubeUpper c := (hl k).mp he.symm
      exact False.elim ((ne_of_lt (hhi k)) he')
  have hcand := (cube_descent_upper_branch c (cubeDual c q) hd hc i hdu hdl).1
  have hh : CubeDescentCurve c q := by
    have hdcurve := hcand.dual hd
    simpa only [hinv] using hdcurve
  exact ⟨hh,hh.hasCubeDescent⟩

#print axioms cube_descent_lower_branch
end Blueprint.Thomson.Tail.Implementation
