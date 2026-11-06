import AllS.Units.N_GI.N_cube_descent.N_upper_model

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_upper_curve_ordered (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25)
    (h0 : q 0=cubeUpper c) (h21 : q 2≤q 1)
    (hlo : ∀k,cubeLower c<q k) (hhi : ∀k,k≠0 → q k<cubeUpper c) : CubeDescentCurve c q := by
  let C : ℝ → ℝ := fun t => c-t
  let Q : ℝ → Fin 3 → ℝ := fun t => cubeUpperModel (C t)
  have hC : ContinuousAt C 0 := by unfold C;fun_prop
  have hC0 : C 0=c := by simp [C]
  have hQ : ContinuousAt Q 0 := (hC0 ▸ cubeUpperModel_continuousAt c h.1.1).comp hC
  have hQ0 : Q 0=q := by change cubeUpperModel (c-0)=q;rw [sub_zero];exact cubeUpperModel_recover c q h.1 hc h0 h21
  have hL : ContinuousAt (fun t => cubeLower (C t)) 0 :=
    (hC0 ▸ cubeLower_continuousAt c h.1.1).comp hC
  have hU : ContinuousAt (fun t => cubeUpper (C t)) 0 := cubeUpper_continuous.continuousAt.comp hC
  have hb : ∀ᶠt in nhds (0:ℝ),∀k,cubeLower (C t)<Q t k ∧ Q t k≤cubeUpper (C t) := by
    apply Filter.eventually_all.mpr
    intro k
    have hqk : ContinuousAt (fun t => Q t k) 0 := (continuousAt_pi.mp hQ) k
    have hlo' := hL.eventually_lt hqk (by simpa only [hC0,hQ0] using hlo k)
    have hhi' : ∀ᶠt in nhds (0:ℝ),Q t k≤cubeUpper (C t) := by
      by_cases hk : k=0
      · subst k;exact Filter.Eventually.of_forall (fun t => le_rfl)
      · exact (hqk.eventually_lt hU (by simpa only [hC0,hQ0] using hhi k hk)).mono (fun _ ht => ht.le)
    exact hlo'.and hhi'
  refine ⟨fun t => (C t,Q t),hC.prodMk hQ,by change (C 0,Q 0)=(c,q);rw [hC0,hQ0],?_⟩
  have ht0 : ∀ᶠt in nhds (0:ℝ),t<c := continuousAt_id.eventually_lt continuousAt_const h.1.1
  filter_upwards [nhdsWithin_le_nhds hb,nhdsWithin_le_nhds ht0,self_mem_nhdsWithin] with t hbt htq ht
  have htpos : 0<t := ht
  have hct : 0<c-t := by linarith
  refine ⟨⟨cubeUpperModel_equations (c-t) hct (by linarith),fun k => ⟨(hbt k).1.le,(hbt k).2⟩⟩,?_⟩
  change c-t<c
  linarith

theorem cube_upper_curve_zero (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25)
    (h0 : q 0=cubeUpper c) (hlo : ∀k,cubeLower c<q k) (hhi : ∀k,k≠0 → q k<cubeUpper c) :
    CubeDescentCurve c q := by
  by_cases h21 : q 2≤q 1
  · exact cube_upper_curve_ordered c q h hc h0 h21 hlo hhi
  · let e : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have he0 : e 0=0 := by decide
    have he1 : e 1=2 := by decide
    have he2 : e 2=1 := by decide
    have hs : CubeDescentCurve c (q ∘ e) := by
      apply cube_upper_curve_ordered c (q ∘ e) (cube_feasible_reindex c q e h) hc
      · simpa only [Function.comp_apply,he0] using h0
      · simpa only [Function.comp_apply,he1,he2] using (le_of_lt (lt_of_not_ge h21))
      · exact fun k => hlo (e k)
      · intro k hk
        apply hhi (e k)
        intro he
        exact hk (e.injective (he.trans he0.symm))
    have hs' := hs.reindex e.symm
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using hs'

theorem cube_descent_upper_branch (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25)
    (i : Fin 3) (hi : q i=cubeUpper c) (hlo : ∀k,cubeLower c<q k) :
    CubeDescentCurve c q ∧ HasCubeDescent c q := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  have he0 : e 0=i := Equiv.swap_apply_left 0 i
  have hs : CubeDescentCurve c (q ∘ e) := by
    apply cube_upper_curve_zero c (q ∘ e) (cube_feasible_reindex c q e h) hc
    · simpa only [Function.comp_apply,he0] using hi
    · exact fun k => hlo (e k)
    · intro k hk
      rcases lt_or_eq_of_le (h.2 (e k)).2 with ht | he
      · exact ht
      · have hei := cube_at_most_one_upper c q h.1 (e k) i he hi
        exact False.elim (hk (e.injective (hei.trans he0.symm)))
  have hh : CubeDescentCurve c q := by
    have hs' := hs.reindex e.symm
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using hs'
  exact ⟨hh,hh.hasCubeDescent⟩

#print axioms cube_descent_upper_branch
end Blueprint.Thomson.Tail.Implementation
