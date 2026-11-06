import AllS.Units.N_G.N_cube_parameters

noncomputable section
open SquareAntiprismVerification Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def HasCubeDescent (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  (c,q)∈closure {z : ℝ × (Fin 3 → ℝ) | CubeFeasible z.1 z.2 ∧ z.1<c}

def CubeDescentCurve (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  ∃ γ : ℝ → ℝ × (Fin 3 → ℝ),ContinuousAt γ 0 ∧ γ 0=(c,q) ∧
    ∀ᶠ t in 𝓝[>] (0:ℝ),CubeFeasible (γ t).1 (γ t).2 ∧ (γ t).1<c

theorem CubeDescentCurve.hasCubeDescent {c : ℝ} {q : Fin 3 → ℝ} (h : CubeDescentCurve c q) :
    HasCubeDescent c q := by
  obtain ⟨γ,hγ,h0,hm⟩ := h
  exact mem_closure_of_tendsto (h0 ▸ hγ.tendsto.mono_left nhdsWithin_le_nhds) hm

theorem cube_equations_reindex (c : ℝ) (q : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3))
    (h : CubeEquations c q) : CubeEquations c (q ∘ e) := by
  refine ⟨h.1,fun k => h.2.1 _,?_,?_⟩
  · exact (Equiv.sum_comp e q).trans h.2.2.1
  · change c^2*(∑k,1/q (e k))=1
    rw [Equiv.sum_comp e (fun k => 1/q k)]
    exact h.2.2.2

theorem cube_feasible_reindex (c : ℝ) (q : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3))
    (h : CubeFeasible c q) : CubeFeasible c (q ∘ e) :=
  ⟨cube_equations_reindex c q e h.1,fun k => h.2 _⟩

theorem cube_bounds_strict (c : ℝ) (hc : 0<c) (hc1 : c<1) : cubeLower c<cubeUpper c := by
  have h1 : 0<1+c := by positivity
  unfold cubeLower cubeUpper
  apply (div_lt_iff₀ h1).mpr
  nlinarith [mul_pos (sub_pos.mpr hc1) (show 0<3*c+1 by positivity)]

end Blueprint.Thomson.Tail.Implementation
