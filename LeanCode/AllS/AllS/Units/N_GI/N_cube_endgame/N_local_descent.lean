import AllS.Units.N_GI.N_cube_endgame.N_model_realization

noncomputable section
open Real SquareAntiprismVerification Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def PackingLocalMinimum (Y : Fin 8 → Point) : Prop :=
  IsLocalMinOn packingMaxInner {Z | ∀i,‖Z i‖=1} Y

theorem cube_local_minimum_no_descent (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q)
    (hmin : PackingLocalMinimum (cubeConfiguration e label c q)) : ¬CubeDescentCurve c q := by
  rintro ⟨γ,hγ,h0,hm⟩
  let Y : ℝ → Fin 8 → Point := fun t => cubeConfiguration e label (γ t).1 (γ t).2
  have hY0 : Y 0=cubeConfiguration e label c q := by simp only [Y,h0]
  have hY : ContinuousAt Y 0 :=
    (h0 ▸ cubeConfiguration_continuousAt e label c q h.1.2.1).comp hγ
  have hYn : Tendsto Y (𝓝[>] (0:ℝ)) (nhds (cubeConfiguration e label c q)) := by
    rw [←hY0]
    exact hY.tendsto.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠt in 𝓝[>] (0:ℝ),Y t∈{Z | ∀i,‖Z i‖=1} := by
    filter_upwards [hm] with t ht
    exact cubeConfiguration_unit e he label _ _ ht.1.1
  have hwithin : Tendsto Y (𝓝[>] (0:ℝ)) (𝓝[{Z | ∀i,‖Z i‖=1}] (cubeConfiguration e label c q)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hYn,hmem⟩
  have hmin' : ∀ᶠt in 𝓝[>] (0:ℝ),packingMaxInner (cubeConfiguration e label c q)≤packingMaxInner (Y t) :=
    hwithin.eventually hmin
  obtain ⟨t,ht,hmt⟩ := (hm.and hmin').exists
  rw [cubeConfiguration_maximum e he label c q h] at hmt
  change c≤packingMaxInner (cubeConfiguration e label (γ t).1 (γ t).2) at hmt
  rw [cubeConfiguration_maximum e he label _ _ ht.1] at hmt
  exact (not_lt_of_ge hmt) ht.2

theorem cube_local_minimum_parameters (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25)
    (hmin : PackingLocalMinimum (cubeConfiguration e label c q)) : CubeAntiprismParameters c q := by
  rcases cube_descent_assemble c q h hc with hexc | ⟨hcurve,_⟩
  · exact hexc
  · exact False.elim (cube_local_minimum_no_descent e he label c q h hmin hcurve)

#print axioms cube_local_minimum_parameters
end Blueprint.Thomson.Tail.Implementation
