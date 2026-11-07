import AllS.Units.N_G.N_cube_descent
import AllS.Units.N_GI.N_cubic_quads.N_cube_labeling

noncomputable section
open Real SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def cubeVertexModel (e : Fin 3 → Point) (c : ℝ) (q : Fin 3 → ℝ) (v : CubeVertex) : Point :=
  if v.1=0 then cubeModelA e q v.2 else cubeModelB e c q v.2

def cubeConfiguration (e : Fin 3 → Point) (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) : Fin 8 → Point :=
  cubeVertexModel e c q ∘ label.symm

theorem cubeSign_square (i : Fin 4) (k : Fin 3) : cubeSign i k*cubeSign i k=1 := by
  fin_cases i <;> fin_cases k <;> norm_num [cubeSign]

theorem cubeModel_units (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    (∀i,‖cubeModelA e q i‖=1) ∧ (∀i,‖cubeModelB e c q i‖=1) := by
  constructor
  · intro i
    have hi := cubeModelA_inner e he q h.2.1 i i
    simp only [cubeSign_square,one_mul,h.2.2.1,real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (cubeModelA e q i)]
  · intro i
    have hi := cubeModelB_inner e he c q h.2.1 i i
    have hs : (∑k,c^2/q k)=1 := by simpa only [Finset.mul_sum,mul_one_div] using h.2.2.2
    simp only [cubeSign_square,one_mul,hs,real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (cubeModelB e c q i)]

theorem cubeVertexModel_unit (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) (v : CubeVertex) :
    ‖cubeVertexModel e c q v‖=1 := by
  unfold cubeVertexModel
  split
  · exact (cubeModel_units e he c q h).1 v.2
  · exact (cubeModel_units e he c q h).2 v.2

theorem cubeVertexModel_bound (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (v w : CubeVertex) (hvw : v≠w) :
    inner ℝ (cubeVertexModel e c q v) (cubeVertexModel e c q w)≤c := by
  obtain ⟨hA,hB,hAB⟩ := (cube_model_bounds_iff e he c q h.1).mpr h.2
  obtain ⟨v,i⟩ := v
  obtain ⟨w,j⟩ := w
  fin_cases v <;> fin_cases w
  · change inner ℝ (cubeModelA e q i) (cubeModelA e q j)≤c
    exact hA i j (fun hij => hvw (Prod.ext rfl hij))
  · exact hAB i j
  · change inner ℝ (cubeModelB e c q i) (cubeModelA e q j)≤c
    rw [real_inner_comm]
    exact hAB j i
  · change inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)≤c
    exact hB i j (fun hij => hvw (Prod.ext rfl hij))

theorem cubeConfiguration_unit (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    ∀i,‖cubeConfiguration e label c q i‖=1 := fun i => cubeVertexModel_unit e he c q h (label.symm i)

theorem cubeConfiguration_bound (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) :
    PackingInnerBound c (cubeConfiguration e label c q) := by
  intro i j hij
  exact cubeVertexModel_bound e he c q h (label.symm i) (label.symm j) (label.symm.injective.ne hij)

theorem cubeConfiguration_maximum (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) :
    packingMaxInner (cubeConfiguration e label c q)=c := by
  apply le_antisymm ((packingMaxInner_le_iff _ c).mpr (cubeConfiguration_bound e he label c q h))
  have hh := inner_le_packingMaxInner (cubeConfiguration e label c q) (label (0,0)) (label (1,1))
    (label.injective.ne (by decide))
  have heq : inner ℝ (cubeConfiguration e label c q (label (0,0)))
      (cubeConfiguration e label c q (label (1,1)))=c := by
    change inner ℝ (cubeVertexModel e c q (label.symm (label (0,0))))
      (cubeVertexModel e c q (label.symm (label (1,1))))=c
    simp only [Equiv.symm_apply_apply]
    change inner ℝ (cubeModelA e q 0) (cubeModelB e c q 1)=c
    rw [cubeModel_cross_inner e he c q h.1.2.1,if_neg (by decide)]
  rwa [heq] at hh

theorem cubeConfiguration_isConfiguration (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<1) :
    Blueprint.Thomson.IsConfiguration (cubeConfiguration e label c q) :=
  packingInnerBound_configuration _ c (cubeConfiguration_unit e he label c q h.1) hc
    (cubeConfiguration_bound e he label c q h)

theorem cubeConfiguration_continuousAt (e : Fin 3 → Point) (label : CubeVertex ≃ Fin 8)
    (c : ℝ) (q : Fin 3 → ℝ) (hq : ∀k,0<q k) :
    ContinuousAt (fun z : ℝ × (Fin 3 → ℝ) => cubeConfiguration e label z.1 z.2) (c,q) := by
  apply continuousAt_pi.mpr
  intro i
  dsimp only [cubeConfiguration,Function.comp_apply,cubeVertexModel]
  split
  · exact (cubeModelA_continuous e _).continuousAt
  · unfold cubeModelB
    fun_prop (disch := exact (Real.sqrt_pos.mpr (hq _)).ne')

#print axioms cubeConfiguration_isConfiguration
#print axioms cubeConfiguration_maximum
#print axioms cubeConfiguration_continuousAt
end Blueprint.Thomson.Tail.Implementation
