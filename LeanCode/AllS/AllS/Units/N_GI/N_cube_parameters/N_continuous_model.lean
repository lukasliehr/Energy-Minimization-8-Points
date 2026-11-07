import AllS.Units.N_GI.N_cube_parameters.N_definitions

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cubeModelA_continuous (e : Fin 3 → Point) (i : Fin 4) :
    Continuous (fun z : ℝ × (Fin 3 → ℝ) => cubeModelA e z.2 i) := by
  unfold cubeModelA
  fun_prop

theorem cubeModelB_continuousOn (e : Fin 3 → Point) (i : Fin 4) :
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => cubeModelB e z.1 z.2 i)
      {z | ∀k,0<z.2 k} := by
  intro z hz
  have h : ContinuousAt (fun z : ℝ × (Fin 3 → ℝ) => cubeModelB e z.1 z.2 i) z := by
    unfold cubeModelB
    fun_prop (disch := exact (Real.sqrt_pos.mpr (hz _)).ne')
  exact h.continuousWithinAt

theorem cube_parameters_continuous_model (e : Fin 3 → Point) :
    (∀i,Continuous (fun z : ℝ × (Fin 3 → ℝ) => cubeModelA e z.2 i)) ∧
    (∀i,ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => cubeModelB e z.1 z.2 i)
      {z | ∀k,0<z.2 k}) :=
  ⟨cubeModelA_continuous e,cubeModelB_continuousOn e⟩

#print axioms cube_parameters_continuous_model
end Blueprint.Thomson.Tail.Implementation
