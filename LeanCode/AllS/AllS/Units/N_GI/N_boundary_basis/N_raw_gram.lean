import AllS.Units.N_GI.N_boundary_basis.N_definitions

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
theorem boundaryRaw_gram (j k : Fin 16) :
    inner ℝ (boundaryRaw j) (boundaryRaw k)=if j=k then boundaryWeight j else 0 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : √(2:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [PiLp.inner_apply]
  fin_cases j <;> fin_cases k <;>
    norm_num [boundaryRaw,boundaryRawPair,boundaryWeight,boundaryCos2,boundarySin2,
      boundaryCos3,boundarySin3,angularCos,angularSin,layerSign,PiLp.inner_apply,
      Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
    field_simp <;> norm_num [hs] <;> ring

theorem boundaryWeight_pos (j : Fin 16) : 0<boundaryWeight j := by
  obtain ⟨hH,hR,_,_⟩ := packing_parameters
  fin_cases j <;> simp [boundaryWeight] <;> positivity

#print axioms boundaryRaw_gram
end Blueprint.Thomson.Tail.Implementation
