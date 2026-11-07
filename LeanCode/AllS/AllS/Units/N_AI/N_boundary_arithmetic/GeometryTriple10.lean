import AllS.Units.N_AI.N_boundary_arithmetic.GeometryData
import AllS.Units.N_G.N_boundary_basis

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation
theorem triple_physical_10 (i : Fin 8) (k : Fin 3) : qeval (tripleData 10 i k) = boundaryTriple 10 i k := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hi : (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt 2 / 2 := by field_simp; nlinarith
  have hs3 : (Real.sqrt (2 : ℝ)) ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ,hs]
  fin_cases i <;> fin_cases k <;> norm_num [tripleData, qeval, boundaryTriple, boundaryATriple, boundaryBTriple, angularCos, angularSin, layerSign, boundaryCos2, boundarySin2, boundaryCos3, boundarySin3, packingHeight, one_div, hi] <;> ring_nf <;> simp [hs,hs3] <;> ring
#print axioms triple_physical_10
end Blueprint.CAP.BoundaryDirect
