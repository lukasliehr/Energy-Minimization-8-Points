import AllS.Units.N_AI.N_boundary_arithmetic.GeometryKernels
import AllS.Units.N_AI.N_boundary_arithmetic.Generated.Contact_2_2
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation
theorem contact_arithmetic_2_2 : normalize (contactRaw (2,1)) = Generated.Contact_2_2.value := by decide +kernel
theorem contact_physical_2_2 (y : Fin 13 → ℝ) : eval Generated.Contact_2_2.value y = boundaryContactPolynomial (2,1) y := by
  rw [←contact_arithmetic_2_2,eval_normalize,contactRaw_eval]
#print axioms contact_physical_2_2
end Blueprint.CAP.BoundaryDirect
