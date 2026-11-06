import AllS.Units.N_AI.N_boundary_arithmetic.GeometryKernels
import AllS.Units.N_AI.N_boundary_arithmetic.Generated.Contact_5_1
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation
theorem contact_arithmetic_5_1 : normalize (contactRaw (5,0)) = Generated.Contact_5_1.value := by decide +kernel
theorem contact_physical_5_1 (y : Fin 13 → ℝ) : eval Generated.Contact_5_1.value y = boundaryContactPolynomial (5,0) y := by
  rw [←contact_arithmetic_5_1,eval_normalize,contactRaw_eval]
#print axioms contact_physical_5_1
end Blueprint.CAP.BoundaryDirect
