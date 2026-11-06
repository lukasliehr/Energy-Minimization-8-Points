import AllS.Units.N_AI.N_boundary_arithmetic.GeometryKernels
import AllS.Units.N_AI.N_boundary_arithmetic.Generated.Contact_6_1
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation
theorem contact_arithmetic_6_1 : normalize (contactRaw (6,0)) = Generated.Contact_6_1.value := by decide +kernel
theorem contact_physical_6_1 (y : Fin 13 → ℝ) : eval Generated.Contact_6_1.value y = boundaryContactPolynomial (6,0) y := by
  rw [←contact_arithmetic_6_1,eval_normalize,contactRaw_eval]
#print axioms contact_physical_6_1
end Blueprint.CAP.BoundaryDirect
