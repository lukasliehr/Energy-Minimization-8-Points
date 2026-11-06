import AllS.Units.N_AI.N_boundary_arithmetic.GeometryKernels
import AllS.Units.N_AI.N_boundary_arithmetic.Generated.Contact_7_1
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation
theorem contact_arithmetic_7_1 : normalize (contactRaw (7,0)) = Generated.Contact_7_1.value := by decide +kernel
theorem contact_physical_7_1 (y : Fin 13 → ℝ) : eval Generated.Contact_7_1.value y = boundaryContactPolynomial (7,0) y := by
  rw [←contact_arithmetic_7_1,eval_normalize,contactRaw_eval]
#print axioms contact_physical_7_1
end Blueprint.CAP.BoundaryDirect
