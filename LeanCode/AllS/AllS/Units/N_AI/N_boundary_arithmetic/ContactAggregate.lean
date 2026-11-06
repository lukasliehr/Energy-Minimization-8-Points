import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck0_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck0_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck1_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck1_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck2_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck2_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck3_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck3_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck4_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck4_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck5_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck5_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck6_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck6_2
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck7_1
import AllS.Units.N_AI.N_boundary_arithmetic.ContactCheck7_2

namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

def contactValue (e : ContactIndex) : Poly :=
  (![![Generated.Contact_0_1.value,Generated.Contact_0_2.value],
    ![Generated.Contact_1_1.value,Generated.Contact_1_2.value],
    ![Generated.Contact_2_1.value,Generated.Contact_2_2.value],
    ![Generated.Contact_3_1.value,Generated.Contact_3_2.value],
    ![Generated.Contact_4_1.value,Generated.Contact_4_2.value],
    ![Generated.Contact_5_1.value,Generated.Contact_5_2.value],
    ![Generated.Contact_6_1.value,Generated.Contact_6_2.value],
    ![Generated.Contact_7_1.value,Generated.Contact_7_2.value]]) e.1 e.2

theorem contactValue_eval (e : ContactIndex) (y : Fin 13 → ℝ) :
    eval (contactValue e) y = boundaryContactPolynomial e y := by
  rcases e with ⟨i,d⟩
  fin_cases i <;> fin_cases d
  · exact contact_physical_0_1 y
  · exact contact_physical_0_2 y
  · exact contact_physical_1_1 y
  · exact contact_physical_1_2 y
  · exact contact_physical_2_1 y
  · exact contact_physical_2_2 y
  · exact contact_physical_3_1 y
  · exact contact_physical_3_2 y
  · exact contact_physical_4_1 y
  · exact contact_physical_4_2 y
  · exact contact_physical_5_1 y
  · exact contact_physical_5_2 y
  · exact contact_physical_6_1 y
  · exact contact_physical_6_2 y
  · exact contact_physical_7_1 y
  · exact contact_physical_7_2 y

#print axioms contactValue_eval
end Blueprint.CAP.BoundaryDirect
