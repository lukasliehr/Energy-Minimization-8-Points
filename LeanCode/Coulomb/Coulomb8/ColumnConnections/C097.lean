import Coulomb8.Columns.C097
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C097

theorem coefficient_list : Columns.C097.coefficients=List.ofFn CoefficientMatrix.column97 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C097
