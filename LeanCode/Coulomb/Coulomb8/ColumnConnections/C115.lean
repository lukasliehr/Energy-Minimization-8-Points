import Coulomb8.Columns.C115
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C115

theorem coefficient_list : Columns.C115.coefficients=List.ofFn CoefficientMatrix.column115 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C115
