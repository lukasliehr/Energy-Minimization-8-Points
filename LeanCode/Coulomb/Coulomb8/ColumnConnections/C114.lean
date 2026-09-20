import Coulomb8.Columns.C114
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C114

theorem coefficient_list : Columns.C114.coefficients=List.ofFn CoefficientMatrix.column114 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C114
