import Coulomb8.Columns.C107
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C107

theorem coefficient_list : Columns.C107.coefficients=List.ofFn CoefficientMatrix.column107 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C107
