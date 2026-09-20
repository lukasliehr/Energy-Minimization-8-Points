import Coulomb8.Columns.C069
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C069

theorem coefficient_list : Columns.C069.coefficients=List.ofFn CoefficientMatrix.column69 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C069
