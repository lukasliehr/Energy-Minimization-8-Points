import Coulomb8.Columns.C109
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C109

theorem coefficient_list : Columns.C109.coefficients=List.ofFn CoefficientMatrix.column109 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C109
