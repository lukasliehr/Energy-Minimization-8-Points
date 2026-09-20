import Coulomb8.Columns.C106
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C106

theorem coefficient_list : Columns.C106.coefficients=List.ofFn CoefficientMatrix.column106 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C106
