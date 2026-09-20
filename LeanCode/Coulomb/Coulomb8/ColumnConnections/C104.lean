import Coulomb8.Columns.C104
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C104

theorem coefficient_list : Columns.C104.coefficients=List.ofFn CoefficientMatrix.column104 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C104
