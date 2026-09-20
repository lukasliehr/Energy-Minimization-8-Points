import Coulomb8.Columns.C011
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C011

theorem coefficient_list : Columns.C011.coefficients=List.ofFn CoefficientMatrix.column11 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C011
