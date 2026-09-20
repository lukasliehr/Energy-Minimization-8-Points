import Coulomb8.Columns.C006
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C006

theorem coefficient_list : Columns.C006.coefficients=List.ofFn CoefficientMatrix.column6 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C006
