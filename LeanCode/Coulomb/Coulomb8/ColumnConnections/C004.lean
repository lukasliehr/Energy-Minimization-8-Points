import Coulomb8.Columns.C004
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C004

theorem coefficient_list : Columns.C004.coefficients=List.ofFn CoefficientMatrix.column4 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C004
