import Coulomb8.Columns.C163
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C163

theorem coefficient_list : Columns.C163.coefficients=List.ofFn CoefficientMatrix.column163 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C163
