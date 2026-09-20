import Coulomb8.Columns.C116
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C116

theorem coefficient_list : Columns.C116.coefficients=List.ofFn CoefficientMatrix.column116 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C116
