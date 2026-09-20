import Coulomb8.Columns.C052
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C052

theorem coefficient_list : Columns.C052.coefficients=List.ofFn CoefficientMatrix.column52 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C052
