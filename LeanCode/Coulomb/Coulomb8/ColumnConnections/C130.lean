import Coulomb8.Columns.C130
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C130

theorem coefficient_list : Columns.C130.coefficients=List.ofFn CoefficientMatrix.column130 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C130
