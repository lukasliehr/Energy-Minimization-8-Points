import Coulomb8.Columns.C154
import Coulomb8.CoefficientMatrix.C19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C154

theorem coefficient_list : Columns.C154.coefficients=List.ofFn CoefficientMatrix.column154 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C154
