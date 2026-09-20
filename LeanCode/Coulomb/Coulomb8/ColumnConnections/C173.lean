import Coulomb8.Columns.C173
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C173

theorem coefficient_list : Columns.C173.coefficients=List.ofFn CoefficientMatrix.column173 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C173
