import Coulomb8.Columns.C171
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C171

theorem coefficient_list : Columns.C171.coefficients=List.ofFn CoefficientMatrix.column171 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C171
