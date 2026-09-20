import Coulomb8.Columns.C122
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C122

theorem coefficient_list : Columns.C122.coefficients=List.ofFn CoefficientMatrix.column122 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C122
