import Coulomb8.Columns.C086
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C086

theorem coefficient_list : Columns.C086.coefficients=List.ofFn CoefficientMatrix.column86 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C086
