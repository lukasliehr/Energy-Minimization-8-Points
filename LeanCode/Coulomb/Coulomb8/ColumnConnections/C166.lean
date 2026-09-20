import Coulomb8.Columns.C166
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C166

theorem coefficient_list : Columns.C166.coefficients=List.ofFn CoefficientMatrix.column166 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C166
