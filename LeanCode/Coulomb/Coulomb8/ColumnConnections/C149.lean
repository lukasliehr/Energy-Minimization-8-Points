import Coulomb8.Columns.C149
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C149

theorem coefficient_list : Columns.C149.coefficients=List.ofFn CoefficientMatrix.column149 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C149
