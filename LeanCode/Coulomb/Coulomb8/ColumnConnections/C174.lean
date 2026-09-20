import Coulomb8.Columns.C174
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C174

theorem coefficient_list : Columns.C174.coefficients=List.ofFn CoefficientMatrix.column174 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C174
