import Coulomb8.Columns.C162
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C162

theorem coefficient_list : Columns.C162.coefficients=List.ofFn CoefficientMatrix.column162 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C162
