import Coulomb8.Columns.C186
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C186

theorem coefficient_list : Columns.C186.coefficients=List.ofFn CoefficientMatrix.column186 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C186
