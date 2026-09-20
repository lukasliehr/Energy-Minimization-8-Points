import Coulomb8.Columns.C043
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C043

theorem coefficient_list : Columns.C043.coefficients=List.ofFn CoefficientMatrix.column43 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C043
