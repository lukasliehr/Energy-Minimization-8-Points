import Coulomb8.Columns.C100
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C100

theorem coefficient_list : Columns.C100.coefficients=List.ofFn CoefficientMatrix.column100 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C100
