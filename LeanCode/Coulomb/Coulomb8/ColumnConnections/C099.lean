import Coulomb8.Columns.C099
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C099

theorem coefficient_list : Columns.C099.coefficients=List.ofFn CoefficientMatrix.column99 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C099
