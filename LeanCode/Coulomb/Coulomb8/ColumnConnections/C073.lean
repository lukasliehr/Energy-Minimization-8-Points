import Coulomb8.Columns.C073
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C073

theorem coefficient_list : Columns.C073.coefficients=List.ofFn CoefficientMatrix.column73 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C073
