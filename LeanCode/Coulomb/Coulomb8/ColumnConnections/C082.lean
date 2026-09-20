import Coulomb8.Columns.C082
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C082

theorem coefficient_list : Columns.C082.coefficients=List.ofFn CoefficientMatrix.column82 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C082
