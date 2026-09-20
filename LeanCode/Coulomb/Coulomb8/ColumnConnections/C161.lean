import Coulomb8.Columns.C161
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C161

theorem coefficient_list : Columns.C161.coefficients=List.ofFn CoefficientMatrix.column161 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C161
