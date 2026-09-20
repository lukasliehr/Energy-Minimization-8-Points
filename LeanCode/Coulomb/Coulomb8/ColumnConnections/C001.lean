import Coulomb8.Columns.C001
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C001

theorem coefficient_list : Columns.C001.coefficients=List.ofFn CoefficientMatrix.column1 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C001
