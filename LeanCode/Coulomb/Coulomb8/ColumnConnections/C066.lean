import Coulomb8.Columns.C066
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C066

theorem coefficient_list : Columns.C066.coefficients=List.ofFn CoefficientMatrix.column66 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C066
