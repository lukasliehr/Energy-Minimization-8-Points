import Coulomb8.Columns.C049
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C049

theorem coefficient_list : Columns.C049.coefficients=List.ofFn CoefficientMatrix.column49 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C049
