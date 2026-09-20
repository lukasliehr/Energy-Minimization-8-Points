import Coulomb8.Columns.C059
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C059

theorem coefficient_list : Columns.C059.coefficients=List.ofFn CoefficientMatrix.column59 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C059
