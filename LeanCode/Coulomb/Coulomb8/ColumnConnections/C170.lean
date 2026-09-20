import Coulomb8.Columns.C170
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C170

theorem coefficient_list : Columns.C170.coefficients=List.ofFn CoefficientMatrix.column170 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C170
