import Coulomb8.Columns.C168
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C168

theorem coefficient_list : Columns.C168.coefficients=List.ofFn CoefficientMatrix.column168 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C168
