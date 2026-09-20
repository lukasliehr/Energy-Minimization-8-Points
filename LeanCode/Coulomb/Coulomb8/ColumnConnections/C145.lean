import Coulomb8.Columns.C145
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C145

theorem coefficient_list : Columns.C145.coefficients=List.ofFn CoefficientMatrix.column145 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C145
