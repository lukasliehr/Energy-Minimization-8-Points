import Coulomb8.Columns.C148
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C148

theorem coefficient_list : Columns.C148.coefficients=List.ofFn CoefficientMatrix.column148 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C148
