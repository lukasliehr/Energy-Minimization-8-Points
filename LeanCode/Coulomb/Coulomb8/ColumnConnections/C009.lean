import Coulomb8.Columns.C009
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C009

theorem coefficient_list : Columns.C009.coefficients=List.ofFn CoefficientMatrix.column9 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C009
