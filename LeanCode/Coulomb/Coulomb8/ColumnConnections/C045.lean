import Coulomb8.Columns.C045
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C045

theorem coefficient_list : Columns.C045.coefficients=List.ofFn CoefficientMatrix.column45 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C045
