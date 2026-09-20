import Coulomb8.Columns.C063
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C063

theorem coefficient_list : Columns.C063.coefficients=List.ofFn CoefficientMatrix.column63 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C063
