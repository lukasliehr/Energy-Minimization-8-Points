import Coulomb8.Columns.C164
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C164

theorem coefficient_list : Columns.C164.coefficients=List.ofFn CoefficientMatrix.column164 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C164
