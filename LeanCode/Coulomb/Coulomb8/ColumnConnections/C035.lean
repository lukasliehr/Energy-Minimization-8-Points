import Coulomb8.Columns.C035
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C035

theorem coefficient_list : Columns.C035.coefficients=List.ofFn CoefficientMatrix.column35 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C035
