import Coulomb8.Columns.C034
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C034

theorem coefficient_list : Columns.C034.coefficients=List.ofFn CoefficientMatrix.column34 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C034
