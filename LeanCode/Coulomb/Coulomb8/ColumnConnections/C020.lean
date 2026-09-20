import Coulomb8.Columns.C020
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C020

theorem coefficient_list : Columns.C020.coefficients=List.ofFn CoefficientMatrix.column20 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C020
