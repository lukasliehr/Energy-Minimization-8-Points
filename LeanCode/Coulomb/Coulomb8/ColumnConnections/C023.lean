import Coulomb8.Columns.C023
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C023

theorem coefficient_list : Columns.C023.coefficients=List.ofFn CoefficientMatrix.column23 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C023
