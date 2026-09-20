import Coulomb8.Columns.C021
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C021

theorem coefficient_list : Columns.C021.coefficients=List.ofFn CoefficientMatrix.column21 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C021
