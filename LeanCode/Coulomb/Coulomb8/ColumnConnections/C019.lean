import Coulomb8.Columns.C019
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C019

theorem coefficient_list : Columns.C019.coefficients=List.ofFn CoefficientMatrix.column19 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C019
