import Coulomb8.Columns.C017
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C017

theorem coefficient_list : Columns.C017.coefficients=List.ofFn CoefficientMatrix.column17 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C017
