import Coulomb8.Columns.C016
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C016

theorem coefficient_list : Columns.C016.coefficients=List.ofFn CoefficientMatrix.column16 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C016
