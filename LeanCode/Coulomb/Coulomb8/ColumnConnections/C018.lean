import Coulomb8.Columns.C018
import Coulomb8.CoefficientMatrix.C02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C018

theorem coefficient_list : Columns.C018.coefficients=List.ofFn CoefficientMatrix.column18 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C018
