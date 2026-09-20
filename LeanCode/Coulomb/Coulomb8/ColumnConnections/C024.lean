import Coulomb8.Columns.C024
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C024

theorem coefficient_list : Columns.C024.coefficients=List.ofFn CoefficientMatrix.column24 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C024
