import Coulomb8.Columns.C126
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C126

theorem coefficient_list : Columns.C126.coefficients=List.ofFn CoefficientMatrix.column126 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C126
