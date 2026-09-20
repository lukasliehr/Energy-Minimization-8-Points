import Coulomb8.Columns.C026
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C026

theorem coefficient_list : Columns.C026.coefficients=List.ofFn CoefficientMatrix.column26 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C026
