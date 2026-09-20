import Coulomb8.Columns.C039
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C039

theorem coefficient_list : Columns.C039.coefficients=List.ofFn CoefficientMatrix.column39 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C039
