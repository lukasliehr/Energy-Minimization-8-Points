import Coulomb8.Columns.C182
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C182

theorem coefficient_list : Columns.C182.coefficients=List.ofFn CoefficientMatrix.column182 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C182
