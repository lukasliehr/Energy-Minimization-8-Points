import Coulomb8.Columns.C077
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C077

theorem coefficient_list : Columns.C077.coefficients=List.ofFn CoefficientMatrix.column77 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C077
