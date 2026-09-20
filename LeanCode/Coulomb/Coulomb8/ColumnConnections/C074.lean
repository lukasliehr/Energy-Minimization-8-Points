import Coulomb8.Columns.C074
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C074

theorem coefficient_list : Columns.C074.coefficients=List.ofFn CoefficientMatrix.column74 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C074
