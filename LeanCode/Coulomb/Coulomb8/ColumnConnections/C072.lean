import Coulomb8.Columns.C072
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C072

theorem coefficient_list : Columns.C072.coefficients=List.ofFn CoefficientMatrix.column72 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C072
