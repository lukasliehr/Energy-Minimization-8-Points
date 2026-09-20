import Coulomb8.Columns.C150
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C150

theorem coefficient_list : Columns.C150.coefficients=List.ofFn CoefficientMatrix.column150 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C150
