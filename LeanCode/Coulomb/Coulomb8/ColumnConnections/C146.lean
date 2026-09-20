import Coulomb8.Columns.C146
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C146

theorem coefficient_list : Columns.C146.coefficients=List.ofFn CoefficientMatrix.column146 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C146
