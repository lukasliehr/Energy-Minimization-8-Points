import Coulomb8.Columns.C085
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C085

theorem coefficient_list : Columns.C085.coefficients=List.ofFn CoefficientMatrix.column85 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C085
