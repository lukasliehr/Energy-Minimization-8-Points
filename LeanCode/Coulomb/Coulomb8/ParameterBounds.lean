import Coulomb8.Parameter

namespace Coulomb8

def parameterBox : Box := ⟨leftEndpoint,rightEndpoint⟩
theorem parameterBox_contains : parameterBox.Contains a := a_bracket

end Coulomb8
