import Coulomb8.Setup

namespace Coulomb8

noncomputable def q : ℝ := Real.sqrt 2
noncomputable def dMinus (s : ℝ) : ℝ := 2-q+(2+q)*s
noncomputable def dPlus (s : ℝ) : ℝ := 2+q+(2-q)*s
noncomputable def F (s : ℝ) : ℝ :=
  (2*q+1)/((1-s)*Real.sqrt (1-s))
    -4*(2+q)/(dMinus s*Real.sqrt (dMinus s))
    -4*(2-q)/(dPlus s*Real.sqrt (dPlus s))

def leftEndpoint : ℚ := 3140893678892018673812332 / 10000000000000000000000000
def rightEndpoint : ℚ := 3140893678892018673812333 / 10000000000000000000000000

noncomputable def nodeA (s : ℝ) : ℝ := s
noncomputable def nodeB (s : ℝ) : ℝ := 2*s-1
noncomputable def nodeC (s : ℝ) : ℝ := -s+(1-s)/q
noncomputable def nodeD (s : ℝ) : ℝ := -s-(1-s)/q
noncomputable def nodes (s : ℝ) : Fin 4 → ℝ := ![nodeA s,nodeB s,nodeC s,nodeD s]
noncomputable def phi (t : ℝ) : ℝ := 1 / Real.sqrt (2-2*t)
noncomputable def G (s : ℝ) : ℝ :=
  (4*q+2)/Real.sqrt (1-s)+8/Real.sqrt (dMinus s)+8/Real.sqrt (dPlus s)

end Coulomb8
