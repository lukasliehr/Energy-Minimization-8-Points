import Coulomb8.HermiteSemantics

namespace Coulomb8

noncomputable def target (r : Fin 102) : ℝ :=
  if r=0 then Hpoly.coeff 0-G a/28
  else if r.val ≤ 12 then Hpoly.coeff r.val/3 else 0

end Coulomb8
