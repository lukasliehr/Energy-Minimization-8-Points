import Coulomb8.Dyadic
import Coulomb8.ParameterBounds

namespace Coulomb8

def parameterDyadic : Dyadic := ⟨106879073530039017138168416880705077704,106879073530039017138168450908941769799⟩

theorem parameterDyadic_contains : parameterDyadic.Contains a := by
  have hl : (parameterDyadic.lo : ℚ) ≤ (Dyadic.scale : ℚ)*leftEndpoint := by decide +kernel
  have hu : (Dyadic.scale : ℚ)*rightEndpoint ≤ (parameterDyadic.hi : ℚ) := by decide +kernel
  have hlr : (parameterDyadic.lo : ℝ) ≤ (Dyadic.scale : ℝ)*(leftEndpoint : ℝ) := by exact_mod_cast hl
  have hur : (Dyadic.scale : ℝ)*(rightEndpoint : ℝ) ≤ (parameterDyadic.hi : ℝ) := by exact_mod_cast hu
  exact ⟨hlr.trans (mul_le_mul_of_nonneg_left a_bracket.1 Dyadic.scale_pos.le),
    (mul_le_mul_of_nonneg_left a_bracket.2 Dyadic.scale_pos.le).trans hur⟩

end Coulomb8
