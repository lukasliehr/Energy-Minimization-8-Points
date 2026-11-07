import ThomsonNegative.Certificate.Bridges.RawEntries4_00
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock4_physical (i j : Fin 3) : invariantSubst (rawCoordinate 4 i.val j.val)=kernelRPolynomial 4 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_4_00_00_physical
  · exact rawEntry_4_00_01_physical
  · exact rawEntry_4_00_02_physical
  · exact rawEntry_4_01_00_physical
  · exact rawEntry_4_01_01_physical
  · exact rawEntry_4_01_02_physical
  · exact rawEntry_4_02_00_physical
  · exact rawEntry_4_02_01_physical
  · exact rawEntry_4_02_02_physical
#print axioms rawBlock4_physical
end ThomsonNegative.Certificate.Bridges
