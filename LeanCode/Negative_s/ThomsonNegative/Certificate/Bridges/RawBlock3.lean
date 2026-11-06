import ThomsonNegative.Certificate.Bridges.RawEntries3_00
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock3_physical (i j : Fin 4) : invariantSubst (rawCoordinate 3 i.val j.val)=kernelRPolynomial 3 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_3_00_00_physical
  · exact rawEntry_3_00_01_physical
  · exact rawEntry_3_00_02_physical
  · exact rawEntry_3_00_03_physical
  · exact rawEntry_3_01_00_physical
  · exact rawEntry_3_01_01_physical
  · exact rawEntry_3_01_02_physical
  · exact rawEntry_3_01_03_physical
  · exact rawEntry_3_02_00_physical
  · exact rawEntry_3_02_01_physical
  · exact rawEntry_3_02_02_physical
  · exact rawEntry_3_02_03_physical
  · exact rawEntry_3_03_00_physical
  · exact rawEntry_3_03_01_physical
  · exact rawEntry_3_03_02_physical
  · exact rawEntry_3_03_03_physical
#print axioms rawBlock3_physical
end ThomsonNegative.Certificate.Bridges
