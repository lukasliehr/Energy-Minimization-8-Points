import ThomsonNegative.Certificate.Bridges.RawEntries1_00
import ThomsonNegative.Certificate.Bridges.RawEntries1_01
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock1_physical (i j : Fin 6) : invariantSubst (rawCoordinate 1 i.val j.val)=kernelRPolynomial 1 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_1_00_00_physical
  · exact rawEntry_1_00_01_physical
  · exact rawEntry_1_00_02_physical
  · exact rawEntry_1_00_03_physical
  · exact rawEntry_1_00_04_physical
  · exact rawEntry_1_00_05_physical
  · exact rawEntry_1_01_00_physical
  · exact rawEntry_1_01_01_physical
  · exact rawEntry_1_01_02_physical
  · exact rawEntry_1_01_03_physical
  · exact rawEntry_1_01_04_physical
  · exact rawEntry_1_01_05_physical
  · exact rawEntry_1_02_00_physical
  · exact rawEntry_1_02_01_physical
  · exact rawEntry_1_02_02_physical
  · exact rawEntry_1_02_03_physical
  · exact rawEntry_1_02_04_physical
  · exact rawEntry_1_02_05_physical
  · exact rawEntry_1_03_00_physical
  · exact rawEntry_1_03_01_physical
  · exact rawEntry_1_03_02_physical
  · exact rawEntry_1_03_03_physical
  · exact rawEntry_1_03_04_physical
  · exact rawEntry_1_03_05_physical
  · exact rawEntry_1_04_00_physical
  · exact rawEntry_1_04_01_physical
  · exact rawEntry_1_04_02_physical
  · exact rawEntry_1_04_03_physical
  · exact rawEntry_1_04_04_physical
  · exact rawEntry_1_04_05_physical
  · exact rawEntry_1_05_00_physical
  · exact rawEntry_1_05_01_physical
  · exact rawEntry_1_05_02_physical
  · exact rawEntry_1_05_03_physical
  · exact rawEntry_1_05_04_physical
  · exact rawEntry_1_05_05_physical
#print axioms rawBlock1_physical
end ThomsonNegative.Certificate.Bridges
