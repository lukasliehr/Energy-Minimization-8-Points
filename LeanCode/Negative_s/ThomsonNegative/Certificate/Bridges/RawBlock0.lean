import ThomsonNegative.Certificate.Bridges.RawEntries0_00
import ThomsonNegative.Certificate.Bridges.RawEntries0_01
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock0_physical (i j : Fin 7) : invariantSubst (rawCoordinate 0 i.val j.val)=kernelRPolynomial 0 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_0_00_00_physical
  · exact rawEntry_0_00_01_physical
  · exact rawEntry_0_00_02_physical
  · exact rawEntry_0_00_03_physical
  · exact rawEntry_0_00_04_physical
  · exact rawEntry_0_00_05_physical
  · exact rawEntry_0_00_06_physical
  · exact rawEntry_0_01_00_physical
  · exact rawEntry_0_01_01_physical
  · exact rawEntry_0_01_02_physical
  · exact rawEntry_0_01_03_physical
  · exact rawEntry_0_01_04_physical
  · exact rawEntry_0_01_05_physical
  · exact rawEntry_0_01_06_physical
  · exact rawEntry_0_02_00_physical
  · exact rawEntry_0_02_01_physical
  · exact rawEntry_0_02_02_physical
  · exact rawEntry_0_02_03_physical
  · exact rawEntry_0_02_04_physical
  · exact rawEntry_0_02_05_physical
  · exact rawEntry_0_02_06_physical
  · exact rawEntry_0_03_00_physical
  · exact rawEntry_0_03_01_physical
  · exact rawEntry_0_03_02_physical
  · exact rawEntry_0_03_03_physical
  · exact rawEntry_0_03_04_physical
  · exact rawEntry_0_03_05_physical
  · exact rawEntry_0_03_06_physical
  · exact rawEntry_0_04_00_physical
  · exact rawEntry_0_04_01_physical
  · exact rawEntry_0_04_02_physical
  · exact rawEntry_0_04_03_physical
  · exact rawEntry_0_04_04_physical
  · exact rawEntry_0_04_05_physical
  · exact rawEntry_0_04_06_physical
  · exact rawEntry_0_05_00_physical
  · exact rawEntry_0_05_01_physical
  · exact rawEntry_0_05_02_physical
  · exact rawEntry_0_05_03_physical
  · exact rawEntry_0_05_04_physical
  · exact rawEntry_0_05_05_physical
  · exact rawEntry_0_05_06_physical
  · exact rawEntry_0_06_00_physical
  · exact rawEntry_0_06_01_physical
  · exact rawEntry_0_06_02_physical
  · exact rawEntry_0_06_03_physical
  · exact rawEntry_0_06_04_physical
  · exact rawEntry_0_06_05_physical
  · exact rawEntry_0_06_06_physical
#print axioms rawBlock0_physical
end ThomsonNegative.Certificate.Bridges
