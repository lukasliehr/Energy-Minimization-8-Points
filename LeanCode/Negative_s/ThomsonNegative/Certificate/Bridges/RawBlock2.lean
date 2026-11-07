import ThomsonNegative.Certificate.Bridges.RawEntries2_00
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock2_physical (i j : Fin 5) : invariantSubst (rawCoordinate 2 i.val j.val)=kernelRPolynomial 2 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_2_00_00_physical
  · exact rawEntry_2_00_01_physical
  · exact rawEntry_2_00_02_physical
  · exact rawEntry_2_00_03_physical
  · exact rawEntry_2_00_04_physical
  · exact rawEntry_2_01_00_physical
  · exact rawEntry_2_01_01_physical
  · exact rawEntry_2_01_02_physical
  · exact rawEntry_2_01_03_physical
  · exact rawEntry_2_01_04_physical
  · exact rawEntry_2_02_00_physical
  · exact rawEntry_2_02_01_physical
  · exact rawEntry_2_02_02_physical
  · exact rawEntry_2_02_03_physical
  · exact rawEntry_2_02_04_physical
  · exact rawEntry_2_03_00_physical
  · exact rawEntry_2_03_01_physical
  · exact rawEntry_2_03_02_physical
  · exact rawEntry_2_03_03_physical
  · exact rawEntry_2_03_04_physical
  · exact rawEntry_2_04_00_physical
  · exact rawEntry_2_04_01_physical
  · exact rawEntry_2_04_02_physical
  · exact rawEntry_2_04_03_physical
  · exact rawEntry_2_04_04_physical
#print axioms rawBlock2_physical
end ThomsonNegative.Certificate.Bridges
