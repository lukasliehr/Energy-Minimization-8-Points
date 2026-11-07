import ThomsonNegative.Certificate.Bridges.RawEntries5_00
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
theorem rawBlock5_physical (i j : Fin 2) : invariantSubst (rawCoordinate 5 i.val j.val)=kernelRPolynomial 5 i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact rawEntry_5_00_00_physical
  · exact rawEntry_5_00_01_physical
  · exact rawEntry_5_01_00_physical
  · exact rawEntry_5_01_01_physical
#print axioms rawBlock5_physical
end ThomsonNegative.Certificate.Bridges
