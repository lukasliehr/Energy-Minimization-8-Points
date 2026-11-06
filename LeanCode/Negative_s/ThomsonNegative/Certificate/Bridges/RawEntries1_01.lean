import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_1_05_05 : SparseEntry := [(53,15),(54,-2),(55,10),(56,-40),(57,-60),(58,25),(59,100),(60,25),(61,-50),(62,-60),(63,35),(64,10),(65,-10),(66,1),(67,24),(68,6),(69,-24),(71,12),(83,-21),(84,-12),(85,-8),(86,120),(87,-24),(88,-234),(89,36),(90,-28),(91,240),(92,180),(93,-105),(94,-252),(95,-42),(96,112),(97,96),(98,-54),(99,-12),(100,12),(101,-1)]
theorem rawEntry_1_05_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 5=sparseCoefficient rawEntry_1_05_05 r := by decide +kernel
theorem rawEntry_1_05_05_coordinates : sparsePolynomial 3 rawEntry_1_05_05=termsCoordinates 5 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_05_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_05_05_physical : invariantSubst (rawCoordinate 1 5 5)=kernelRPolynomial 1 5 5 := by
  rw [rawCoordinate_sparse 1 5 5 rawEntry_1_05_05 rawEntry_1_05_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_05_05)=_
  rw [rawEntry_1_05_05_coordinates]
  simpa using (rawMoment_from_terms 1 5 5 qTerms1 qTerms1_eq)
end ThomsonNegative.Certificate.Bridges
