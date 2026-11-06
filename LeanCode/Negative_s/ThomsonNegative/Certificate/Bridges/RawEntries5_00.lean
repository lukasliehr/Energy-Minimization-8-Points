import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_5_00_00 : SparseEntry := [(0,3),(1,30),(2,-20),(3,-5),(4,-180),(5,300),(6,-120),(7,-100),(8,340),(9,20),(10,10),(11,-690),(12,510),(13,210),(14,-450),(15,96),(16,-300),(17,-40),(18,990),(19,30),(20,-510),(21,30),(22,-10),(23,-600),(24,540),(26,300),(31,-220),(32,130),(33,-240),(34,-120),(35,-140),(36,20),(37,100),(38,40),(39,-40),(40,5),(41,450),(42,150),(43,-450),(53,-45),(54,-4),(55,20),(56,70),(57,30),(58,-25),(59,-100),(60,-25),(61,50),(62,60),(63,-35),(64,-10),(65,10),(66,-1)]
theorem rawEntry_5_00_00_data : ∀r : Fin 102, RawData.coefficient 5 r.val 0 0=sparseCoefficient rawEntry_5_00_00 r := by decide +kernel
theorem rawEntry_5_00_00_coordinates : sparsePolynomial 3 rawEntry_5_00_00=termsCoordinates 0 0 qTerms5 := by
  norm_num only [qTerms5,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_5_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_5_00_00_physical : invariantSubst (rawCoordinate 5 0 0)=kernelRPolynomial 5 0 0 := by
  rw [rawCoordinate_sparse 5 0 0 rawEntry_5_00_00 rawEntry_5_00_00_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_5_00_00)=_
  rw [rawEntry_5_00_00_coordinates]
  simpa using (rawMoment_from_terms 5 0 0 qTerms5 qTerms5_eq)
def rawEntry_5_00_01 : SparseEntry := [(1,1),(2,30),(4,30),(6,-5),(7,180),(8,30),(9,-90),(11,430),(12,-10),(13,-40),(14,-20),(15,10),(16,441),(17,246),(18,-69),(19,-252),(20,-33),(21,63),(23,830),(24,155),(25,40),(26,-435),(27,-80),(28,-25),(29,55),(30,-10),(31,1440),(33,-300),(34,-450),(36,150),(41,825),(42,-105),(43,-105),(44,105),(45,120),(46,-60),(47,-180),(48,-135),(49,135),(50,45),(51,-45),(52,5),(53,-75),(55,375),(56,75),(57,-225),(67,23),(68,-8),(69,-93),(70,8),(71,-1),(72,125),(73,95),(74,-55),(75,-165),(76,-33),(77,77),(78,77),(79,-44),(80,-11),(81,11),(82,-1)]
theorem rawEntry_5_00_01_data : ∀r : Fin 102, RawData.coefficient 5 r.val 0 1=sparseCoefficient rawEntry_5_00_01 r := by decide +kernel
theorem rawEntry_5_00_01_coordinates : sparsePolynomial 3 rawEntry_5_00_01=termsCoordinates 0 1 qTerms5 := by
  norm_num only [qTerms5,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_5_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_5_00_01_physical : invariantSubst (rawCoordinate 5 0 1)=kernelRPolynomial 5 0 1 := by
  rw [rawCoordinate_sparse 5 0 1 rawEntry_5_00_01 rawEntry_5_00_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_5_00_01)=_
  rw [rawEntry_5_00_01_coordinates]
  simpa using (rawMoment_from_terms 5 0 1 qTerms5 qTerms5_eq)
theorem rawEntry_5_01_00_data : ∀r : Fin 102, RawData.coefficient 5 r.val 1 0=sparseCoefficient rawEntry_5_00_01 r := by decide +kernel
theorem rawEntry_5_01_00_physical : invariantSubst (rawCoordinate 5 1 0)=kernelRPolynomial 5 1 0 := by
  have hh : rawCoordinate 5 1 0=rawCoordinate 5 0 1 := by
    rw [rawCoordinate_sparse 5 1 0 rawEntry_5_00_01 rawEntry_5_01_00_data,rawCoordinate_sparse 5 0 1 rawEntry_5_00_01 rawEntry_5_00_01_data]
  rw [hh,rawEntry_5_00_01_physical]
  exact kernelRPolynomial_index_symm 5 0 1
def rawEntry_5_01_01 : SparseEntry := [(2,-2),(3,1),(4,90),(7,-40),(8,40),(9,20),(10,-5),(11,480),(13,-240),(16,930),(17,-140),(18,120),(19,150),(20,-60),(21,-60),(22,10),(23,312),(24,624),(26,-624),(28,156),(31,2420),(32,-80),(33,-240),(34,-1050),(35,280),(36,80),(37,-230),(38,-20),(39,80),(40,-10),(41,1620),(42,-600),(43,1200),(45,300),(46,-600),(53,15),(54,110),(55,1130),(56,-680),(57,-300),(58,65),(59,740),(60,5),(61,-250),(62,-300),(63,175),(64,50),(65,-50),(66,5),(67,600),(68,150),(69,-600),(71,300),(83,-21),(84,-12),(85,-8),(86,120),(87,-24),(88,-234),(89,36),(90,-28),(91,240),(92,180),(93,-105),(94,-252),(95,-42),(96,112),(97,96),(98,-54),(99,-12),(100,12),(101,-1)]
theorem rawEntry_5_01_01_data : ∀r : Fin 102, RawData.coefficient 5 r.val 1 1=sparseCoefficient rawEntry_5_01_01 r := by decide +kernel
theorem rawEntry_5_01_01_coordinates : sparsePolynomial 3 rawEntry_5_01_01=termsCoordinates 1 1 qTerms5 := by
  norm_num only [qTerms5,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_5_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_5_01_01_physical : invariantSubst (rawCoordinate 5 1 1)=kernelRPolynomial 5 1 1 := by
  rw [rawCoordinate_sparse 5 1 1 rawEntry_5_01_01 rawEntry_5_01_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_5_01_01)=_
  rw [rawEntry_5_01_01_coordinates]
  simpa using (rawMoment_from_terms 5 1 1 qTerms5 qTerms5_eq)
end ThomsonNegative.Certificate.Bridges
