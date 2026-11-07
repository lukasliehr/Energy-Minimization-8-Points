import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_3_00_00 : SparseEntry := [(0,3),(1,-18),(2,24),(3,-3),(4,18),(5,-54),(6,24),(7,42),(8,-42),(9,-30),(10,3),(11,54),(16,-21),(17,-4),(18,30),(19,-9),(20,-6),(21,6),(22,-1)]
theorem rawEntry_3_00_00_data : ∀r : Fin 102, RawData.coefficient 3 r.val 0 0=sparseCoefficient rawEntry_3_00_00 r := by decide +kernel
theorem rawEntry_3_00_00_coordinates : sparsePolynomial 3 rawEntry_3_00_00=termsCoordinates 0 0 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_00_00_physical : invariantSubst (rawCoordinate 3 0 0)=kernelRPolynomial 3 0 0 := by
  rw [rawCoordinate_sparse 3 0 0 rawEntry_3_00_00 rawEntry_3_00_00_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_00_00)=_
  rw [rawEntry_3_00_00_coordinates]
  simpa using (rawMoment_from_terms 3 0 0 qTerms3 qTerms3_eq)
def rawEntry_3_00_01 : SparseEntry := [(1,1),(2,-18),(4,-36),(5,18),(6,-3),(7,-42),(8,-3),(9,21),(11,-123),(12,33),(13,42),(14,-24),(15,3),(16,-81),(18,27),(23,-4),(24,-22),(25,4),(26,30),(27,-14),(28,-7),(29,7),(30,-1)]
theorem rawEntry_3_00_01_data : ∀r : Fin 102, RawData.coefficient 3 r.val 0 1=sparseCoefficient rawEntry_3_00_01 r := by decide +kernel
theorem rawEntry_3_00_01_coordinates : sparsePolynomial 3 rawEntry_3_00_01=termsCoordinates 0 1 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_00_01_physical : invariantSubst (rawCoordinate 3 0 1)=kernelRPolynomial 3 0 1 := by
  rw [rawCoordinate_sparse 3 0 1 rawEntry_3_00_01 rawEntry_3_00_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_00_01)=_
  rw [rawEntry_3_00_01_coordinates]
  simpa using (rawMoment_from_terms 3 0 1 qTerms3 qTerms3_eq)
theorem rawEntry_3_01_00_data : ∀r : Fin 102, RawData.coefficient 3 r.val 1 0=sparseCoefficient rawEntry_3_00_01 r := by decide +kernel
theorem rawEntry_3_01_00_physical : invariantSubst (rawCoordinate 3 1 0)=kernelRPolynomial 3 1 0 := by
  have hh : rawCoordinate 3 1 0=rawCoordinate 3 0 1 := by
    rw [rawCoordinate_sparse 3 1 0 rawEntry_3_00_01 rawEntry_3_01_00_data,rawCoordinate_sparse 3 0 1 rawEntry_3_00_01 rawEntry_3_00_01_data]
  rw [hh,rawEntry_3_00_01_physical]
  exact kernelRPolynomial_index_symm 3 0 1
def rawEntry_3_00_02 : SparseEntry := [(2,-2),(3,1),(4,27),(5,-9),(7,-24),(8,-21),(9,21),(10,-3),(11,51),(12,-15),(13,-33),(14,9),(16,90),(17,-42),(18,-81),(19,63),(20,27),(21,-27),(22,3),(23,-54),(24,-27),(26,27),(31,29),(32,4),(33,-42),(34,-21),(35,13),(36,41),(37,-20),(38,-8),(39,8),(40,-1)]
theorem rawEntry_3_00_02_data : ∀r : Fin 102, RawData.coefficient 3 r.val 0 2=sparseCoefficient rawEntry_3_00_02 r := by decide +kernel
theorem rawEntry_3_00_02_coordinates : sparsePolynomial 3 rawEntry_3_00_02=termsCoordinates 0 2 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_00_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_00_02_physical : invariantSubst (rawCoordinate 3 0 2)=kernelRPolynomial 3 0 2 := by
  rw [rawCoordinate_sparse 3 0 2 rawEntry_3_00_02 rawEntry_3_00_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_00_02)=_
  rw [rawEntry_3_00_02_coordinates]
  simpa using (rawMoment_from_terms 3 0 2 qTerms3 qTerms3_eq)
theorem rawEntry_3_02_00_data : ∀r : Fin 102, RawData.coefficient 3 r.val 2 0=sparseCoefficient rawEntry_3_00_02 r := by decide +kernel
theorem rawEntry_3_02_00_physical : invariantSubst (rawCoordinate 3 2 0)=kernelRPolynomial 3 2 0 := by
  have hh : rawCoordinate 3 2 0=rawCoordinate 3 0 2 := by
    rw [rawCoordinate_sparse 3 2 0 rawEntry_3_00_02 rawEntry_3_02_00_data,rawCoordinate_sparse 3 0 2 rawEntry_3_00_02 rawEntry_3_00_02_data]
  rw [hh,rawEntry_3_00_02_physical]
  exact kernelRPolynomial_index_symm 3 0 2
def rawEntry_3_00_03 : SparseEntry := [(4,3),(5,-3),(6,1),(7,18),(8,9),(9,-9),(11,60),(12,-42),(13,-24),(14,24),(15,-3),(16,18),(17,42),(19,-36),(20,-9),(21,9),(23,165),(24,48),(25,-75),(26,-153),(27,87),(28,30),(29,-30),(30,3),(31,135),(33,-81),(34,-27),(36,27),(41,-21),(43,81),(45,-81),(46,-27),(47,27),(48,54),(49,-27),(50,-9),(51,9),(52,-1)]
theorem rawEntry_3_00_03_data : ∀r : Fin 102, RawData.coefficient 3 r.val 0 3=sparseCoefficient rawEntry_3_00_03 r := by decide +kernel
theorem rawEntry_3_00_03_coordinates : sparsePolynomial 3 rawEntry_3_00_03=termsCoordinates 0 3 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_00_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_00_03_physical : invariantSubst (rawCoordinate 3 0 3)=kernelRPolynomial 3 0 3 := by
  rw [rawCoordinate_sparse 3 0 3 rawEntry_3_00_03 rawEntry_3_00_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_00_03)=_
  rw [rawEntry_3_00_03_coordinates]
  simpa using (rawMoment_from_terms 3 0 3 qTerms3 qTerms3_eq)
theorem rawEntry_3_03_00_data : ∀r : Fin 102, RawData.coefficient 3 r.val 3 0=sparseCoefficient rawEntry_3_00_03 r := by decide +kernel
theorem rawEntry_3_03_00_physical : invariantSubst (rawCoordinate 3 3 0)=kernelRPolynomial 3 3 0 := by
  have hh : rawCoordinate 3 3 0=rawCoordinate 3 0 3 := by
    rw [rawCoordinate_sparse 3 3 0 rawEntry_3_00_03 rawEntry_3_03_00_data,rawCoordinate_sparse 3 0 3 rawEntry_3_00_03 rawEntry_3_00_03_data]
  rw [hh,rawEntry_3_00_03_physical]
  exact kernelRPolynomial_index_symm 3 0 3
def rawEntry_3_01_01 : SparseEntry := [(2,-2),(3,1),(4,-54),(7,12),(8,-48),(9,12),(10,-3),(11,-120),(13,60),(16,-153),(17,30),(18,-108),(19,9),(20,54),(21,-18),(22,3),(23,54),(24,-108),(31,-16),(32,-8),(34,-24),(35,16),(36,32),(37,-20),(38,-8),(39,8),(40,-1)]
theorem rawEntry_3_01_01_data : ∀r : Fin 102, RawData.coefficient 3 r.val 1 1=sparseCoefficient rawEntry_3_01_01 r := by decide +kernel
theorem rawEntry_3_01_01_coordinates : sparsePolynomial 3 rawEntry_3_01_01=termsCoordinates 1 1 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_01_01_physical : invariantSubst (rawCoordinate 3 1 1)=kernelRPolynomial 3 1 1 := by
  rw [rawCoordinate_sparse 3 1 1 rawEntry_3_01_01 rawEntry_3_01_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_01_01)=_
  rw [rawEntry_3_01_01_coordinates]
  simpa using (rawMoment_from_terms 3 1 1 qTerms3 qTerms3_eq)
def rawEntry_3_01_02 : SparseEntry := [(4,3),(5,-3),(6,1),(8,-18),(11,6),(12,-6),(13,-33),(14,15),(15,-3),(16,-9),(18,-33),(20,18),(23,3),(24,-33),(25,-3),(26,-90),(27,33),(28,39),(29,-21),(30,3),(31,-27),(33,27),(34,-54),(41,6),(42,12),(43,6),(44,-12),(45,-42),(46,-24),(47,30),(48,45),(49,-27),(50,-9),(51,9),(52,-1)]
theorem rawEntry_3_01_02_data : ∀r : Fin 102, RawData.coefficient 3 r.val 1 2=sparseCoefficient rawEntry_3_01_02 r := by decide +kernel
theorem rawEntry_3_01_02_coordinates : sparsePolynomial 3 rawEntry_3_01_02=termsCoordinates 1 2 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_01_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_01_02_physical : invariantSubst (rawCoordinate 3 1 2)=kernelRPolynomial 3 1 2 := by
  rw [rawCoordinate_sparse 3 1 2 rawEntry_3_01_02 rawEntry_3_01_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_01_02)=_
  rw [rawEntry_3_01_02_coordinates]
  simpa using (rawMoment_from_terms 3 1 2 qTerms3 qTerms3_eq)
theorem rawEntry_3_02_01_data : ∀r : Fin 102, RawData.coefficient 3 r.val 2 1=sparseCoefficient rawEntry_3_01_02 r := by decide +kernel
theorem rawEntry_3_02_01_physical : invariantSubst (rawCoordinate 3 2 1)=kernelRPolynomial 3 2 1 := by
  have hh : rawCoordinate 3 2 1=rawCoordinate 3 1 2 := by
    rw [rawCoordinate_sparse 3 2 1 rawEntry_3_01_02 rawEntry_3_02_01_data,rawCoordinate_sparse 3 1 2 rawEntry_3_01_02 rawEntry_3_01_02_data]
  rw [hh,rawEntry_3_01_02_physical]
  exact kernelRPolynomial_index_symm 3 1 2
def rawEntry_3_01_03 : SparseEntry := [(7,2),(8,4),(9,-4),(10,1),(11,36),(13,-18),(16,-36),(17,-12),(18,72),(19,-18),(20,-36),(21,18),(22,-3),(23,78),(24,-12),(26,-72),(28,18),(31,30),(32,-30),(33,144),(34,9),(35,-12),(36,-168),(37,51),(38,42),(39,-24),(40,3),(41,-81),(42,-54),(43,108),(45,27),(46,-54),(53,12),(54,8),(55,-16),(56,16),(57,60),(58,-28),(59,-88),(60,-31),(61,50),(62,60),(63,-35),(64,-10),(65,10),(66,-1)]
theorem rawEntry_3_01_03_data : ∀r : Fin 102, RawData.coefficient 3 r.val 1 3=sparseCoefficient rawEntry_3_01_03 r := by decide +kernel
theorem rawEntry_3_01_03_coordinates : sparsePolynomial 3 rawEntry_3_01_03=termsCoordinates 1 3 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_01_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_01_03_physical : invariantSubst (rawCoordinate 3 1 3)=kernelRPolynomial 3 1 3 := by
  rw [rawCoordinate_sparse 3 1 3 rawEntry_3_01_03 rawEntry_3_01_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_01_03)=_
  rw [rawEntry_3_01_03_coordinates]
  simpa using (rawMoment_from_terms 3 1 3 qTerms3 qTerms3_eq)
theorem rawEntry_3_03_01_data : ∀r : Fin 102, RawData.coefficient 3 r.val 3 1=sparseCoefficient rawEntry_3_01_03 r := by decide +kernel
theorem rawEntry_3_03_01_physical : invariantSubst (rawCoordinate 3 3 1)=kernelRPolynomial 3 3 1 := by
  have hh : rawCoordinate 3 3 1=rawCoordinate 3 1 3 := by
    rw [rawCoordinate_sparse 3 3 1 rawEntry_3_01_03 rawEntry_3_03_01_data,rawCoordinate_sparse 3 1 3 rawEntry_3_01_03 rawEntry_3_01_03_data]
  rw [hh,rawEntry_3_01_03_physical]
  exact kernelRPolynomial_index_symm 3 1 3
def rawEntry_3_02_02 : SparseEntry := [(7,2),(8,4),(9,-4),(10,1),(11,-18),(16,45),(17,24),(18,-18),(19,-27),(20,-18),(21,18),(22,-3),(23,-36),(24,6),(26,18),(31,30),(32,42),(33,-36),(34,-18),(35,-66),(36,-42),(37,60),(38,24),(39,-24),(40,3),(41,162),(42,54),(43,-162),(53,-45),(54,-4),(55,20),(56,70),(57,30),(58,-25),(59,-100),(60,-25),(61,50),(62,60),(63,-35),(64,-10),(65,10),(66,-1)]
theorem rawEntry_3_02_02_data : ∀r : Fin 102, RawData.coefficient 3 r.val 2 2=sparseCoefficient rawEntry_3_02_02 r := by decide +kernel
theorem rawEntry_3_02_02_coordinates : sparsePolynomial 3 rawEntry_3_02_02=termsCoordinates 2 2 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_02_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_02_02_physical : invariantSubst (rawCoordinate 3 2 2)=kernelRPolynomial 3 2 2 := by
  rw [rawCoordinate_sparse 3 2 2 rawEntry_3_02_02 rawEntry_3_02_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_02_02)=_
  rw [rawEntry_3_02_02_coordinates]
  simpa using (rawMoment_from_terms 3 2 2 qTerms3 qTerms3_eq)
def rawEntry_3_02_03 : SparseEntry := [(11,-5),(12,5),(13,5),(14,-5),(15,1),(16,27),(18,-9),(23,-30),(24,24),(25,30),(26,36),(27,-42),(28,-21),(29,21),(30,-3),(31,60),(33,-18),(34,-27),(36,9),(41,90),(42,-45),(43,-18),(44,45),(45,117),(46,9),(47,-99),(48,-108),(49,81),(50,27),(51,-27),(52,3),(53,-27),(55,135),(56,27),(57,-81),(67,23),(68,-8),(69,-93),(70,8),(71,-1),(72,125),(73,95),(74,-55),(75,-165),(76,-33),(77,77),(78,77),(79,-44),(80,-11),(81,11),(82,-1)]
theorem rawEntry_3_02_03_data : ∀r : Fin 102, RawData.coefficient 3 r.val 2 3=sparseCoefficient rawEntry_3_02_03 r := by decide +kernel
theorem rawEntry_3_02_03_coordinates : sparsePolynomial 3 rawEntry_3_02_03=termsCoordinates 2 3 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_02_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_02_03_physical : invariantSubst (rawCoordinate 3 2 3)=kernelRPolynomial 3 2 3 := by
  rw [rawCoordinate_sparse 3 2 3 rawEntry_3_02_03 rawEntry_3_02_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_02_03)=_
  rw [rawEntry_3_02_03_coordinates]
  simpa using (rawMoment_from_terms 3 2 3 qTerms3 qTerms3_eq)
theorem rawEntry_3_03_02_data : ∀r : Fin 102, RawData.coefficient 3 r.val 3 2=sparseCoefficient rawEntry_3_02_03 r := by decide +kernel
theorem rawEntry_3_03_02_physical : invariantSubst (rawCoordinate 3 3 2)=kernelRPolynomial 3 3 2 := by
  have hh : rawCoordinate 3 3 2=rawCoordinate 3 2 3 := by
    rw [rawCoordinate_sparse 3 3 2 rawEntry_3_02_03 rawEntry_3_03_02_data,rawCoordinate_sparse 3 2 3 rawEntry_3_02_03 rawEntry_3_02_03_data]
  rw [hh,rawEntry_3_02_03_physical]
  exact kernelRPolynomial_index_symm 3 2 3
def rawEntry_3_03_03 : SparseEntry := [(16,3),(17,-2),(18,-12),(19,9),(20,6),(21,-6),(22,1),(23,-18),(24,36),(31,96),(32,12),(33,-144),(35,48),(36,96),(37,-60),(38,-24),(39,24),(40,-3),(41,18),(42,-36),(43,72),(45,18),(46,-36),(53,135),(54,30),(55,138),(56,-264),(57,-180),(58,57),(59,372),(60,39),(61,-150),(62,-180),(63,105),(64,30),(65,-30),(66,3),(67,216),(68,54),(69,-216),(71,108),(83,-21),(84,-12),(85,-8),(86,120),(87,-24),(88,-234),(89,36),(90,-28),(91,240),(92,180),(93,-105),(94,-252),(95,-42),(96,112),(97,96),(98,-54),(99,-12),(100,12),(101,-1)]
theorem rawEntry_3_03_03_data : ∀r : Fin 102, RawData.coefficient 3 r.val 3 3=sparseCoefficient rawEntry_3_03_03 r := by decide +kernel
theorem rawEntry_3_03_03_coordinates : sparsePolynomial 3 rawEntry_3_03_03=termsCoordinates 3 3 qTerms3 := by
  norm_num only [qTerms3,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_3_03_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_3_03_03_physical : invariantSubst (rawCoordinate 3 3 3)=kernelRPolynomial 3 3 3 := by
  rw [rawCoordinate_sparse 3 3 3 rawEntry_3_03_03 rawEntry_3_03_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_3_03_03)=_
  rw [rawEntry_3_03_03_coordinates]
  simpa using (rawMoment_from_terms 3 3 3 qTerms3 qTerms3_eq)
end ThomsonNegative.Certificate.Bridges
