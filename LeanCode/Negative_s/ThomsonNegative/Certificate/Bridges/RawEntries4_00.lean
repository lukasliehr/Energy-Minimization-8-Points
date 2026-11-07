import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_4_00_00 : SparseEntry := [(0,21),(2,152),(3,-76),(4,288),(7,204),(8,120),(9,-264),(10,66),(11,768),(13,-384),(16,600),(17,-64),(18,192),(20,-96),(21,24),(22,-4),(23,-96),(24,192),(31,16),(32,8),(34,24),(35,-16),(36,-32),(37,20),(38,8),(39,-8),(40,1)]
theorem rawEntry_4_00_00_data : ∀r : Fin 102, RawData.coefficient 4 r.val 0 0=sparseCoefficient rawEntry_4_00_00 r := by decide +kernel
theorem rawEntry_4_00_00_coordinates : sparsePolynomial 3 rawEntry_4_00_00=termsCoordinates 0 0 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_00_00_physical : invariantSubst (rawCoordinate 4 0 0)=kernelRPolynomial 4 0 0 := by
  rw [rawCoordinate_sparse 4 0 0 rawEntry_4_00_00 rawEntry_4_00_00_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_00_00)=_
  rw [rawEntry_4_00_00_coordinates]
  simpa using (rawMoment_from_terms 4 0 0 qTerms4 qTerms4_eq)
def rawEntry_4_00_01 : SparseEntry := [(1,7),(4,42),(5,18),(6,-16),(8,96),(11,111),(12,-9),(13,9),(14,-33),(15,12),(16,144),(18,144),(20,-96),(23,8),(24,176),(25,-8),(26,138),(27,-38),(28,-64),(29,28),(30,-4),(31,48),(33,-48),(34,96),(41,-6),(42,-12),(43,-6),(44,12),(45,42),(46,24),(47,-30),(48,-45),(49,27),(50,9),(51,-9),(52,1)]
theorem rawEntry_4_00_01_data : ∀r : Fin 102, RawData.coefficient 4 r.val 0 1=sparseCoefficient rawEntry_4_00_01 r := by decide +kernel
theorem rawEntry_4_00_01_coordinates : sparsePolynomial 3 rawEntry_4_00_01=termsCoordinates 0 1 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_00_01_physical : invariantSubst (rawCoordinate 4 0 1)=kernelRPolynomial 4 0 1 := by
  rw [rawCoordinate_sparse 4 0 1 rawEntry_4_00_01 rawEntry_4_00_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_00_01)=_
  rw [rawEntry_4_00_01_coordinates]
  simpa using (rawMoment_from_terms 4 0 1 qTerms4 qTerms4_eq)
theorem rawEntry_4_01_00_data : ∀r : Fin 102, RawData.coefficient 4 r.val 1 0=sparseCoefficient rawEntry_4_00_01 r := by decide +kernel
theorem rawEntry_4_01_00_physical : invariantSubst (rawCoordinate 4 1 0)=kernelRPolynomial 4 1 0 := by
  have hh : rawCoordinate 4 1 0=rawCoordinate 4 0 1 := by
    rw [rawCoordinate_sparse 4 1 0 rawEntry_4_00_01 rawEntry_4_01_00_data,rawCoordinate_sparse 4 0 1 rawEntry_4_00_01 rawEntry_4_00_01_data]
  rw [hh,rawEntry_4_00_01_physical]
  exact kernelRPolynomial_index_symm 4 0 1
def rawEntry_4_00_02 : SparseEntry := [(2,-14),(3,7),(7,-92),(8,56),(9,64),(10,-16),(11,-192),(13,96),(16,63),(17,-102),(18,12),(19,147),(20,-6),(21,-72),(22,12),(23,-480),(24,192),(26,384),(28,-96),(31,-268),(32,64),(33,-240),(34,102),(35,-8),(36,272),(37,-62),(38,-68),(39,32),(40,-4),(41,144),(42,96),(43,-192),(45,-48),(46,96),(53,-12),(54,-8),(55,16),(56,-16),(57,-60),(58,28),(59,88),(60,31),(61,-50),(62,-60),(63,35),(64,10),(65,-10),(66,1)]
theorem rawEntry_4_00_02_data : ∀r : Fin 102, RawData.coefficient 4 r.val 0 2=sparseCoefficient rawEntry_4_00_02 r := by decide +kernel
theorem rawEntry_4_00_02_coordinates : sparsePolynomial 3 rawEntry_4_00_02=termsCoordinates 0 2 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_00_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_00_02_physical : invariantSubst (rawCoordinate 4 0 2)=kernelRPolynomial 4 0 2 := by
  rw [rawCoordinate_sparse 4 0 2 rawEntry_4_00_02 rawEntry_4_00_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_00_02)=_
  rw [rawEntry_4_00_02_coordinates]
  simpa using (rawMoment_from_terms 4 0 2 qTerms4 qTerms4_eq)
theorem rawEntry_4_02_00_data : ∀r : Fin 102, RawData.coefficient 4 r.val 2 0=sparseCoefficient rawEntry_4_00_02 r := by decide +kernel
theorem rawEntry_4_02_00_physical : invariantSubst (rawCoordinate 4 2 0)=kernelRPolynomial 4 2 0 := by
  have hh : rawCoordinate 4 2 0=rawCoordinate 4 0 2 := by
    rw [rawCoordinate_sparse 4 2 0 rawEntry_4_00_02 rawEntry_4_02_00_data,rawCoordinate_sparse 4 0 2 rawEntry_4_00_02 rawEntry_4_00_02_data]
  rw [hh,rawEntry_4_00_02_physical]
  exact kernelRPolynomial_index_symm 4 0 2
def rawEntry_4_01_01 : SparseEntry := [(2,4),(3,1),(7,16),(8,-52),(9,4),(10,-4),(11,96),(16,-72),(17,-24),(18,-54),(19,30),(20,78),(21,-30),(22,6),(23,192),(24,-96),(26,-96),(31,20),(32,-80),(33,120),(34,60),(35,100),(36,20),(37,-80),(38,-32),(39,32),(40,-4),(41,-288),(42,-96),(43,288),(53,45),(54,4),(55,-20),(56,-70),(57,-30),(58,25),(59,100),(60,25),(61,-50),(62,-60),(63,35),(64,10),(65,-10),(66,1)]
theorem rawEntry_4_01_01_data : ∀r : Fin 102, RawData.coefficient 4 r.val 1 1=sparseCoefficient rawEntry_4_01_01 r := by decide +kernel
theorem rawEntry_4_01_01_coordinates : sparsePolynomial 3 rawEntry_4_01_01=termsCoordinates 1 1 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_01_01_physical : invariantSubst (rawCoordinate 4 1 1)=kernelRPolynomial 4 1 1 := by
  rw [rawCoordinate_sparse 4 1 1 rawEntry_4_01_01 rawEntry_4_01_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_01_01)=_
  rw [rawEntry_4_01_01_coordinates]
  simpa using (rawMoment_from_terms 4 1 1 qTerms4 qTerms4_eq)
def rawEntry_4_01_02 : SparseEntry := [(4,-6),(6,1),(11,-52),(12,-8),(13,-2),(14,14),(15,-4),(16,-144),(18,48),(23,-54),(24,-51),(25,-48),(26,3),(27,72),(28,33),(29,-39),(30,6),(31,-384),(33,96),(34,144),(36,-48),(41,-318),(42,72),(43,30),(44,-72),(45,-126),(46,18),(47,138),(48,126),(49,-108),(50,-36),(51,36),(52,-4),(53,48),(55,-240),(56,-48),(57,144),(67,-23),(68,8),(69,93),(70,-8),(71,1),(72,-125),(73,-95),(74,55),(75,165),(76,33),(77,-77),(78,-77),(79,44),(80,11),(81,-11),(82,1)]
theorem rawEntry_4_01_02_data : ∀r : Fin 102, RawData.coefficient 4 r.val 1 2=sparseCoefficient rawEntry_4_01_02 r := by decide +kernel
theorem rawEntry_4_01_02_coordinates : sparsePolynomial 3 rawEntry_4_01_02=termsCoordinates 1 2 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_01_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_01_02_physical : invariantSubst (rawCoordinate 4 1 2)=kernelRPolynomial 4 1 2 := by
  rw [rawCoordinate_sparse 4 1 2 rawEntry_4_01_02 rawEntry_4_01_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_01_02)=_
  rw [rawEntry_4_01_02_coordinates]
  simpa using (rawMoment_from_terms 4 1 2 qTerms4 qTerms4_eq)
theorem rawEntry_4_02_01_data : ∀r : Fin 102, RawData.coefficient 4 r.val 2 1=sparseCoefficient rawEntry_4_01_02 r := by decide +kernel
theorem rawEntry_4_02_01_physical : invariantSubst (rawCoordinate 4 2 1)=kernelRPolynomial 4 2 1 := by
  have hh : rawCoordinate 4 2 1=rawCoordinate 4 1 2 := by
    rw [rawCoordinate_sparse 4 2 1 rawEntry_4_01_02 rawEntry_4_02_01_data,rawCoordinate_sparse 4 1 2 rawEntry_4_01_02 rawEntry_4_01_02_data]
  rw [hh,rawEntry_4_01_02_physical]
  exact kernelRPolynomial_index_symm 4 1 2
def rawEntry_4_02_02 : SparseEntry := [(7,8),(8,-8),(9,-4),(10,1),(16,-120),(17,32),(19,-48),(21,24),(22,-4),(23,96),(24,-192),(31,-420),(33,240),(34,114),(35,-120),(36,-144),(37,126),(38,36),(39,-48),(40,6),(41,-288),(42,192),(43,-384),(45,-96),(46,192),(53,-144),(54,-64),(55,-448),(56,448),(57,240),(58,-64),(59,-544),(60,-28),(61,200),(62,240),(63,-140),(64,-40),(65,40),(66,-4),(67,-384),(68,-96),(69,384),(71,-192),(83,21),(84,12),(85,8),(86,-120),(87,24),(88,234),(89,-36),(90,28),(91,-240),(92,-180),(93,105),(94,252),(95,42),(96,-112),(97,-96),(98,54),(99,12),(100,-12),(101,1)]
theorem rawEntry_4_02_02_data : ∀r : Fin 102, RawData.coefficient 4 r.val 2 2=sparseCoefficient rawEntry_4_02_02 r := by decide +kernel
theorem rawEntry_4_02_02_coordinates : sparsePolynomial 3 rawEntry_4_02_02=termsCoordinates 2 2 qTerms4 := by
  norm_num only [qTerms4,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_4_02_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_4_02_02_physical : invariantSubst (rawCoordinate 4 2 2)=kernelRPolynomial 4 2 2 := by
  rw [rawCoordinate_sparse 4 2 2 rawEntry_4_02_02 rawEntry_4_02_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_4_02_02)=_
  rw [rawEntry_4_02_02_coordinates]
  simpa using (rawMoment_from_terms 4 2 2 qTerms4 qTerms4_eq)
end ThomsonNegative.Certificate.Bridges
