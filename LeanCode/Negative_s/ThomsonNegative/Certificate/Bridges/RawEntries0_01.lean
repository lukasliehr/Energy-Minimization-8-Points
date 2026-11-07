import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_0_03_05 : SparseEntry := [(0,3),(4,21),(5,-21),(6,7),(11,-35),(12,35),(13,35),(14,-35),(15,7),(31,-203),(32,-28),(33,294),(34,147),(35,-91),(36,-287),(37,140),(38,56),(39,-56),(40,7)]
theorem rawEntry_0_03_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 5=sparseCoefficient rawEntry_0_03_05 r := by decide +kernel
theorem rawEntry_0_03_05_coordinates : sparsePolynomial 21 rawEntry_0_03_05=r0Coordinates 3 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_03_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_03_05_physical : invariantSubst (rawCoordinate 0 3 5)=kernelRPolynomial 0 3 5 := by
  rw [rawCoordinate_sparse 0 3 5 rawEntry_0_03_05 rawEntry_0_03_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_03_05)=_
  rw [rawEntry_0_03_05_coordinates]
  exact r0Coordinates_subst 3 5
theorem rawEntry_0_05_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 3=sparseCoefficient rawEntry_0_03_05 r := by decide +kernel
theorem rawEntry_0_05_03_physical : invariantSubst (rawCoordinate 0 5 3)=kernelRPolynomial 0 5 3 := by
  have hh : rawCoordinate 0 5 3=rawCoordinate 0 3 5 := by
    rw [rawCoordinate_sparse 0 5 3 rawEntry_0_03_05 rawEntry_0_05_03_data,rawCoordinate_sparse 0 3 5 rawEntry_0_03_05 rawEntry_0_03_05_data]
  rw [hh,rawEntry_0_03_05_physical]
  exact kernelRPolynomial_index_symm 0 3 5
def rawEntry_0_03_06 : SparseEntry := [(0,3),(4,21),(5,-21),(6,7),(16,21),(17,-14),(18,-84),(19,63),(20,42),(21,-42),(22,7),(41,147),(43,-567),(45,567),(46,189),(47,-189),(48,-378),(49,189),(50,63),(51,-63),(52,7)]
theorem rawEntry_0_03_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 6=sparseCoefficient rawEntry_0_03_06 r := by decide +kernel
theorem rawEntry_0_03_06_coordinates : sparsePolynomial 21 rawEntry_0_03_06=r0Coordinates 3 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_03_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_03_06_physical : invariantSubst (rawCoordinate 0 3 6)=kernelRPolynomial 0 3 6 := by
  rw [rawCoordinate_sparse 0 3 6 rawEntry_0_03_06 rawEntry_0_03_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_03_06)=_
  rw [rawEntry_0_03_06_coordinates]
  exact r0Coordinates_subst 3 6
theorem rawEntry_0_06_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 3=sparseCoefficient rawEntry_0_03_06 r := by decide +kernel
theorem rawEntry_0_06_03_physical : invariantSubst (rawCoordinate 0 6 3)=kernelRPolynomial 0 6 3 := by
  have hh : rawCoordinate 0 6 3=rawCoordinate 0 3 6 := by
    rw [rawCoordinate_sparse 0 6 3 rawEntry_0_03_06 rawEntry_0_06_03_data,rawCoordinate_sparse 0 3 6 rawEntry_0_03_06 rawEntry_0_03_06_data]
  rw [hh,rawEntry_0_03_06_physical]
  exact kernelRPolynomial_index_symm 0 3 6
def rawEntry_0_04_04 : SparseEntry := [(0,3),(7,28),(8,56),(9,-56),(10,14),(31,112),(32,56),(34,168),(35,-112),(36,-224),(37,140),(38,56),(39,-56),(40,7)]
theorem rawEntry_0_04_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 4=sparseCoefficient rawEntry_0_04_04 r := by decide +kernel
theorem rawEntry_0_04_04_coordinates : sparsePolynomial 21 rawEntry_0_04_04=r0Coordinates 4 4 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_04_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_04_04_physical : invariantSubst (rawCoordinate 0 4 4)=kernelRPolynomial 0 4 4 := by
  rw [rawCoordinate_sparse 0 4 4 rawEntry_0_04_04 rawEntry_0_04_04_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_04_04)=_
  rw [rawEntry_0_04_04_coordinates]
  exact r0Coordinates_subst 4 4
def rawEntry_0_04_05 : SparseEntry := [(0,3),(7,14),(8,28),(9,-28),(10,7),(11,-35),(12,35),(13,35),(14,-35),(15,7),(41,-42),(42,-84),(43,-42),(44,84),(45,294),(46,168),(47,-210),(48,-315),(49,189),(50,63),(51,-63),(52,7)]
theorem rawEntry_0_04_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 5=sparseCoefficient rawEntry_0_04_05 r := by decide +kernel
theorem rawEntry_0_04_05_coordinates : sparsePolynomial 21 rawEntry_0_04_05=r0Coordinates 4 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_04_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_04_05_physical : invariantSubst (rawCoordinate 0 4 5)=kernelRPolynomial 0 4 5 := by
  rw [rawCoordinate_sparse 0 4 5 rawEntry_0_04_05 rawEntry_0_04_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_04_05)=_
  rw [rawEntry_0_04_05_coordinates]
  exact r0Coordinates_subst 4 5
theorem rawEntry_0_05_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 4=sparseCoefficient rawEntry_0_04_05 r := by decide +kernel
theorem rawEntry_0_05_04_physical : invariantSubst (rawCoordinate 0 5 4)=kernelRPolynomial 0 5 4 := by
  have hh : rawCoordinate 0 5 4=rawCoordinate 0 4 5 := by
    rw [rawCoordinate_sparse 0 5 4 rawEntry_0_04_05 rawEntry_0_05_04_data,rawCoordinate_sparse 0 4 5 rawEntry_0_04_05 rawEntry_0_04_05_data]
  rw [hh,rawEntry_0_04_05_physical]
  exact kernelRPolynomial_index_symm 0 4 5
def rawEntry_0_04_06 : SparseEntry := [(0,3),(7,14),(8,28),(9,-28),(10,7),(16,21),(17,-14),(18,-84),(19,63),(20,42),(21,-42),(22,7),(53,-84),(54,-56),(55,112),(56,-112),(57,-420),(58,196),(59,616),(60,217),(61,-350),(62,-420),(63,245),(64,70),(65,-70),(66,7)]
theorem rawEntry_0_04_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 6=sparseCoefficient rawEntry_0_04_06 r := by decide +kernel
theorem rawEntry_0_04_06_coordinates : sparsePolynomial 21 rawEntry_0_04_06=r0Coordinates 4 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_04_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_04_06_physical : invariantSubst (rawCoordinate 0 4 6)=kernelRPolynomial 0 4 6 := by
  rw [rawCoordinate_sparse 0 4 6 rawEntry_0_04_06 rawEntry_0_04_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_04_06)=_
  rw [rawEntry_0_04_06_coordinates]
  exact r0Coordinates_subst 4 6
theorem rawEntry_0_06_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 4=sparseCoefficient rawEntry_0_04_06 r := by decide +kernel
theorem rawEntry_0_06_04_physical : invariantSubst (rawCoordinate 0 6 4)=kernelRPolynomial 0 6 4 := by
  have hh : rawCoordinate 0 6 4=rawCoordinate 0 4 6 := by
    rw [rawCoordinate_sparse 0 6 4 rawEntry_0_04_06 rawEntry_0_06_04_data,rawCoordinate_sparse 0 4 6 rawEntry_0_04_06 rawEntry_0_04_06_data]
  rw [hh,rawEntry_0_04_06_physical]
  exact kernelRPolynomial_index_symm 0 4 6
def rawEntry_0_05_05 : SparseEntry := [(0,3),(11,-70),(12,70),(13,70),(14,-70),(15,14),(53,315),(54,28),(55,-140),(56,-490),(57,-210),(58,175),(59,700),(60,175),(61,-350),(62,-420),(63,245),(64,70),(65,-70),(66,7)]
theorem rawEntry_0_05_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 5=sparseCoefficient rawEntry_0_05_05 r := by decide +kernel
theorem rawEntry_0_05_05_coordinates : sparsePolynomial 21 rawEntry_0_05_05=r0Coordinates 5 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_05_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_05_05_physical : invariantSubst (rawCoordinate 0 5 5)=kernelRPolynomial 0 5 5 := by
  rw [rawCoordinate_sparse 0 5 5 rawEntry_0_05_05 rawEntry_0_05_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_05_05)=_
  rw [rawEntry_0_05_05_coordinates]
  exact r0Coordinates_subst 5 5
def rawEntry_0_05_06 : SparseEntry := [(0,3),(11,-35),(12,35),(13,35),(14,-35),(15,7),(16,21),(17,-14),(18,-84),(19,63),(20,42),(21,-42),(22,7),(67,-161),(68,56),(69,651),(70,-56),(71,7),(72,-875),(73,-665),(74,385),(75,1155),(76,231),(77,-539),(78,-539),(79,308),(80,77),(81,-77),(82,7)]
theorem rawEntry_0_05_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 6=sparseCoefficient rawEntry_0_05_06 r := by decide +kernel
theorem rawEntry_0_05_06_coordinates : sparsePolynomial 21 rawEntry_0_05_06=r0Coordinates 5 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_05_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_05_06_physical : invariantSubst (rawCoordinate 0 5 6)=kernelRPolynomial 0 5 6 := by
  rw [rawCoordinate_sparse 0 5 6 rawEntry_0_05_06 rawEntry_0_05_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_05_06)=_
  rw [rawEntry_0_05_06_coordinates]
  exact r0Coordinates_subst 5 6
theorem rawEntry_0_06_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 5=sparseCoefficient rawEntry_0_05_06 r := by decide +kernel
theorem rawEntry_0_06_05_physical : invariantSubst (rawCoordinate 0 6 5)=kernelRPolynomial 0 6 5 := by
  have hh : rawCoordinate 0 6 5=rawCoordinate 0 5 6 := by
    rw [rawCoordinate_sparse 0 6 5 rawEntry_0_05_06 rawEntry_0_06_05_data,rawCoordinate_sparse 0 5 6 rawEntry_0_05_06 rawEntry_0_05_06_data]
  rw [hh,rawEntry_0_05_06_physical]
  exact kernelRPolynomial_index_symm 0 5 6
def rawEntry_0_06_06 : SparseEntry := [(0,3),(16,42),(17,-28),(18,-168),(19,126),(20,84),(21,-84),(22,14),(83,147),(84,84),(85,56),(86,-840),(87,168),(88,1638),(89,-252),(90,196),(91,-1680),(92,-1260),(93,735),(94,1764),(95,294),(96,-784),(97,-672),(98,378),(99,84),(100,-84),(101,7)]
theorem rawEntry_0_06_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 6=sparseCoefficient rawEntry_0_06_06 r := by decide +kernel
theorem rawEntry_0_06_06_coordinates : sparsePolynomial 21 rawEntry_0_06_06=r0Coordinates 6 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_06_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_06_06_physical : invariantSubst (rawCoordinate 0 6 6)=kernelRPolynomial 0 6 6 := by
  rw [rawCoordinate_sparse 0 6 6 rawEntry_0_06_06 rawEntry_0_06_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_06_06)=_
  rw [rawEntry_0_06_06_coordinates]
  exact r0Coordinates_subst 6 6
end ThomsonNegative.Certificate.Bridges
