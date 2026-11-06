import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_2_00_00 : SparseEntry := [(0,-15),(2,-44),(3,22),(4,-72),(7,8),(8,-8),(9,-4),(10,1)]
theorem rawEntry_2_00_00_data : ∀r : Fin 102, RawData.coefficient 2 r.val 0 0=sparseCoefficient rawEntry_2_00_00 r := by decide +kernel
theorem rawEntry_2_00_00_coordinates : sparsePolynomial 3 rawEntry_2_00_00=termsCoordinates 0 0 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_00_00_physical : invariantSubst (rawCoordinate 2 0 0)=kernelRPolynomial 2 0 0 := by
  rw [rawCoordinate_sparse 2 0 0 rawEntry_2_00_00 rawEntry_2_00_00_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_00_00)=_
  rw [rawEntry_2_00_00_coordinates]
  simpa using (rawMoment_from_terms 2 0 0 qTerms2 qTerms2_eq)
def rawEntry_2_00_01 : SparseEntry := [(1,-5),(4,-15),(5,-3),(6,4),(8,-24),(11,-8),(12,8),(13,-1),(14,-5),(15,1)]
theorem rawEntry_2_00_01_data : ∀r : Fin 102, RawData.coefficient 2 r.val 0 1=sparseCoefficient rawEntry_2_00_01 r := by decide +kernel
theorem rawEntry_2_00_01_coordinates : sparsePolynomial 3 rawEntry_2_00_01=termsCoordinates 0 1 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_00_01_physical : invariantSubst (rawCoordinate 2 0 1)=kernelRPolynomial 2 0 1 := by
  rw [rawCoordinate_sparse 2 0 1 rawEntry_2_00_01 rawEntry_2_00_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_00_01)=_
  rw [rawEntry_2_00_01_coordinates]
  simpa using (rawMoment_from_terms 2 0 1 qTerms2 qTerms2_eq)
theorem rawEntry_2_01_00_data : ∀r : Fin 102, RawData.coefficient 2 r.val 1 0=sparseCoefficient rawEntry_2_00_01 r := by decide +kernel
theorem rawEntry_2_01_00_physical : invariantSubst (rawCoordinate 2 1 0)=kernelRPolynomial 2 1 0 := by
  have hh : rawCoordinate 2 1 0=rawCoordinate 2 0 1 := by
    rw [rawCoordinate_sparse 2 1 0 rawEntry_2_00_01 rawEntry_2_01_00_data,rawCoordinate_sparse 2 0 1 rawEntry_2_00_01 rawEntry_2_00_01_data]
  rw [hh,rawEntry_2_00_01_physical]
  exact kernelRPolynomial_index_symm 2 0 1
def rawEntry_2_00_02 : SparseEntry := [(2,10),(3,-5),(7,26),(8,-20),(9,-16),(10,4),(11,48),(13,-24),(16,-6),(17,-8),(19,12),(21,-6),(22,1)]
theorem rawEntry_2_00_02_data : ∀r : Fin 102, RawData.coefficient 2 r.val 0 2=sparseCoefficient rawEntry_2_00_02 r := by decide +kernel
theorem rawEntry_2_00_02_coordinates : sparsePolynomial 3 rawEntry_2_00_02=termsCoordinates 0 2 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_00_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_00_02_physical : invariantSubst (rawCoordinate 2 0 2)=kernelRPolynomial 2 0 2 := by
  rw [rawCoordinate_sparse 2 0 2 rawEntry_2_00_02 rawEntry_2_00_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_00_02)=_
  rw [rawEntry_2_00_02_coordinates]
  simpa using (rawMoment_from_terms 2 0 2 qTerms2 qTerms2_eq)
theorem rawEntry_2_02_00_data : ∀r : Fin 102, RawData.coefficient 2 r.val 2 0=sparseCoefficient rawEntry_2_00_02 r := by decide +kernel
theorem rawEntry_2_02_00_physical : invariantSubst (rawCoordinate 2 2 0)=kernelRPolynomial 2 2 0 := by
  have hh : rawCoordinate 2 2 0=rawCoordinate 2 0 2 := by
    rw [rawCoordinate_sparse 2 2 0 rawEntry_2_00_02 rawEntry_2_02_00_data,rawCoordinate_sparse 2 0 2 rawEntry_2_00_02 rawEntry_2_00_02_data]
  rw [hh,rawEntry_2_00_02_physical]
  exact kernelRPolynomial_index_symm 2 0 2
def rawEntry_2_00_03 : SparseEntry := [(4,-15),(5,15),(6,-5),(11,-29),(12,29),(13,2),(14,-20),(15,4),(16,-72),(18,72),(20,-24),(23,16),(24,-14),(25,-16),(26,-3),(27,17),(28,1),(29,-7),(30,1)]
theorem rawEntry_2_00_03_data : ∀r : Fin 102, RawData.coefficient 2 r.val 0 3=sparseCoefficient rawEntry_2_00_03 r := by decide +kernel
theorem rawEntry_2_00_03_coordinates : sparsePolynomial 3 rawEntry_2_00_03=termsCoordinates 0 3 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_00_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_00_03_physical : invariantSubst (rawCoordinate 2 0 3)=kernelRPolynomial 2 0 3 := by
  rw [rawCoordinate_sparse 2 0 3 rawEntry_2_00_03 rawEntry_2_00_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_00_03)=_
  rw [rawEntry_2_00_03_coordinates]
  simpa using (rawMoment_from_terms 2 0 3 qTerms2 qTerms2_eq)
theorem rawEntry_2_03_00_data : ∀r : Fin 102, RawData.coefficient 2 r.val 3 0=sparseCoefficient rawEntry_2_00_03 r := by decide +kernel
theorem rawEntry_2_03_00_physical : invariantSubst (rawCoordinate 2 3 0)=kernelRPolynomial 2 3 0 := by
  have hh : rawCoordinate 2 3 0=rawCoordinate 2 0 3 := by
    rw [rawCoordinate_sparse 2 3 0 rawEntry_2_00_03 rawEntry_2_03_00_data,rawCoordinate_sparse 2 0 3 rawEntry_2_00_03 rawEntry_2_00_03_data]
  rw [hh,rawEntry_2_00_03_physical]
  exact kernelRPolynomial_index_symm 2 0 3
def rawEntry_2_00_04 : SparseEntry := [(7,-10),(8,-20),(9,20),(10,-5),(16,-15),(17,-26),(18,-12),(19,45),(20,6),(21,-24),(22,4),(23,-48),(24,-96),(26,96),(28,-24),(31,-2),(32,8),(33,24),(34,-15),(35,-28),(36,-8),(37,23),(38,2),(39,-8),(40,1)]
theorem rawEntry_2_00_04_data : ∀r : Fin 102, RawData.coefficient 2 r.val 0 4=sparseCoefficient rawEntry_2_00_04 r := by decide +kernel
theorem rawEntry_2_00_04_coordinates : sparsePolynomial 3 rawEntry_2_00_04=termsCoordinates 0 4 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_00_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_00_04_physical : invariantSubst (rawCoordinate 2 0 4)=kernelRPolynomial 2 0 4 := by
  rw [rawCoordinate_sparse 2 0 4 rawEntry_2_00_04 rawEntry_2_00_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_00_04)=_
  rw [rawEntry_2_00_04_coordinates]
  simpa using (rawMoment_from_terms 2 0 4 qTerms2 qTerms2_eq)
theorem rawEntry_2_04_00_data : ∀r : Fin 102, RawData.coefficient 2 r.val 4 0=sparseCoefficient rawEntry_2_00_04 r := by decide +kernel
theorem rawEntry_2_04_00_physical : invariantSubst (rawCoordinate 2 4 0)=kernelRPolynomial 2 4 0 := by
  have hh : rawCoordinate 2 4 0=rawCoordinate 2 0 4 := by
    rw [rawCoordinate_sparse 2 4 0 rawEntry_2_00_04 rawEntry_2_04_00_data,rawCoordinate_sparse 2 0 4 rawEntry_2_00_04 rawEntry_2_00_04_data]
  rw [hh,rawEntry_2_00_04_physical]
  exact kernelRPolynomial_index_symm 2 0 4
def rawEntry_2_01_01 : SparseEntry := [(2,-8),(3,1),(7,-16),(8,-2),(9,14),(10,-2),(11,-24),(16,21),(17,4),(18,-30),(19,9),(20,6),(21,-6),(22,1)]
theorem rawEntry_2_01_01_data : ∀r : Fin 102, RawData.coefficient 2 r.val 1 1=sparseCoefficient rawEntry_2_01_01 r := by decide +kernel
theorem rawEntry_2_01_01_coordinates : sparsePolynomial 3 rawEntry_2_01_01=termsCoordinates 1 1 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_01_01_physical : invariantSubst (rawCoordinate 2 1 1)=kernelRPolynomial 2 1 1 := by
  rw [rawCoordinate_sparse 2 1 1 rawEntry_2_01_01 rawEntry_2_01_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_01_01)=_
  rw [rawEntry_2_01_01_coordinates]
  simpa using (rawMoment_from_terms 2 1 1 qTerms2 qTerms2_eq)
def rawEntry_2_01_02 : SparseEntry := [(4,12),(5,-6),(6,1),(11,34),(12,-16),(13,-19),(14,13),(15,-2),(16,36),(18,-12),(23,4),(24,22),(25,-4),(26,-30),(27,14),(28,7),(29,-7),(30,1)]
theorem rawEntry_2_01_02_data : ∀r : Fin 102, RawData.coefficient 2 r.val 1 2=sparseCoefficient rawEntry_2_01_02 r := by decide +kernel
theorem rawEntry_2_01_02_coordinates : sparsePolynomial 3 rawEntry_2_01_02=termsCoordinates 1 2 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_01_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_01_02_physical : invariantSubst (rawCoordinate 2 1 2)=kernelRPolynomial 2 1 2 := by
  rw [rawCoordinate_sparse 2 1 2 rawEntry_2_01_02 rawEntry_2_01_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_01_02)=_
  rw [rawEntry_2_01_02_coordinates]
  simpa using (rawMoment_from_terms 2 1 2 qTerms2 qTerms2_eq)
theorem rawEntry_2_02_01_data : ∀r : Fin 102, RawData.coefficient 2 r.val 2 1=sparseCoefficient rawEntry_2_01_02 r := by decide +kernel
theorem rawEntry_2_02_01_physical : invariantSubst (rawCoordinate 2 2 1)=kernelRPolynomial 2 2 1 := by
  have hh : rawCoordinate 2 2 1=rawCoordinate 2 1 2 := by
    rw [rawCoordinate_sparse 2 2 1 rawEntry_2_01_02 rawEntry_2_02_01_data,rawCoordinate_sparse 2 1 2 rawEntry_2_01_02 rawEntry_2_01_02_data]
  rw [hh,rawEntry_2_01_02_physical]
  exact kernelRPolynomial_index_symm 2 1 2
def rawEntry_2_01_03 : SparseEntry := [(7,8),(8,7),(9,-7),(10,1),(16,-15),(17,16),(18,33),(19,-30),(20,-15),(21,15),(22,-2),(23,24),(24,12),(26,-12),(31,-29),(32,-4),(33,42),(34,21),(35,-13),(36,-41),(37,20),(38,8),(39,-8),(40,1)]
theorem rawEntry_2_01_03_data : ∀r : Fin 102, RawData.coefficient 2 r.val 1 3=sparseCoefficient rawEntry_2_01_03 r := by decide +kernel
theorem rawEntry_2_01_03_coordinates : sparsePolynomial 3 rawEntry_2_01_03=termsCoordinates 1 3 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_01_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_01_03_physical : invariantSubst (rawCoordinate 2 1 3)=kernelRPolynomial 2 1 3 := by
  rw [rawCoordinate_sparse 2 1 3 rawEntry_2_01_03 rawEntry_2_01_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_01_03)=_
  rw [rawEntry_2_01_03_coordinates]
  simpa using (rawMoment_from_terms 2 1 3 qTerms2 qTerms2_eq)
theorem rawEntry_2_03_01_data : ∀r : Fin 102, RawData.coefficient 2 r.val 3 1=sparseCoefficient rawEntry_2_01_03 r := by decide +kernel
theorem rawEntry_2_03_01_physical : invariantSubst (rawCoordinate 2 3 1)=kernelRPolynomial 2 3 1 := by
  have hh : rawCoordinate 2 3 1=rawCoordinate 2 1 3 := by
    rw [rawCoordinate_sparse 2 3 1 rawEntry_2_01_03 rawEntry_2_03_01_data,rawCoordinate_sparse 2 1 3 rawEntry_2_01_03 rawEntry_2_01_03_data]
  rw [hh,rawEntry_2_01_03_physical]
  exact kernelRPolynomial_index_symm 2 1 3
def rawEntry_2_01_04 : SparseEntry := [(11,-20),(12,14),(13,8),(14,-8),(15,1),(23,-50),(24,-17),(25,32),(26,66),(27,-43),(28,-17),(29,17),(30,-2),(31,-60),(33,36),(34,12),(36,-12),(41,21),(43,-81),(45,81),(46,27),(47,-27),(48,-54),(49,27),(50,9),(51,-9),(52,1)]
theorem rawEntry_2_01_04_data : ∀r : Fin 102, RawData.coefficient 2 r.val 1 4=sparseCoefficient rawEntry_2_01_04 r := by decide +kernel
theorem rawEntry_2_01_04_coordinates : sparsePolynomial 3 rawEntry_2_01_04=termsCoordinates 1 4 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_01_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_01_04_physical : invariantSubst (rawCoordinate 2 1 4)=kernelRPolynomial 2 1 4 := by
  rw [rawCoordinate_sparse 2 1 4 rawEntry_2_01_04 rawEntry_2_01_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_01_04)=_
  rw [rawEntry_2_01_04_coordinates]
  simpa using (rawMoment_from_terms 2 1 4 qTerms2 qTerms2_eq)
theorem rawEntry_2_04_01_data : ∀r : Fin 102, RawData.coefficient 2 r.val 4 1=sparseCoefficient rawEntry_2_01_04 r := by decide +kernel
theorem rawEntry_2_04_01_physical : invariantSubst (rawCoordinate 2 4 1)=kernelRPolynomial 2 4 1 := by
  have hh : rawCoordinate 2 4 1=rawCoordinate 2 1 4 := by
    rw [rawCoordinate_sparse 2 4 1 rawEntry_2_01_04 rawEntry_2_04_01_data,rawCoordinate_sparse 2 1 4 rawEntry_2_01_04 rawEntry_2_01_04_data]
  rw [hh,rawEntry_2_01_04_physical]
  exact kernelRPolynomial_index_symm 2 1 4
def rawEntry_2_02_02 : SparseEntry := [(7,-4),(8,16),(9,-4),(10,1),(16,12),(17,-8),(18,48),(19,-12),(20,-24),(21,12),(22,-2),(23,-24),(24,48),(31,16),(32,8),(34,24),(35,-16),(36,-32),(37,20),(38,8),(39,-8),(40,1)]
theorem rawEntry_2_02_02_data : ∀r : Fin 102, RawData.coefficient 2 r.val 2 2=sparseCoefficient rawEntry_2_02_02 r := by decide +kernel
theorem rawEntry_2_02_02_coordinates : sparsePolynomial 3 rawEntry_2_02_02=termsCoordinates 2 2 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_02_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_02_02_physical : invariantSubst (rawCoordinate 2 2 2)=kernelRPolynomial 2 2 2 := by
  rw [rawCoordinate_sparse 2 2 2 rawEntry_2_02_02 rawEntry_2_02_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_02_02)=_
  rw [rawEntry_2_02_02_coordinates]
  simpa using (rawMoment_from_terms 2 2 2 qTerms2 qTerms2_eq)
def rawEntry_2_02_03 : SparseEntry := [(11,-2),(12,2),(13,11),(14,-5),(15,1),(23,-8),(24,-8),(25,8),(26,51),(27,-25),(28,-20),(29,14),(30,-2),(31,12),(33,-12),(34,24),(41,-6),(42,-12),(43,-6),(44,12),(45,42),(46,24),(47,-30),(48,-45),(49,27),(50,9),(51,-9),(52,1)]
theorem rawEntry_2_02_03_data : ∀r : Fin 102, RawData.coefficient 2 r.val 2 3=sparseCoefficient rawEntry_2_02_03 r := by decide +kernel
theorem rawEntry_2_02_03_coordinates : sparsePolynomial 3 rawEntry_2_02_03=termsCoordinates 2 3 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_02_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_02_03_physical : invariantSubst (rawCoordinate 2 2 3)=kernelRPolynomial 2 2 3 := by
  rw [rawCoordinate_sparse 2 2 3 rawEntry_2_02_03 rawEntry_2_02_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_02_03)=_
  rw [rawEntry_2_02_03_coordinates]
  simpa using (rawMoment_from_terms 2 2 3 qTerms2 qTerms2_eq)
theorem rawEntry_2_03_02_data : ∀r : Fin 102, RawData.coefficient 2 r.val 3 2=sparseCoefficient rawEntry_2_02_03 r := by decide +kernel
theorem rawEntry_2_03_02_physical : invariantSubst (rawCoordinate 2 3 2)=kernelRPolynomial 2 3 2 := by
  have hh : rawCoordinate 2 3 2=rawCoordinate 2 2 3 := by
    rw [rawCoordinate_sparse 2 3 2 rawEntry_2_02_03 rawEntry_2_03_02_data,rawCoordinate_sparse 2 2 3 rawEntry_2_02_03 rawEntry_2_02_03_data]
  rw [hh,rawEntry_2_02_03_physical]
  exact kernelRPolynomial_index_symm 2 2 3
def rawEntry_2_02_04 : SparseEntry := [(16,12),(17,4),(18,-24),(19,6),(20,12),(21,-6),(22,1),(31,22),(32,8),(33,-72),(34,-27),(35,20),(36,88),(37,-37),(38,-22),(39,16),(40,-2),(41,36),(42,24),(43,-48),(45,-12),(46,24),(53,-12),(54,-8),(55,16),(56,-16),(57,-60),(58,28),(59,88),(60,31),(61,-50),(62,-60),(63,35),(64,10),(65,-10),(66,1)]
theorem rawEntry_2_02_04_data : ∀r : Fin 102, RawData.coefficient 2 r.val 2 4=sparseCoefficient rawEntry_2_02_04 r := by decide +kernel
theorem rawEntry_2_02_04_coordinates : sparsePolynomial 3 rawEntry_2_02_04=termsCoordinates 2 4 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_02_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_02_04_physical : invariantSubst (rawCoordinate 2 2 4)=kernelRPolynomial 2 2 4 := by
  rw [rawCoordinate_sparse 2 2 4 rawEntry_2_02_04 rawEntry_2_02_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_02_04)=_
  rw [rawEntry_2_02_04_coordinates]
  simpa using (rawMoment_from_terms 2 2 4 qTerms2 qTerms2_eq)
theorem rawEntry_2_04_02_data : ∀r : Fin 102, RawData.coefficient 2 r.val 4 2=sparseCoefficient rawEntry_2_02_04 r := by decide +kernel
theorem rawEntry_2_04_02_physical : invariantSubst (rawCoordinate 2 4 2)=kernelRPolynomial 2 4 2 := by
  have hh : rawCoordinate 2 4 2=rawCoordinate 2 2 4 := by
    rw [rawCoordinate_sparse 2 4 2 rawEntry_2_02_04 rawEntry_2_04_02_data,rawCoordinate_sparse 2 2 4 rawEntry_2_02_04 rawEntry_2_02_04_data]
  rw [hh,rawEntry_2_02_04_physical]
  exact kernelRPolynomial_index_symm 2 2 4
def rawEntry_2_03_03 : SparseEntry := [(16,-15),(17,-8),(18,6),(19,9),(20,6),(21,-6),(22,1),(31,-14),(32,-16),(33,-12),(34,-6),(35,38),(36,46),(37,-40),(38,-16),(39,16),(40,-2),(41,-72),(42,-24),(43,72),(53,45),(54,4),(55,-20),(56,-70),(57,-30),(58,25),(59,100),(60,25),(61,-50),(62,-60),(63,35),(64,10),(65,-10),(66,1)]
theorem rawEntry_2_03_03_data : ∀r : Fin 102, RawData.coefficient 2 r.val 3 3=sparseCoefficient rawEntry_2_03_03 r := by decide +kernel
theorem rawEntry_2_03_03_coordinates : sparsePolynomial 3 rawEntry_2_03_03=termsCoordinates 3 3 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_03_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_03_03_physical : invariantSubst (rawCoordinate 2 3 3)=kernelRPolynomial 2 3 3 := by
  rw [rawCoordinate_sparse 2 3 3 rawEntry_2_03_03 rawEntry_2_03_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_03_03)=_
  rw [rawEntry_2_03_03_coordinates]
  simpa using (rawMoment_from_terms 2 3 3 qTerms2 qTerms2_eq)
def rawEntry_2_03_04 : SparseEntry := [(23,10),(24,-8),(25,-10),(26,-12),(27,14),(28,7),(29,-7),(30,1),(41,-15),(42,24),(43,27),(44,-24),(45,-93),(46,-21),(47,63),(48,81),(49,-54),(50,-18),(51,18),(52,-2),(53,12),(55,-60),(56,-12),(57,36),(67,-23),(68,8),(69,93),(70,-8),(71,1),(72,-125),(73,-95),(74,55),(75,165),(76,33),(77,-77),(78,-77),(79,44),(80,11),(81,-11),(82,1)]
theorem rawEntry_2_03_04_data : ∀r : Fin 102, RawData.coefficient 2 r.val 3 4=sparseCoefficient rawEntry_2_03_04 r := by decide +kernel
theorem rawEntry_2_03_04_coordinates : sparsePolynomial 3 rawEntry_2_03_04=termsCoordinates 3 4 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_03_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_03_04_physical : invariantSubst (rawCoordinate 2 3 4)=kernelRPolynomial 2 3 4 := by
  rw [rawCoordinate_sparse 2 3 4 rawEntry_2_03_04 rawEntry_2_03_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_03_04)=_
  rw [rawEntry_2_03_04_coordinates]
  simpa using (rawMoment_from_terms 2 3 4 qTerms2 qTerms2_eq)
theorem rawEntry_2_04_03_data : ∀r : Fin 102, RawData.coefficient 2 r.val 4 3=sparseCoefficient rawEntry_2_03_04 r := by decide +kernel
theorem rawEntry_2_04_03_physical : invariantSubst (rawCoordinate 2 4 3)=kernelRPolynomial 2 4 3 := by
  have hh : rawCoordinate 2 4 3=rawCoordinate 2 3 4 := by
    rw [rawCoordinate_sparse 2 4 3 rawEntry_2_03_04 rawEntry_2_04_03_data,rawCoordinate_sparse 2 3 4 rawEntry_2_03_04 rawEntry_2_03_04_data]
  rw [hh,rawEntry_2_03_04_physical]
  exact kernelRPolynomial_index_symm 2 3 4
def rawEntry_2_04_04 : SparseEntry := [(31,-32),(32,-4),(33,48),(35,-16),(36,-32),(37,20),(38,8),(39,-8),(40,1),(53,-72),(54,-8),(55,-32),(56,128),(57,120),(58,-44),(59,-224),(60,-38),(61,100),(62,120),(63,-70),(64,-20),(65,20),(66,-2),(67,-96),(68,-24),(69,96),(71,-48),(83,21),(84,12),(85,8),(86,-120),(87,24),(88,234),(89,-36),(90,28),(91,-240),(92,-180),(93,105),(94,252),(95,42),(96,-112),(97,-96),(98,54),(99,12),(100,-12),(101,1)]
theorem rawEntry_2_04_04_data : ∀r : Fin 102, RawData.coefficient 2 r.val 4 4=sparseCoefficient rawEntry_2_04_04 r := by decide +kernel
theorem rawEntry_2_04_04_coordinates : sparsePolynomial 3 rawEntry_2_04_04=termsCoordinates 4 4 qTerms2 := by
  norm_num only [qTerms2,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_2_04_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_2_04_04_physical : invariantSubst (rawCoordinate 2 4 4)=kernelRPolynomial 2 4 4 := by
  rw [rawCoordinate_sparse 2 4 4 rawEntry_2_04_04 rawEntry_2_04_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_2_04_04)=_
  rw [rawEntry_2_04_04_coordinates]
  simpa using (rawMoment_from_terms 2 4 4 qTerms2 qTerms2_eq)
end ThomsonNegative.Certificate.Bridges
