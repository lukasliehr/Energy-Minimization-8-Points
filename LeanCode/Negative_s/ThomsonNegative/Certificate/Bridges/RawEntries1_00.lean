import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_1_00_00 : SparseEntry := [(0,3),(1,6),(2,-4),(3,-1)]
theorem rawEntry_1_00_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 0=sparseCoefficient rawEntry_1_00_00 r := by decide +kernel
theorem rawEntry_1_00_00_coordinates : sparsePolynomial 3 rawEntry_1_00_00=termsCoordinates 0 0 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_00_physical : invariantSubst (rawCoordinate 1 0 0)=kernelRPolynomial 1 0 0 := by
  rw [rawCoordinate_sparse 1 0 0 rawEntry_1_00_00 rawEntry_1_00_00_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_00)=_
  rw [rawEntry_1_00_00_coordinates]
  simpa using (rawMoment_from_terms 1 0 0 qTerms1 qTerms1_eq)
def rawEntry_1_00_01 : SparseEntry := [(1,1),(2,6),(4,6),(6,-1)]
theorem rawEntry_1_00_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 1=sparseCoefficient rawEntry_1_00_01 r := by decide +kernel
theorem rawEntry_1_00_01_coordinates : sparsePolynomial 3 rawEntry_1_00_01=termsCoordinates 0 1 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_01_physical : invariantSubst (rawCoordinate 1 0 1)=kernelRPolynomial 1 0 1 := by
  rw [rawCoordinate_sparse 1 0 1 rawEntry_1_00_01 rawEntry_1_00_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_01)=_
  rw [rawEntry_1_00_01_coordinates]
  simpa using (rawMoment_from_terms 1 0 1 qTerms1 qTerms1_eq)
theorem rawEntry_1_01_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 0=sparseCoefficient rawEntry_1_00_01 r := by decide +kernel
theorem rawEntry_1_01_00_physical : invariantSubst (rawCoordinate 1 1 0)=kernelRPolynomial 1 1 0 := by
  have hh : rawCoordinate 1 1 0=rawCoordinate 1 0 1 := by
    rw [rawCoordinate_sparse 1 1 0 rawEntry_1_00_01 rawEntry_1_01_00_data,rawCoordinate_sparse 1 0 1 rawEntry_1_00_01 rawEntry_1_00_01_data]
  rw [hh,rawEntry_1_00_01_physical]
  exact kernelRPolynomial_index_symm 1 0 1
def rawEntry_1_00_02 : SparseEntry := [(2,-2),(3,1),(4,-9),(5,3),(7,4),(8,-1),(9,1),(10,-1)]
theorem rawEntry_1_00_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 2=sparseCoefficient rawEntry_1_00_02 r := by decide +kernel
theorem rawEntry_1_00_02_coordinates : sparsePolynomial 3 rawEntry_1_00_02=termsCoordinates 0 2 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_02_physical : invariantSubst (rawCoordinate 1 0 2)=kernelRPolynomial 1 0 2 := by
  rw [rawCoordinate_sparse 1 0 2 rawEntry_1_00_02 rawEntry_1_00_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_02)=_
  rw [rawEntry_1_00_02_coordinates]
  simpa using (rawMoment_from_terms 1 0 2 qTerms1 qTerms1_eq)
theorem rawEntry_1_02_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 0=sparseCoefficient rawEntry_1_00_02 r := by decide +kernel
theorem rawEntry_1_02_00_physical : invariantSubst (rawCoordinate 1 2 0)=kernelRPolynomial 1 2 0 := by
  have hh : rawCoordinate 1 2 0=rawCoordinate 1 0 2 := by
    rw [rawCoordinate_sparse 1 2 0 rawEntry_1_00_02 rawEntry_1_02_00_data,rawCoordinate_sparse 1 0 2 rawEntry_1_00_02 rawEntry_1_00_02_data]
  rw [hh,rawEntry_1_00_02_physical]
  exact kernelRPolynomial_index_symm 1 0 2
def rawEntry_1_00_03 : SparseEntry := [(4,3),(5,-3),(6,1),(7,-6),(8,-3),(9,3),(11,-10),(12,4),(13,-2),(14,2),(15,-1)]
theorem rawEntry_1_00_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 3=sparseCoefficient rawEntry_1_00_03 r := by decide +kernel
theorem rawEntry_1_00_03_coordinates : sparsePolynomial 3 rawEntry_1_00_03=termsCoordinates 0 3 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_03_physical : invariantSubst (rawCoordinate 1 0 3)=kernelRPolynomial 1 0 3 := by
  rw [rawCoordinate_sparse 1 0 3 rawEntry_1_00_03 rawEntry_1_00_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_03)=_
  rw [rawEntry_1_00_03_coordinates]
  simpa using (rawMoment_from_terms 1 0 3 qTerms1 qTerms1_eq)
theorem rawEntry_1_03_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 0=sparseCoefficient rawEntry_1_00_03 r := by decide +kernel
theorem rawEntry_1_03_00_physical : invariantSubst (rawCoordinate 1 3 0)=kernelRPolynomial 1 3 0 := by
  have hh : rawCoordinate 1 3 0=rawCoordinate 1 0 3 := by
    rw [rawCoordinate_sparse 1 3 0 rawEntry_1_00_03 rawEntry_1_03_00_data,rawCoordinate_sparse 1 0 3 rawEntry_1_00_03 rawEntry_1_00_03_data]
  rw [hh,rawEntry_1_00_03_physical]
  exact kernelRPolynomial_index_symm 1 0 3
def rawEntry_1_00_04 : SparseEntry := [(7,2),(8,4),(9,-4),(10,1),(11,15),(12,-9),(13,-3),(14,3),(16,6),(17,-4),(18,-9),(19,3),(20,-3),(21,3),(22,-1)]
theorem rawEntry_1_00_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 4=sparseCoefficient rawEntry_1_00_04 r := by decide +kernel
theorem rawEntry_1_00_04_coordinates : sparsePolynomial 3 rawEntry_1_00_04=termsCoordinates 0 4 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_04_physical : invariantSubst (rawCoordinate 1 0 4)=kernelRPolynomial 1 0 4 := by
  rw [rawCoordinate_sparse 1 0 4 rawEntry_1_00_04 rawEntry_1_00_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_04)=_
  rw [rawEntry_1_00_04_coordinates]
  simpa using (rawMoment_from_terms 1 0 4 qTerms1 qTerms1_eq)
theorem rawEntry_1_04_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 0=sparseCoefficient rawEntry_1_00_04 r := by decide +kernel
theorem rawEntry_1_04_00_physical : invariantSubst (rawCoordinate 1 4 0)=kernelRPolynomial 1 4 0 := by
  have hh : rawCoordinate 1 4 0=rawCoordinate 1 0 4 := by
    rw [rawCoordinate_sparse 1 4 0 rawEntry_1_00_04 rawEntry_1_04_00_data,rawCoordinate_sparse 1 0 4 rawEntry_1_00_04 rawEntry_1_00_04_data]
  rw [hh,rawEntry_1_00_04_physical]
  exact kernelRPolynomial_index_symm 1 0 4
def rawEntry_1_00_05 : SparseEntry := [(11,-5),(12,5),(13,5),(14,-5),(15,1),(16,-9),(17,6),(18,21),(19,-12),(20,-3),(21,3),(23,14),(24,5),(25,-8),(26,-6),(27,1),(28,-4),(29,4),(30,-1)]
theorem rawEntry_1_00_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 0 5=sparseCoefficient rawEntry_1_00_05 r := by decide +kernel
theorem rawEntry_1_00_05_coordinates : sparsePolynomial 3 rawEntry_1_00_05=termsCoordinates 0 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_00_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_00_05_physical : invariantSubst (rawCoordinate 1 0 5)=kernelRPolynomial 1 0 5 := by
  rw [rawCoordinate_sparse 1 0 5 rawEntry_1_00_05 rawEntry_1_00_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_00_05)=_
  rw [rawEntry_1_00_05_coordinates]
  simpa using (rawMoment_from_terms 1 0 5 qTerms1 qTerms1_eq)
theorem rawEntry_1_05_00_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 0=sparseCoefficient rawEntry_1_00_05 r := by decide +kernel
theorem rawEntry_1_05_00_physical : invariantSubst (rawCoordinate 1 5 0)=kernelRPolynomial 1 5 0 := by
  have hh : rawCoordinate 1 5 0=rawCoordinate 1 0 5 := by
    rw [rawCoordinate_sparse 1 5 0 rawEntry_1_00_05 rawEntry_1_05_00_data,rawCoordinate_sparse 1 0 5 rawEntry_1_00_05 rawEntry_1_00_05_data]
  rw [hh,rawEntry_1_00_05_physical]
  exact kernelRPolynomial_index_symm 1 0 5
def rawEntry_1_01_01 : SparseEntry := [(2,-2),(3,1),(4,18),(7,-8),(8,8),(9,4),(10,-1)]
theorem rawEntry_1_01_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 1=sparseCoefficient rawEntry_1_01_01 r := by decide +kernel
theorem rawEntry_1_01_01_coordinates : sparsePolynomial 3 rawEntry_1_01_01=termsCoordinates 1 1 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_01_01_physical : invariantSubst (rawCoordinate 1 1 1)=kernelRPolynomial 1 1 1 := by
  rw [rawCoordinate_sparse 1 1 1 rawEntry_1_01_01 rawEntry_1_01_01_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_01_01)=_
  rw [rawEntry_1_01_01_coordinates]
  simpa using (rawMoment_from_terms 1 1 1 qTerms1 qTerms1_eq)
def rawEntry_1_01_02 : SparseEntry := [(4,3),(5,-3),(6,1),(8,6),(11,8),(12,-8),(13,1),(14,5),(15,-1)]
theorem rawEntry_1_01_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 2=sparseCoefficient rawEntry_1_01_02 r := by decide +kernel
theorem rawEntry_1_01_02_coordinates : sparsePolynomial 3 rawEntry_1_01_02=termsCoordinates 1 2 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_01_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_01_02_physical : invariantSubst (rawCoordinate 1 1 2)=kernelRPolynomial 1 1 2 := by
  rw [rawCoordinate_sparse 1 1 2 rawEntry_1_01_02 rawEntry_1_01_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_01_02)=_
  rw [rawEntry_1_01_02_coordinates]
  simpa using (rawMoment_from_terms 1 1 2 qTerms1 qTerms1_eq)
theorem rawEntry_1_02_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 1=sparseCoefficient rawEntry_1_01_02 r := by decide +kernel
theorem rawEntry_1_02_01_physical : invariantSubst (rawCoordinate 1 2 1)=kernelRPolynomial 1 2 1 := by
  have hh : rawCoordinate 1 2 1=rawCoordinate 1 1 2 := by
    rw [rawCoordinate_sparse 1 2 1 rawEntry_1_01_02 rawEntry_1_02_01_data,rawCoordinate_sparse 1 1 2 rawEntry_1_01_02 rawEntry_1_01_02_data]
  rw [hh,rawEntry_1_01_02_physical]
  exact kernelRPolynomial_index_symm 1 1 2
def rawEntry_1_01_03 : SparseEntry := [(7,2),(8,4),(9,-4),(10,1),(11,-12),(13,6),(16,6),(17,8),(19,-12),(21,6),(22,-1)]
theorem rawEntry_1_01_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 3=sparseCoefficient rawEntry_1_01_03 r := by decide +kernel
theorem rawEntry_1_01_03_coordinates : sparsePolynomial 3 rawEntry_1_01_03=termsCoordinates 1 3 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_01_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_01_03_physical : invariantSubst (rawCoordinate 1 1 3)=kernelRPolynomial 1 1 3 := by
  rw [rawCoordinate_sparse 1 1 3 rawEntry_1_01_03 rawEntry_1_01_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_01_03)=_
  rw [rawEntry_1_01_03_coordinates]
  simpa using (rawMoment_from_terms 1 1 3 qTerms1 qTerms1_eq)
theorem rawEntry_1_03_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 1=sparseCoefficient rawEntry_1_01_03 r := by decide +kernel
theorem rawEntry_1_03_01_physical : invariantSubst (rawCoordinate 1 3 1)=kernelRPolynomial 1 3 1 := by
  have hh : rawCoordinate 1 3 1=rawCoordinate 1 1 3 := by
    rw [rawCoordinate_sparse 1 3 1 rawEntry_1_01_03 rawEntry_1_03_01_data,rawCoordinate_sparse 1 1 3 rawEntry_1_01_03 rawEntry_1_01_03_data]
  rw [hh,rawEntry_1_01_03_physical]
  exact kernelRPolynomial_index_symm 1 1 3
def rawEntry_1_01_04 : SparseEntry := [(11,-5),(12,5),(13,5),(14,-5),(15,1),(16,18),(18,-18),(20,6),(23,-16),(24,14),(25,16),(26,3),(27,-17),(28,-1),(29,7),(30,-1)]
theorem rawEntry_1_01_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 4=sparseCoefficient rawEntry_1_01_04 r := by decide +kernel
theorem rawEntry_1_01_04_coordinates : sparsePolynomial 3 rawEntry_1_01_04=termsCoordinates 1 4 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_01_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_01_04_physical : invariantSubst (rawCoordinate 1 1 4)=kernelRPolynomial 1 1 4 := by
  rw [rawCoordinate_sparse 1 1 4 rawEntry_1_01_04 rawEntry_1_01_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_01_04)=_
  rw [rawEntry_1_01_04_coordinates]
  simpa using (rawMoment_from_terms 1 1 4 qTerms1 qTerms1_eq)
theorem rawEntry_1_04_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 1=sparseCoefficient rawEntry_1_01_04 r := by decide +kernel
theorem rawEntry_1_04_01_physical : invariantSubst (rawCoordinate 1 4 1)=kernelRPolynomial 1 4 1 := by
  have hh : rawCoordinate 1 4 1=rawCoordinate 1 1 4 := by
    rw [rawCoordinate_sparse 1 4 1 rawEntry_1_01_04 rawEntry_1_04_01_data,rawCoordinate_sparse 1 1 4 rawEntry_1_01_04 rawEntry_1_01_04_data]
  rw [hh,rawEntry_1_01_04_physical]
  exact kernelRPolynomial_index_symm 1 1 4
def rawEntry_1_01_05 : SparseEntry := [(16,3),(17,-2),(18,-12),(19,9),(20,6),(21,-6),(22,1),(23,12),(24,24),(26,-24),(28,6),(31,2),(32,-8),(33,-24),(34,15),(35,28),(36,8),(37,-23),(38,-2),(39,8),(40,-1)]
theorem rawEntry_1_01_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 1 5=sparseCoefficient rawEntry_1_01_05 r := by decide +kernel
theorem rawEntry_1_01_05_coordinates : sparsePolynomial 3 rawEntry_1_01_05=termsCoordinates 1 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_01_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_01_05_physical : invariantSubst (rawCoordinate 1 1 5)=kernelRPolynomial 1 1 5 := by
  rw [rawCoordinate_sparse 1 1 5 rawEntry_1_01_05 rawEntry_1_01_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_01_05)=_
  rw [rawEntry_1_01_05_coordinates]
  simpa using (rawMoment_from_terms 1 1 5 qTerms1 qTerms1_eq)
theorem rawEntry_1_05_01_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 1=sparseCoefficient rawEntry_1_01_05 r := by decide +kernel
theorem rawEntry_1_05_01_physical : invariantSubst (rawCoordinate 1 5 1)=kernelRPolynomial 1 5 1 := by
  have hh : rawCoordinate 1 5 1=rawCoordinate 1 1 5 := by
    rw [rawCoordinate_sparse 1 5 1 rawEntry_1_01_05 rawEntry_1_05_01_data,rawCoordinate_sparse 1 1 5 rawEntry_1_01_05 rawEntry_1_01_05_data]
  rw [hh,rawEntry_1_01_05_physical]
  exact kernelRPolynomial_index_symm 1 1 5
def rawEntry_1_02_02 : SparseEntry := [(7,2),(8,4),(9,-4),(10,1),(11,6),(16,-21),(17,-4),(18,30),(19,-9),(20,-6),(21,6),(22,-1)]
theorem rawEntry_1_02_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 2=sparseCoefficient rawEntry_1_02_02 r := by decide +kernel
theorem rawEntry_1_02_02_coordinates : sparsePolynomial 3 rawEntry_1_02_02=termsCoordinates 2 2 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_02_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_02_02_physical : invariantSubst (rawCoordinate 1 2 2)=kernelRPolynomial 1 2 2 := by
  rw [rawCoordinate_sparse 1 2 2 rawEntry_1_02_02 rawEntry_1_02_02_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_02_02)=_
  rw [rawEntry_1_02_02_coordinates]
  simpa using (rawMoment_from_terms 1 2 2 qTerms1 qTerms1_eq)
def rawEntry_1_02_03 : SparseEntry := [(11,-5),(12,5),(13,5),(14,-5),(15,1),(16,-9),(18,3),(23,-4),(24,-22),(25,4),(26,30),(27,-14),(28,-7),(29,7),(30,-1)]
theorem rawEntry_1_02_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 3=sparseCoefficient rawEntry_1_02_03 r := by decide +kernel
theorem rawEntry_1_02_03_coordinates : sparsePolynomial 3 rawEntry_1_02_03=termsCoordinates 2 3 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_02_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_02_03_physical : invariantSubst (rawCoordinate 1 2 3)=kernelRPolynomial 1 2 3 := by
  rw [rawCoordinate_sparse 1 2 3 rawEntry_1_02_03 rawEntry_1_02_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_02_03)=_
  rw [rawEntry_1_02_03_coordinates]
  simpa using (rawMoment_from_terms 1 2 3 qTerms1 qTerms1_eq)
theorem rawEntry_1_03_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 2=sparseCoefficient rawEntry_1_02_03 r := by decide +kernel
theorem rawEntry_1_03_02_physical : invariantSubst (rawCoordinate 1 3 2)=kernelRPolynomial 1 3 2 := by
  have hh : rawCoordinate 1 3 2=rawCoordinate 1 2 3 := by
    rw [rawCoordinate_sparse 1 3 2 rawEntry_1_02_03 rawEntry_1_03_02_data,rawCoordinate_sparse 1 2 3 rawEntry_1_02_03 rawEntry_1_02_03_data]
  rw [hh,rawEntry_1_02_03_physical]
  exact kernelRPolynomial_index_symm 1 2 3
def rawEntry_1_02_04 : SparseEntry := [(16,3),(17,-2),(18,-12),(19,9),(20,6),(21,-6),(22,1),(23,-6),(24,-3),(26,3),(31,29),(32,4),(33,-42),(34,-21),(35,13),(36,41),(37,-20),(38,-8),(39,8),(40,-1)]
theorem rawEntry_1_02_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 4=sparseCoefficient rawEntry_1_02_04 r := by decide +kernel
theorem rawEntry_1_02_04_coordinates : sparsePolynomial 3 rawEntry_1_02_04=termsCoordinates 2 4 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_02_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_02_04_physical : invariantSubst (rawCoordinate 1 2 4)=kernelRPolynomial 1 2 4 := by
  rw [rawCoordinate_sparse 1 2 4 rawEntry_1_02_04 rawEntry_1_02_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_02_04)=_
  rw [rawEntry_1_02_04_coordinates]
  simpa using (rawMoment_from_terms 1 2 4 qTerms1 qTerms1_eq)
theorem rawEntry_1_04_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 2=sparseCoefficient rawEntry_1_02_04 r := by decide +kernel
theorem rawEntry_1_04_02_physical : invariantSubst (rawCoordinate 1 4 2)=kernelRPolynomial 1 4 2 := by
  have hh : rawCoordinate 1 4 2=rawCoordinate 1 2 4 := by
    rw [rawCoordinate_sparse 1 4 2 rawEntry_1_02_04 rawEntry_1_04_02_data,rawCoordinate_sparse 1 2 4 rawEntry_1_02_04 rawEntry_1_02_04_data]
  rw [hh,rawEntry_1_02_04_physical]
  exact kernelRPolynomial_index_symm 1 2 4
def rawEntry_1_02_05 : SparseEntry := [(23,7),(24,7),(25,-7),(26,-21),(27,14),(28,7),(29,-7),(30,1),(31,15),(33,-9),(34,-3),(36,3),(41,-21),(43,81),(45,-81),(46,-27),(47,27),(48,54),(49,-27),(50,-9),(51,9),(52,-1)]
theorem rawEntry_1_02_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 2 5=sparseCoefficient rawEntry_1_02_05 r := by decide +kernel
theorem rawEntry_1_02_05_coordinates : sparsePolynomial 3 rawEntry_1_02_05=termsCoordinates 2 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_02_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_02_05_physical : invariantSubst (rawCoordinate 1 2 5)=kernelRPolynomial 1 2 5 := by
  rw [rawCoordinate_sparse 1 2 5 rawEntry_1_02_05 rawEntry_1_02_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_02_05)=_
  rw [rawEntry_1_02_05_coordinates]
  simpa using (rawMoment_from_terms 1 2 5 qTerms1 qTerms1_eq)
theorem rawEntry_1_05_02_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 2=sparseCoefficient rawEntry_1_02_05 r := by decide +kernel
theorem rawEntry_1_05_02_physical : invariantSubst (rawCoordinate 1 5 2)=kernelRPolynomial 1 5 2 := by
  have hh : rawCoordinate 1 5 2=rawCoordinate 1 2 5 := by
    rw [rawCoordinate_sparse 1 5 2 rawEntry_1_02_05 rawEntry_1_05_02_data,rawCoordinate_sparse 1 2 5 rawEntry_1_02_05 rawEntry_1_02_05_data]
  rw [hh,rawEntry_1_02_05_physical]
  exact kernelRPolynomial_index_symm 1 2 5
def rawEntry_1_03_03 : SparseEntry := [(16,3),(17,-2),(18,-12),(19,9),(20,6),(21,-6),(22,1),(23,6),(24,-12),(31,-16),(32,-8),(34,-24),(35,16),(36,32),(37,-20),(38,-8),(39,8),(40,-1)]
theorem rawEntry_1_03_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 3=sparseCoefficient rawEntry_1_03_03 r := by decide +kernel
theorem rawEntry_1_03_03_coordinates : sparsePolynomial 3 rawEntry_1_03_03=termsCoordinates 3 3 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_03_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_03_03_physical : invariantSubst (rawCoordinate 1 3 3)=kernelRPolynomial 1 3 3 := by
  rw [rawCoordinate_sparse 1 3 3 rawEntry_1_03_03 rawEntry_1_03_03_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_03_03)=_
  rw [rawEntry_1_03_03_coordinates]
  simpa using (rawMoment_from_terms 1 3 3 qTerms1 qTerms1_eq)
def rawEntry_1_03_04 : SparseEntry := [(23,7),(24,7),(25,-7),(26,-21),(27,14),(28,7),(29,-7),(30,1),(31,-3),(33,3),(34,-6),(41,6),(42,12),(43,6),(44,-12),(45,-42),(46,-24),(47,30),(48,45),(49,-27),(50,-9),(51,9),(52,-1)]
theorem rawEntry_1_03_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 4=sparseCoefficient rawEntry_1_03_04 r := by decide +kernel
theorem rawEntry_1_03_04_coordinates : sparsePolynomial 3 rawEntry_1_03_04=termsCoordinates 3 4 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_03_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_03_04_physical : invariantSubst (rawCoordinate 1 3 4)=kernelRPolynomial 1 3 4 := by
  rw [rawCoordinate_sparse 1 3 4 rawEntry_1_03_04 rawEntry_1_03_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_03_04)=_
  rw [rawEntry_1_03_04_coordinates]
  simpa using (rawMoment_from_terms 1 3 4 qTerms1 qTerms1_eq)
theorem rawEntry_1_04_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 3=sparseCoefficient rawEntry_1_03_04 r := by decide +kernel
theorem rawEntry_1_04_03_physical : invariantSubst (rawCoordinate 1 4 3)=kernelRPolynomial 1 4 3 := by
  have hh : rawCoordinate 1 4 3=rawCoordinate 1 3 4 := by
    rw [rawCoordinate_sparse 1 4 3 rawEntry_1_03_04 rawEntry_1_04_03_data,rawCoordinate_sparse 1 3 4 rawEntry_1_03_04 rawEntry_1_03_04_data]
  rw [hh,rawEntry_1_03_04_physical]
  exact kernelRPolynomial_index_symm 1 3 4
def rawEntry_1_03_05 : SparseEntry := [(31,-8),(32,2),(33,24),(34,12),(35,-16),(36,-32),(37,20),(38,8),(39,-8),(40,1),(41,-9),(42,-6),(43,12),(45,3),(46,-6),(53,12),(54,8),(55,-16),(56,16),(57,60),(58,-28),(59,-88),(60,-31),(61,50),(62,60),(63,-35),(64,-10),(65,10),(66,-1)]
theorem rawEntry_1_03_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 3 5=sparseCoefficient rawEntry_1_03_05 r := by decide +kernel
theorem rawEntry_1_03_05_coordinates : sparsePolynomial 3 rawEntry_1_03_05=termsCoordinates 3 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_03_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_03_05_physical : invariantSubst (rawCoordinate 1 3 5)=kernelRPolynomial 1 3 5 := by
  rw [rawCoordinate_sparse 1 3 5 rawEntry_1_03_05 rawEntry_1_03_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_03_05)=_
  rw [rawEntry_1_03_05_coordinates]
  simpa using (rawMoment_from_terms 1 3 5 qTerms1 qTerms1_eq)
theorem rawEntry_1_05_03_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 3=sparseCoefficient rawEntry_1_03_05 r := by decide +kernel
theorem rawEntry_1_05_03_physical : invariantSubst (rawCoordinate 1 5 3)=kernelRPolynomial 1 5 3 := by
  have hh : rawCoordinate 1 5 3=rawCoordinate 1 3 5 := by
    rw [rawCoordinate_sparse 1 5 3 rawEntry_1_03_05 rawEntry_1_05_03_data,rawCoordinate_sparse 1 3 5 rawEntry_1_03_05 rawEntry_1_03_05_data]
  rw [hh,rawEntry_1_03_05_physical]
  exact kernelRPolynomial_index_symm 1 3 5
def rawEntry_1_04_04 : SparseEntry := [(31,-8),(32,2),(33,24),(34,12),(35,-16),(36,-32),(37,20),(38,8),(39,-8),(40,1),(41,18),(42,6),(43,-18),(53,-45),(54,-4),(55,20),(56,70),(57,30),(58,-25),(59,-100),(60,-25),(61,50),(62,60),(63,-35),(64,-10),(65,10),(66,-1)]
theorem rawEntry_1_04_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 4=sparseCoefficient rawEntry_1_04_04 r := by decide +kernel
theorem rawEntry_1_04_04_coordinates : sparsePolynomial 3 rawEntry_1_04_04=termsCoordinates 4 4 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_04_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_04_04_physical : invariantSubst (rawCoordinate 1 4 4)=kernelRPolynomial 1 4 4 := by
  rw [rawCoordinate_sparse 1 4 4 rawEntry_1_04_04 rawEntry_1_04_04_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_04_04)=_
  rw [rawEntry_1_04_04_coordinates]
  simpa using (rawMoment_from_terms 1 4 4 qTerms1 qTerms1_eq)
def rawEntry_1_04_05 : SparseEntry := [(41,3),(42,-9),(43,-27),(44,9),(45,54),(46,18),(47,-30),(48,-45),(49,27),(50,9),(51,-9),(52,1),(53,-3),(55,15),(56,3),(57,-9),(67,23),(68,-8),(69,-93),(70,8),(71,-1),(72,125),(73,95),(74,-55),(75,-165),(76,-33),(77,77),(78,77),(79,-44),(80,-11),(81,11),(82,-1)]
theorem rawEntry_1_04_05_data : ∀r : Fin 102, RawData.coefficient 1 r.val 4 5=sparseCoefficient rawEntry_1_04_05 r := by decide +kernel
theorem rawEntry_1_04_05_coordinates : sparsePolynomial 3 rawEntry_1_04_05=termsCoordinates 4 5 qTerms1 := by
  norm_num only [qTerms1,termsCoordinates,termCoordinates,orbitCoordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_1_04_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_1_04_05_physical : invariantSubst (rawCoordinate 1 4 5)=kernelRPolynomial 1 4 5 := by
  rw [rawCoordinate_sparse 1 4 5 rawEntry_1_04_05 rawEntry_1_04_05_data]
  change invariantSubst (sparsePolynomial 3 rawEntry_1_04_05)=_
  rw [rawEntry_1_04_05_coordinates]
  simpa using (rawMoment_from_terms 1 4 5 qTerms1 qTerms1_eq)
theorem rawEntry_1_05_04_data : ∀r : Fin 102, RawData.coefficient 1 r.val 5 4=sparseCoefficient rawEntry_1_04_05 r := by decide +kernel
theorem rawEntry_1_05_04_physical : invariantSubst (rawCoordinate 1 5 4)=kernelRPolynomial 1 5 4 := by
  have hh : rawCoordinate 1 5 4=rawCoordinate 1 4 5 := by
    rw [rawCoordinate_sparse 1 5 4 rawEntry_1_04_05 rawEntry_1_05_04_data,rawCoordinate_sparse 1 4 5 rawEntry_1_04_05 rawEntry_1_04_05_data]
  rw [hh,rawEntry_1_04_05_physical]
  exact kernelRPolynomial_index_symm 1 4 5
end ThomsonNegative.Certificate.Bridges
