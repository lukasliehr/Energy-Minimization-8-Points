import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_0_00_00 : SparseEntry := [(0,192)]
theorem rawEntry_0_00_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 0=sparseCoefficient rawEntry_0_00_00 r := by decide +kernel
theorem rawEntry_0_00_00_coordinates : sparsePolynomial 21 rawEntry_0_00_00=r0Coordinates 0 0 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_00,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_00_physical : invariantSubst (rawCoordinate 0 0 0)=kernelRPolynomial 0 0 0 := by
  rw [rawCoordinate_sparse 0 0 0 rawEntry_0_00_00 rawEntry_0_00_00_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_00)=_
  rw [rawEntry_0_00_00_coordinates]
  exact r0Coordinates_subst 0 0
def rawEntry_0_00_01 : SparseEntry := [(0,24),(1,56)]
theorem rawEntry_0_00_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 1=sparseCoefficient rawEntry_0_00_01 r := by decide +kernel
theorem rawEntry_0_00_01_coordinates : sparsePolynomial 21 rawEntry_0_00_01=r0Coordinates 0 1 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_01_physical : invariantSubst (rawCoordinate 0 0 1)=kernelRPolynomial 0 0 1 := by
  rw [rawCoordinate_sparse 0 0 1 rawEntry_0_00_01 rawEntry_0_00_01_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_01)=_
  rw [rawEntry_0_00_01_coordinates]
  exact r0Coordinates_subst 0 1
theorem rawEntry_0_01_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 0=sparseCoefficient rawEntry_0_00_01 r := by decide +kernel
theorem rawEntry_0_01_00_physical : invariantSubst (rawCoordinate 0 1 0)=kernelRPolynomial 0 1 0 := by
  have hh : rawCoordinate 0 1 0=rawCoordinate 0 0 1 := by
    rw [rawCoordinate_sparse 0 1 0 rawEntry_0_00_01 rawEntry_0_01_00_data,rawCoordinate_sparse 0 0 1 rawEntry_0_00_01 rawEntry_0_00_01_data]
  rw [hh,rawEntry_0_00_01_physical]
  exact kernelRPolynomial_index_symm 0 0 1
def rawEntry_0_00_02 : SparseEntry := [(0,24),(2,-112),(3,56)]
theorem rawEntry_0_00_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 2=sparseCoefficient rawEntry_0_00_02 r := by decide +kernel
theorem rawEntry_0_00_02_coordinates : sparsePolynomial 21 rawEntry_0_00_02=r0Coordinates 0 2 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_02_physical : invariantSubst (rawCoordinate 0 0 2)=kernelRPolynomial 0 0 2 := by
  rw [rawCoordinate_sparse 0 0 2 rawEntry_0_00_02 rawEntry_0_00_02_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_02)=_
  rw [rawEntry_0_00_02_coordinates]
  exact r0Coordinates_subst 0 2
theorem rawEntry_0_02_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 0=sparseCoefficient rawEntry_0_00_02 r := by decide +kernel
theorem rawEntry_0_02_00_physical : invariantSubst (rawCoordinate 0 2 0)=kernelRPolynomial 0 2 0 := by
  have hh : rawCoordinate 0 2 0=rawCoordinate 0 0 2 := by
    rw [rawCoordinate_sparse 0 2 0 rawEntry_0_00_02 rawEntry_0_02_00_data,rawCoordinate_sparse 0 0 2 rawEntry_0_00_02 rawEntry_0_00_02_data]
  rw [hh,rawEntry_0_00_02_physical]
  exact kernelRPolynomial_index_symm 0 0 2
def rawEntry_0_00_03 : SparseEntry := [(0,24),(4,168),(5,-168),(6,56)]
theorem rawEntry_0_00_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 3=sparseCoefficient rawEntry_0_00_03 r := by decide +kernel
theorem rawEntry_0_00_03_coordinates : sparsePolynomial 21 rawEntry_0_00_03=r0Coordinates 0 3 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_03_physical : invariantSubst (rawCoordinate 0 0 3)=kernelRPolynomial 0 0 3 := by
  rw [rawCoordinate_sparse 0 0 3 rawEntry_0_00_03 rawEntry_0_00_03_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_03)=_
  rw [rawEntry_0_00_03_coordinates]
  exact r0Coordinates_subst 0 3
theorem rawEntry_0_03_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 0=sparseCoefficient rawEntry_0_00_03 r := by decide +kernel
theorem rawEntry_0_03_00_physical : invariantSubst (rawCoordinate 0 3 0)=kernelRPolynomial 0 3 0 := by
  have hh : rawCoordinate 0 3 0=rawCoordinate 0 0 3 := by
    rw [rawCoordinate_sparse 0 3 0 rawEntry_0_00_03 rawEntry_0_03_00_data,rawCoordinate_sparse 0 0 3 rawEntry_0_00_03 rawEntry_0_00_03_data]
  rw [hh,rawEntry_0_00_03_physical]
  exact kernelRPolynomial_index_symm 0 0 3
def rawEntry_0_00_04 : SparseEntry := [(0,24),(7,112),(8,224),(9,-224),(10,56)]
theorem rawEntry_0_00_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 4=sparseCoefficient rawEntry_0_00_04 r := by decide +kernel
theorem rawEntry_0_00_04_coordinates : sparsePolynomial 21 rawEntry_0_00_04=r0Coordinates 0 4 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_04_physical : invariantSubst (rawCoordinate 0 0 4)=kernelRPolynomial 0 0 4 := by
  rw [rawCoordinate_sparse 0 0 4 rawEntry_0_00_04 rawEntry_0_00_04_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_04)=_
  rw [rawEntry_0_00_04_coordinates]
  exact r0Coordinates_subst 0 4
theorem rawEntry_0_04_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 0=sparseCoefficient rawEntry_0_00_04 r := by decide +kernel
theorem rawEntry_0_04_00_physical : invariantSubst (rawCoordinate 0 4 0)=kernelRPolynomial 0 4 0 := by
  have hh : rawCoordinate 0 4 0=rawCoordinate 0 0 4 := by
    rw [rawCoordinate_sparse 0 4 0 rawEntry_0_00_04 rawEntry_0_04_00_data,rawCoordinate_sparse 0 0 4 rawEntry_0_00_04 rawEntry_0_00_04_data]
  rw [hh,rawEntry_0_00_04_physical]
  exact kernelRPolynomial_index_symm 0 0 4
def rawEntry_0_00_05 : SparseEntry := [(0,24),(11,-280),(12,280),(13,280),(14,-280),(15,56)]
theorem rawEntry_0_00_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 5=sparseCoefficient rawEntry_0_00_05 r := by decide +kernel
theorem rawEntry_0_00_05_coordinates : sparsePolynomial 21 rawEntry_0_00_05=r0Coordinates 0 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_05_physical : invariantSubst (rawCoordinate 0 0 5)=kernelRPolynomial 0 0 5 := by
  rw [rawCoordinate_sparse 0 0 5 rawEntry_0_00_05 rawEntry_0_00_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_05)=_
  rw [rawEntry_0_00_05_coordinates]
  exact r0Coordinates_subst 0 5
theorem rawEntry_0_05_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 0=sparseCoefficient rawEntry_0_00_05 r := by decide +kernel
theorem rawEntry_0_05_00_physical : invariantSubst (rawCoordinate 0 5 0)=kernelRPolynomial 0 5 0 := by
  have hh : rawCoordinate 0 5 0=rawCoordinate 0 0 5 := by
    rw [rawCoordinate_sparse 0 5 0 rawEntry_0_00_05 rawEntry_0_05_00_data,rawCoordinate_sparse 0 0 5 rawEntry_0_00_05 rawEntry_0_00_05_data]
  rw [hh,rawEntry_0_00_05_physical]
  exact kernelRPolynomial_index_symm 0 0 5
def rawEntry_0_00_06 : SparseEntry := [(0,24),(16,168),(17,-112),(18,-672),(19,504),(20,336),(21,-336),(22,56)]
theorem rawEntry_0_00_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 0 6=sparseCoefficient rawEntry_0_00_06 r := by decide +kernel
theorem rawEntry_0_00_06_coordinates : sparsePolynomial 21 rawEntry_0_00_06=r0Coordinates 0 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_00_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_00_06_physical : invariantSubst (rawCoordinate 0 0 6)=kernelRPolynomial 0 0 6 := by
  rw [rawCoordinate_sparse 0 0 6 rawEntry_0_00_06 rawEntry_0_00_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_00_06)=_
  rw [rawEntry_0_00_06_coordinates]
  exact r0Coordinates_subst 0 6
theorem rawEntry_0_06_00_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 0=sparseCoefficient rawEntry_0_00_06 r := by decide +kernel
theorem rawEntry_0_06_00_physical : invariantSubst (rawCoordinate 0 6 0)=kernelRPolynomial 0 6 0 := by
  have hh : rawCoordinate 0 6 0=rawCoordinate 0 0 6 := by
    rw [rawCoordinate_sparse 0 6 0 rawEntry_0_00_06 rawEntry_0_06_00_data,rawCoordinate_sparse 0 0 6 rawEntry_0_00_06 rawEntry_0_00_06_data]
  rw [hh,rawEntry_0_00_06_physical]
  exact kernelRPolynomial_index_symm 0 0 6
def rawEntry_0_01_01 : SparseEntry := [(0,3),(1,14),(2,28),(3,7)]
theorem rawEntry_0_01_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 1=sparseCoefficient rawEntry_0_01_01 r := by decide +kernel
theorem rawEntry_0_01_01_coordinates : sparsePolynomial 21 rawEntry_0_01_01=r0Coordinates 1 1 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_01,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_01_physical : invariantSubst (rawCoordinate 0 1 1)=kernelRPolynomial 0 1 1 := by
  rw [rawCoordinate_sparse 0 1 1 rawEntry_0_01_01 rawEntry_0_01_01_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_01)=_
  rw [rawEntry_0_01_01_coordinates]
  exact r0Coordinates_subst 1 1
def rawEntry_0_01_02 : SparseEntry := [(0,3),(1,7),(2,-14),(3,7),(4,-42),(6,7)]
theorem rawEntry_0_01_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 2=sparseCoefficient rawEntry_0_01_02 r := by decide +kernel
theorem rawEntry_0_01_02_coordinates : sparsePolynomial 21 rawEntry_0_01_02=r0Coordinates 1 2 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_02_physical : invariantSubst (rawCoordinate 0 1 2)=kernelRPolynomial 0 1 2 := by
  rw [rawCoordinate_sparse 0 1 2 rawEntry_0_01_02 rawEntry_0_01_02_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_02)=_
  rw [rawEntry_0_01_02_coordinates]
  exact r0Coordinates_subst 1 2
theorem rawEntry_0_02_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 1=sparseCoefficient rawEntry_0_01_02 r := by decide +kernel
theorem rawEntry_0_02_01_physical : invariantSubst (rawCoordinate 0 2 1)=kernelRPolynomial 0 2 1 := by
  have hh : rawCoordinate 0 2 1=rawCoordinate 0 1 2 := by
    rw [rawCoordinate_sparse 0 2 1 rawEntry_0_01_02 rawEntry_0_02_01_data,rawCoordinate_sparse 0 1 2 rawEntry_0_01_02 rawEntry_0_01_02_data]
  rw [hh,rawEntry_0_01_02_physical]
  exact kernelRPolynomial_index_symm 0 1 2
def rawEntry_0_01_03 : SparseEntry := [(0,3),(1,7),(4,21),(5,-21),(6,7),(7,-28),(8,7),(9,-7),(10,7)]
theorem rawEntry_0_01_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 3=sparseCoefficient rawEntry_0_01_03 r := by decide +kernel
theorem rawEntry_0_01_03_coordinates : sparsePolynomial 21 rawEntry_0_01_03=r0Coordinates 1 3 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_03_physical : invariantSubst (rawCoordinate 0 1 3)=kernelRPolynomial 0 1 3 := by
  rw [rawCoordinate_sparse 0 1 3 rawEntry_0_01_03 rawEntry_0_01_03_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_03)=_
  rw [rawEntry_0_01_03_coordinates]
  exact r0Coordinates_subst 1 3
theorem rawEntry_0_03_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 1=sparseCoefficient rawEntry_0_01_03 r := by decide +kernel
theorem rawEntry_0_03_01_physical : invariantSubst (rawCoordinate 0 3 1)=kernelRPolynomial 0 3 1 := by
  have hh : rawCoordinate 0 3 1=rawCoordinate 0 1 3 := by
    rw [rawCoordinate_sparse 0 3 1 rawEntry_0_01_03 rawEntry_0_03_01_data,rawCoordinate_sparse 0 1 3 rawEntry_0_01_03 rawEntry_0_01_03_data]
  rw [hh,rawEntry_0_01_03_physical]
  exact kernelRPolynomial_index_symm 0 1 3
def rawEntry_0_01_04 : SparseEntry := [(0,3),(1,7),(7,14),(8,28),(9,-28),(10,7),(11,70),(12,-28),(13,14),(14,-14),(15,7)]
theorem rawEntry_0_01_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 4=sparseCoefficient rawEntry_0_01_04 r := by decide +kernel
theorem rawEntry_0_01_04_coordinates : sparsePolynomial 21 rawEntry_0_01_04=r0Coordinates 1 4 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_04_physical : invariantSubst (rawCoordinate 0 1 4)=kernelRPolynomial 0 1 4 := by
  rw [rawCoordinate_sparse 0 1 4 rawEntry_0_01_04 rawEntry_0_01_04_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_04)=_
  rw [rawEntry_0_01_04_coordinates]
  exact r0Coordinates_subst 1 4
theorem rawEntry_0_04_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 1=sparseCoefficient rawEntry_0_01_04 r := by decide +kernel
theorem rawEntry_0_04_01_physical : invariantSubst (rawCoordinate 0 4 1)=kernelRPolynomial 0 4 1 := by
  have hh : rawCoordinate 0 4 1=rawCoordinate 0 1 4 := by
    rw [rawCoordinate_sparse 0 4 1 rawEntry_0_01_04 rawEntry_0_04_01_data,rawCoordinate_sparse 0 1 4 rawEntry_0_01_04 rawEntry_0_01_04_data]
  rw [hh,rawEntry_0_01_04_physical]
  exact kernelRPolynomial_index_symm 0 1 4
def rawEntry_0_01_05 : SparseEntry := [(0,3),(1,7),(11,-35),(12,35),(13,35),(14,-35),(15,7),(16,-42),(17,28),(18,63),(19,-21),(20,21),(21,-21),(22,7)]
theorem rawEntry_0_01_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 5=sparseCoefficient rawEntry_0_01_05 r := by decide +kernel
theorem rawEntry_0_01_05_coordinates : sparsePolynomial 21 rawEntry_0_01_05=r0Coordinates 1 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_05_physical : invariantSubst (rawCoordinate 0 1 5)=kernelRPolynomial 0 1 5 := by
  rw [rawCoordinate_sparse 0 1 5 rawEntry_0_01_05 rawEntry_0_01_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_05)=_
  rw [rawEntry_0_01_05_coordinates]
  exact r0Coordinates_subst 1 5
theorem rawEntry_0_05_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 1=sparseCoefficient rawEntry_0_01_05 r := by decide +kernel
theorem rawEntry_0_05_01_physical : invariantSubst (rawCoordinate 0 5 1)=kernelRPolynomial 0 5 1 := by
  have hh : rawCoordinate 0 5 1=rawCoordinate 0 1 5 := by
    rw [rawCoordinate_sparse 0 5 1 rawEntry_0_01_05 rawEntry_0_05_01_data,rawCoordinate_sparse 0 1 5 rawEntry_0_01_05 rawEntry_0_01_05_data]
  rw [hh,rawEntry_0_01_05_physical]
  exact kernelRPolynomial_index_symm 0 1 5
def rawEntry_0_01_06 : SparseEntry := [(0,3),(1,7),(16,21),(17,-14),(18,-84),(19,63),(20,42),(21,-42),(22,7),(23,-98),(24,-35),(25,56),(26,42),(27,-7),(28,28),(29,-28),(30,7)]
theorem rawEntry_0_01_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 1 6=sparseCoefficient rawEntry_0_01_06 r := by decide +kernel
theorem rawEntry_0_01_06_coordinates : sparsePolynomial 21 rawEntry_0_01_06=r0Coordinates 1 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_01_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_01_06_physical : invariantSubst (rawCoordinate 0 1 6)=kernelRPolynomial 0 1 6 := by
  rw [rawCoordinate_sparse 0 1 6 rawEntry_0_01_06 rawEntry_0_01_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_01_06)=_
  rw [rawEntry_0_01_06_coordinates]
  exact r0Coordinates_subst 1 6
theorem rawEntry_0_06_01_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 1=sparseCoefficient rawEntry_0_01_06 r := by decide +kernel
theorem rawEntry_0_06_01_physical : invariantSubst (rawCoordinate 0 6 1)=kernelRPolynomial 0 6 1 := by
  have hh : rawCoordinate 0 6 1=rawCoordinate 0 1 6 := by
    rw [rawCoordinate_sparse 0 6 1 rawEntry_0_01_06 rawEntry_0_06_01_data,rawCoordinate_sparse 0 1 6 rawEntry_0_01_06 rawEntry_0_01_06_data]
  rw [hh,rawEntry_0_01_06_physical]
  exact kernelRPolynomial_index_symm 0 1 6
def rawEntry_0_02_02 : SparseEntry := [(0,3),(2,-28),(3,14),(7,56),(8,-56),(9,-28),(10,7)]
theorem rawEntry_0_02_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 2=sparseCoefficient rawEntry_0_02_02 r := by decide +kernel
theorem rawEntry_0_02_02_coordinates : sparsePolynomial 21 rawEntry_0_02_02=r0Coordinates 2 2 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_02_02,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_02_02_physical : invariantSubst (rawCoordinate 0 2 2)=kernelRPolynomial 0 2 2 := by
  rw [rawCoordinate_sparse 0 2 2 rawEntry_0_02_02 rawEntry_0_02_02_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_02_02)=_
  rw [rawEntry_0_02_02_coordinates]
  exact r0Coordinates_subst 2 2
def rawEntry_0_02_03 : SparseEntry := [(0,3),(2,-14),(3,7),(4,21),(5,-21),(6,7),(11,-56),(12,56),(13,-7),(14,-35),(15,7)]
theorem rawEntry_0_02_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 3=sparseCoefficient rawEntry_0_02_03 r := by decide +kernel
theorem rawEntry_0_02_03_coordinates : sparsePolynomial 21 rawEntry_0_02_03=r0Coordinates 2 3 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_02_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_02_03_physical : invariantSubst (rawCoordinate 0 2 3)=kernelRPolynomial 0 2 3 := by
  rw [rawCoordinate_sparse 0 2 3 rawEntry_0_02_03 rawEntry_0_02_03_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_02_03)=_
  rw [rawEntry_0_02_03_coordinates]
  exact r0Coordinates_subst 2 3
theorem rawEntry_0_03_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 2=sparseCoefficient rawEntry_0_02_03 r := by decide +kernel
theorem rawEntry_0_03_02_physical : invariantSubst (rawCoordinate 0 3 2)=kernelRPolynomial 0 3 2 := by
  have hh : rawCoordinate 0 3 2=rawCoordinate 0 2 3 := by
    rw [rawCoordinate_sparse 0 3 2 rawEntry_0_02_03 rawEntry_0_03_02_data,rawCoordinate_sparse 0 2 3 rawEntry_0_02_03 rawEntry_0_02_03_data]
  rw [hh,rawEntry_0_02_03_physical]
  exact kernelRPolynomial_index_symm 0 2 3
def rawEntry_0_02_04 : SparseEntry := [(0,3),(2,-14),(3,7),(7,14),(8,28),(9,-28),(10,7),(16,-42),(17,-56),(19,84),(21,-42),(22,7)]
theorem rawEntry_0_02_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 4=sparseCoefficient rawEntry_0_02_04 r := by decide +kernel
theorem rawEntry_0_02_04_coordinates : sparsePolynomial 21 rawEntry_0_02_04=r0Coordinates 2 4 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_02_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_02_04_physical : invariantSubst (rawCoordinate 0 2 4)=kernelRPolynomial 0 2 4 := by
  rw [rawCoordinate_sparse 0 2 4 rawEntry_0_02_04 rawEntry_0_02_04_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_02_04)=_
  rw [rawEntry_0_02_04_coordinates]
  exact r0Coordinates_subst 2 4
theorem rawEntry_0_04_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 2=sparseCoefficient rawEntry_0_02_04 r := by decide +kernel
theorem rawEntry_0_04_02_physical : invariantSubst (rawCoordinate 0 4 2)=kernelRPolynomial 0 4 2 := by
  have hh : rawCoordinate 0 4 2=rawCoordinate 0 2 4 := by
    rw [rawCoordinate_sparse 0 4 2 rawEntry_0_02_04 rawEntry_0_04_02_data,rawCoordinate_sparse 0 2 4 rawEntry_0_02_04 rawEntry_0_02_04_data]
  rw [hh,rawEntry_0_02_04_physical]
  exact kernelRPolynomial_index_symm 0 2 4
def rawEntry_0_02_05 : SparseEntry := [(0,3),(2,-14),(3,7),(11,-35),(12,35),(13,35),(14,-35),(15,7),(23,112),(24,-98),(25,-112),(26,-21),(27,119),(28,7),(29,-49),(30,7)]
theorem rawEntry_0_02_05_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 5=sparseCoefficient rawEntry_0_02_05 r := by decide +kernel
theorem rawEntry_0_02_05_coordinates : sparsePolynomial 21 rawEntry_0_02_05=r0Coordinates 2 5 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_02_05,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_02_05_physical : invariantSubst (rawCoordinate 0 2 5)=kernelRPolynomial 0 2 5 := by
  rw [rawCoordinate_sparse 0 2 5 rawEntry_0_02_05 rawEntry_0_02_05_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_02_05)=_
  rw [rawEntry_0_02_05_coordinates]
  exact r0Coordinates_subst 2 5
theorem rawEntry_0_05_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 5 2=sparseCoefficient rawEntry_0_02_05 r := by decide +kernel
theorem rawEntry_0_05_02_physical : invariantSubst (rawCoordinate 0 5 2)=kernelRPolynomial 0 5 2 := by
  have hh : rawCoordinate 0 5 2=rawCoordinate 0 2 5 := by
    rw [rawCoordinate_sparse 0 5 2 rawEntry_0_02_05 rawEntry_0_05_02_data,rawCoordinate_sparse 0 2 5 rawEntry_0_02_05 rawEntry_0_02_05_data]
  rw [hh,rawEntry_0_02_05_physical]
  exact kernelRPolynomial_index_symm 0 2 5
def rawEntry_0_02_06 : SparseEntry := [(0,3),(2,-14),(3,7),(16,21),(17,-14),(18,-84),(19,63),(20,42),(21,-42),(22,7),(31,-14),(32,56),(33,168),(34,-105),(35,-196),(36,-56),(37,161),(38,14),(39,-56),(40,7)]
theorem rawEntry_0_02_06_data : ∀r : Fin 102, RawData.coefficient 0 r.val 2 6=sparseCoefficient rawEntry_0_02_06 r := by decide +kernel
theorem rawEntry_0_02_06_coordinates : sparsePolynomial 21 rawEntry_0_02_06=r0Coordinates 2 6 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_02_06,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_02_06_physical : invariantSubst (rawCoordinate 0 2 6)=kernelRPolynomial 0 2 6 := by
  rw [rawCoordinate_sparse 0 2 6 rawEntry_0_02_06 rawEntry_0_02_06_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_02_06)=_
  rw [rawEntry_0_02_06_coordinates]
  exact r0Coordinates_subst 2 6
theorem rawEntry_0_06_02_data : ∀r : Fin 102, RawData.coefficient 0 r.val 6 2=sparseCoefficient rawEntry_0_02_06 r := by decide +kernel
theorem rawEntry_0_06_02_physical : invariantSubst (rawCoordinate 0 6 2)=kernelRPolynomial 0 6 2 := by
  have hh : rawCoordinate 0 6 2=rawCoordinate 0 2 6 := by
    rw [rawCoordinate_sparse 0 6 2 rawEntry_0_02_06 rawEntry_0_06_02_data,rawCoordinate_sparse 0 2 6 rawEntry_0_02_06 rawEntry_0_02_06_data]
  rw [hh,rawEntry_0_02_06_physical]
  exact kernelRPolynomial_index_symm 0 2 6
def rawEntry_0_03_03 : SparseEntry := [(0,3),(4,42),(5,-42),(6,14),(16,147),(17,28),(18,-210),(19,63),(20,42),(21,-42),(22,7)]
theorem rawEntry_0_03_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 3=sparseCoefficient rawEntry_0_03_03 r := by decide +kernel
theorem rawEntry_0_03_03_coordinates : sparsePolynomial 21 rawEntry_0_03_03=r0Coordinates 3 3 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_03_03,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_03_03_physical : invariantSubst (rawCoordinate 0 3 3)=kernelRPolynomial 0 3 3 := by
  rw [rawCoordinate_sparse 0 3 3 rawEntry_0_03_03 rawEntry_0_03_03_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_03_03)=_
  rw [rawEntry_0_03_03_coordinates]
  exact r0Coordinates_subst 3 3
def rawEntry_0_03_04 : SparseEntry := [(0,3),(4,21),(5,-21),(6,7),(7,14),(8,28),(9,-28),(10,7),(23,28),(24,154),(25,-28),(26,-210),(27,98),(28,49),(29,-49),(30,7)]
theorem rawEntry_0_03_04_data : ∀r : Fin 102, RawData.coefficient 0 r.val 3 4=sparseCoefficient rawEntry_0_03_04 r := by decide +kernel
theorem rawEntry_0_03_04_coordinates : sparsePolynomial 21 rawEntry_0_03_04=r0Coordinates 3 4 := by
  norm_num only [r0Coordinates]
  simp only [← powerTable00_eq,← powerTable01_eq,← powerTable02_eq,← powerTable03_eq,← powerTable04_eq,← powerTable05_eq,← powerTable06_eq,← powerTable07_eq,← powerTable08_eq,← powerTable09_eq,← powerTable10_eq,← powerTable11_eq,← powerTable12_eq]
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_0_03_04,coordinateMonomial,powerTable00,powerTable01,powerTable02,powerTable03,powerTable04,powerTable05,powerTable06,powerTable07,powerTable08,powerTable09,powerTable10,powerTable11,powerTable12] <;> ring
theorem rawEntry_0_03_04_physical : invariantSubst (rawCoordinate 0 3 4)=kernelRPolynomial 0 3 4 := by
  rw [rawCoordinate_sparse 0 3 4 rawEntry_0_03_04 rawEntry_0_03_04_data]
  change invariantSubst (sparsePolynomial 21 rawEntry_0_03_04)=_
  rw [rawEntry_0_03_04_coordinates]
  exact r0Coordinates_subst 3 4
theorem rawEntry_0_04_03_data : ∀r : Fin 102, RawData.coefficient 0 r.val 4 3=sparseCoefficient rawEntry_0_03_04 r := by decide +kernel
theorem rawEntry_0_04_03_physical : invariantSubst (rawCoordinate 0 4 3)=kernelRPolynomial 0 4 3 := by
  have hh : rawCoordinate 0 4 3=rawCoordinate 0 3 4 := by
    rw [rawCoordinate_sparse 0 4 3 rawEntry_0_03_04 rawEntry_0_04_03_data,rawCoordinate_sparse 0 3 4 rawEntry_0_03_04 rawEntry_0_03_04_data]
  rw [hh,rawEntry_0_03_04_physical]
  exact kernelRPolynomial_index_symm 0 3 4
end ThomsonNegative.Certificate.Bridges
