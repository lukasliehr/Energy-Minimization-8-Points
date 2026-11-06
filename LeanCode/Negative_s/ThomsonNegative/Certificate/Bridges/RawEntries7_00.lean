import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_00_00 : SparseEntry := [(2,-108),(3,36)]
theorem rawEntry_7_00_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 0=sparseCoefficient rawEntry_7_00_00 r := by decide +kernel
theorem rawEntry_7_00_00_coordinates : sparsePolynomial 81 rawEntry_7_00_00=rawStandardCoordinates 0 0 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_00,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_00_physical : invariantSubst (rawCoordinate 7 0 0)=rawStandardPolynomial 0 0 := by
  rw [rawCoordinate_sparse 7 0 0 rawEntry_7_00_00 rawEntry_7_00_00_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_00)=_
  rw [rawEntry_7_00_00_coordinates]
  exact rawStandard_subst 0 0
def rawEntry_7_00_01 : SparseEntry := [(5,-108),(6,36)]
theorem rawEntry_7_00_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 1=sparseCoefficient rawEntry_7_00_01 r := by decide +kernel
theorem rawEntry_7_00_01_coordinates : sparsePolynomial 81 rawEntry_7_00_01=rawStandardCoordinates 0 1 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_01,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_01_physical : invariantSubst (rawCoordinate 7 0 1)=rawStandardPolynomial 0 1 := by
  rw [rawCoordinate_sparse 7 0 1 rawEntry_7_00_01 rawEntry_7_00_01_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_01)=_
  rw [rawEntry_7_00_01_coordinates]
  exact rawStandard_subst 0 1
theorem rawEntry_7_01_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 0=sparseCoefficient rawEntry_7_00_01 r := by decide +kernel
theorem rawEntry_7_01_00_physical : invariantSubst (rawCoordinate 7 1 0)=rawStandardPolynomial 1 0 := by
  have hh : rawCoordinate 7 1 0=rawCoordinate 7 0 1 := by
    rw [rawCoordinate_sparse 7 1 0 rawEntry_7_00_01 rawEntry_7_01_00_data,rawCoordinate_sparse 7 0 1 rawEntry_7_00_01 rawEntry_7_00_01_data]
  rw [hh,rawEntry_7_00_01_physical]
  exact rawStandardPolynomial_symm 0 1
def rawEntry_7_00_02 : SparseEntry := [(7,-108),(9,36)]
theorem rawEntry_7_00_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 2=sparseCoefficient rawEntry_7_00_02 r := by decide +kernel
theorem rawEntry_7_00_02_coordinates : sparsePolynomial 81 rawEntry_7_00_02=rawStandardCoordinates 0 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_02,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_02_physical : invariantSubst (rawCoordinate 7 0 2)=rawStandardPolynomial 0 2 := by
  rw [rawCoordinate_sparse 7 0 2 rawEntry_7_00_02 rawEntry_7_00_02_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_02)=_
  rw [rawEntry_7_00_02_coordinates]
  exact rawStandard_subst 0 2
theorem rawEntry_7_02_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 0=sparseCoefficient rawEntry_7_00_02 r := by decide +kernel
theorem rawEntry_7_02_00_physical : invariantSubst (rawCoordinate 7 2 0)=rawStandardPolynomial 2 0 := by
  have hh : rawCoordinate 7 2 0=rawCoordinate 7 0 2 := by
    rw [rawCoordinate_sparse 7 2 0 rawEntry_7_00_02 rawEntry_7_02_00_data,rawCoordinate_sparse 7 0 2 rawEntry_7_00_02 rawEntry_7_00_02_data]
  rw [hh,rawEntry_7_00_02_physical]
  exact rawStandardPolynomial_symm 0 2
def rawEntry_7_00_03 : SparseEntry := [(9,-108),(10,36)]
theorem rawEntry_7_00_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 3=sparseCoefficient rawEntry_7_00_03 r := by decide +kernel
theorem rawEntry_7_00_03_coordinates : sparsePolynomial 81 rawEntry_7_00_03=rawStandardCoordinates 0 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_03,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_03_physical : invariantSubst (rawCoordinate 7 0 3)=rawStandardPolynomial 0 3 := by
  rw [rawCoordinate_sparse 7 0 3 rawEntry_7_00_03 rawEntry_7_00_03_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_03)=_
  rw [rawEntry_7_00_03_coordinates]
  exact rawStandard_subst 0 3
theorem rawEntry_7_03_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 0=sparseCoefficient rawEntry_7_00_03 r := by decide +kernel
theorem rawEntry_7_03_00_physical : invariantSubst (rawCoordinate 7 3 0)=rawStandardPolynomial 3 0 := by
  have hh : rawCoordinate 7 3 0=rawCoordinate 7 0 3 := by
    rw [rawCoordinate_sparse 7 3 0 rawEntry_7_00_03 rawEntry_7_03_00_data,rawCoordinate_sparse 7 0 3 rawEntry_7_00_03 rawEntry_7_00_03_data]
  rw [hh,rawEntry_7_00_03_physical]
  exact rawStandardPolynomial_symm 0 3
def rawEntry_7_00_04 : SparseEntry := [(11,-108),(13,36)]
theorem rawEntry_7_00_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 4=sparseCoefficient rawEntry_7_00_04 r := by decide +kernel
theorem rawEntry_7_00_04_coordinates : sparsePolynomial 81 rawEntry_7_00_04=rawStandardCoordinates 0 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_04,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_04_physical : invariantSubst (rawCoordinate 7 0 4)=rawStandardPolynomial 0 4 := by
  rw [rawCoordinate_sparse 7 0 4 rawEntry_7_00_04 rawEntry_7_00_04_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_04)=_
  rw [rawEntry_7_00_04_coordinates]
  exact rawStandard_subst 0 4
theorem rawEntry_7_04_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 0=sparseCoefficient rawEntry_7_00_04 r := by decide +kernel
theorem rawEntry_7_04_00_physical : invariantSubst (rawCoordinate 7 4 0)=rawStandardPolynomial 4 0 := by
  have hh : rawCoordinate 7 4 0=rawCoordinate 7 0 4 := by
    rw [rawCoordinate_sparse 7 4 0 rawEntry_7_00_04 rawEntry_7_04_00_data,rawCoordinate_sparse 7 0 4 rawEntry_7_00_04 rawEntry_7_00_04_data]
  rw [hh,rawEntry_7_00_04_physical]
  exact rawStandardPolynomial_symm 0 4
def rawEntry_7_00_05 : SparseEntry := [(12,-108),(14,36)]
theorem rawEntry_7_00_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 5=sparseCoefficient rawEntry_7_00_05 r := by decide +kernel
theorem rawEntry_7_00_05_coordinates : sparsePolynomial 81 rawEntry_7_00_05=rawStandardCoordinates 0 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_05_physical : invariantSubst (rawCoordinate 7 0 5)=rawStandardPolynomial 0 5 := by
  rw [rawCoordinate_sparse 7 0 5 rawEntry_7_00_05 rawEntry_7_00_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_05)=_
  rw [rawEntry_7_00_05_coordinates]
  exact rawStandard_subst 0 5
theorem rawEntry_7_05_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 0=sparseCoefficient rawEntry_7_00_05 r := by decide +kernel
theorem rawEntry_7_05_00_physical : invariantSubst (rawCoordinate 7 5 0)=rawStandardPolynomial 5 0 := by
  have hh : rawCoordinate 7 5 0=rawCoordinate 7 0 5 := by
    rw [rawCoordinate_sparse 7 5 0 rawEntry_7_00_05 rawEntry_7_05_00_data,rawCoordinate_sparse 7 0 5 rawEntry_7_00_05 rawEntry_7_00_05_data]
  rw [hh,rawEntry_7_00_05_physical]
  exact rawStandardPolynomial_symm 0 5
def rawEntry_7_00_06 : SparseEntry := [(14,-108),(15,36)]
theorem rawEntry_7_00_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 6=sparseCoefficient rawEntry_7_00_06 r := by decide +kernel
theorem rawEntry_7_00_06_coordinates : sparsePolynomial 81 rawEntry_7_00_06=rawStandardCoordinates 0 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_06_physical : invariantSubst (rawCoordinate 7 0 6)=rawStandardPolynomial 0 6 := by
  rw [rawCoordinate_sparse 7 0 6 rawEntry_7_00_06 rawEntry_7_00_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_06)=_
  rw [rawEntry_7_00_06_coordinates]
  exact rawStandard_subst 0 6
theorem rawEntry_7_06_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 0=sparseCoefficient rawEntry_7_00_06 r := by decide +kernel
theorem rawEntry_7_06_00_physical : invariantSubst (rawCoordinate 7 6 0)=rawStandardPolynomial 6 0 := by
  have hh : rawCoordinate 7 6 0=rawCoordinate 7 0 6 := by
    rw [rawCoordinate_sparse 7 6 0 rawEntry_7_00_06 rawEntry_7_06_00_data,rawCoordinate_sparse 7 0 6 rawEntry_7_00_06 rawEntry_7_00_06_data]
  rw [hh,rawEntry_7_00_06_physical]
  exact rawStandardPolynomial_symm 0 6
def rawEntry_7_00_07 : SparseEntry := [(17,-108),(19,36)]
theorem rawEntry_7_00_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 7=sparseCoefficient rawEntry_7_00_07 r := by decide +kernel
theorem rawEntry_7_00_07_coordinates : sparsePolynomial 81 rawEntry_7_00_07=rawStandardCoordinates 0 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_07_physical : invariantSubst (rawCoordinate 7 0 7)=rawStandardPolynomial 0 7 := by
  rw [rawCoordinate_sparse 7 0 7 rawEntry_7_00_07 rawEntry_7_00_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_07)=_
  rw [rawEntry_7_00_07_coordinates]
  exact rawStandard_subst 0 7
theorem rawEntry_7_07_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 0=sparseCoefficient rawEntry_7_00_07 r := by decide +kernel
theorem rawEntry_7_07_00_physical : invariantSubst (rawCoordinate 7 7 0)=rawStandardPolynomial 7 0 := by
  have hh : rawCoordinate 7 7 0=rawCoordinate 7 0 7 := by
    rw [rawCoordinate_sparse 7 7 0 rawEntry_7_00_07 rawEntry_7_07_00_data,rawCoordinate_sparse 7 0 7 rawEntry_7_00_07 rawEntry_7_00_07_data]
  rw [hh,rawEntry_7_00_07_physical]
  exact rawStandardPolynomial_symm 0 7
def rawEntry_7_00_08 : SparseEntry := [(18,-108),(20,36)]
theorem rawEntry_7_00_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 8=sparseCoefficient rawEntry_7_00_08 r := by decide +kernel
theorem rawEntry_7_00_08_coordinates : sparsePolynomial 81 rawEntry_7_00_08=rawStandardCoordinates 0 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_08_physical : invariantSubst (rawCoordinate 7 0 8)=rawStandardPolynomial 0 8 := by
  rw [rawCoordinate_sparse 7 0 8 rawEntry_7_00_08 rawEntry_7_00_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_08)=_
  rw [rawEntry_7_00_08_coordinates]
  exact rawStandard_subst 0 8
theorem rawEntry_7_08_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 0=sparseCoefficient rawEntry_7_00_08 r := by decide +kernel
theorem rawEntry_7_08_00_physical : invariantSubst (rawCoordinate 7 8 0)=rawStandardPolynomial 8 0 := by
  have hh : rawCoordinate 7 8 0=rawCoordinate 7 0 8 := by
    rw [rawCoordinate_sparse 7 8 0 rawEntry_7_00_08 rawEntry_7_08_00_data,rawCoordinate_sparse 7 0 8 rawEntry_7_00_08 rawEntry_7_00_08_data]
  rw [hh,rawEntry_7_00_08_physical]
  exact rawStandardPolynomial_symm 0 8
def rawEntry_7_00_09 : SparseEntry := [(19,-108),(21,36)]
theorem rawEntry_7_00_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 9=sparseCoefficient rawEntry_7_00_09 r := by decide +kernel
theorem rawEntry_7_00_09_coordinates : sparsePolynomial 81 rawEntry_7_00_09=rawStandardCoordinates 0 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_09_physical : invariantSubst (rawCoordinate 7 0 9)=rawStandardPolynomial 0 9 := by
  rw [rawCoordinate_sparse 7 0 9 rawEntry_7_00_09 rawEntry_7_00_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_09)=_
  rw [rawEntry_7_00_09_coordinates]
  exact rawStandard_subst 0 9
theorem rawEntry_7_09_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 0=sparseCoefficient rawEntry_7_00_09 r := by decide +kernel
theorem rawEntry_7_09_00_physical : invariantSubst (rawCoordinate 7 9 0)=rawStandardPolynomial 9 0 := by
  have hh : rawCoordinate 7 9 0=rawCoordinate 7 0 9 := by
    rw [rawCoordinate_sparse 7 9 0 rawEntry_7_00_09 rawEntry_7_09_00_data,rawCoordinate_sparse 7 0 9 rawEntry_7_00_09 rawEntry_7_00_09_data]
  rw [hh,rawEntry_7_00_09_physical]
  exact rawStandardPolynomial_symm 0 9
def rawEntry_7_00_10 : SparseEntry := [(21,-108),(22,36)]
theorem rawEntry_7_00_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 10=sparseCoefficient rawEntry_7_00_10 r := by decide +kernel
theorem rawEntry_7_00_10_coordinates : sparsePolynomial 81 rawEntry_7_00_10=rawStandardCoordinates 0 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_10_physical : invariantSubst (rawCoordinate 7 0 10)=rawStandardPolynomial 0 10 := by
  rw [rawCoordinate_sparse 7 0 10 rawEntry_7_00_10 rawEntry_7_00_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_10)=_
  rw [rawEntry_7_00_10_coordinates]
  exact rawStandard_subst 0 10
theorem rawEntry_7_10_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 0=sparseCoefficient rawEntry_7_00_10 r := by decide +kernel
theorem rawEntry_7_10_00_physical : invariantSubst (rawCoordinate 7 10 0)=rawStandardPolynomial 10 0 := by
  have hh : rawCoordinate 7 10 0=rawCoordinate 7 0 10 := by
    rw [rawCoordinate_sparse 7 10 0 rawEntry_7_00_10 rawEntry_7_10_00_data,rawCoordinate_sparse 7 0 10 rawEntry_7_00_10 rawEntry_7_00_10_data]
  rw [hh,rawEntry_7_00_10_physical]
  exact rawStandardPolynomial_symm 0 10
def rawEntry_7_00_11 : SparseEntry := [(4,162),(5,-54),(6,12)]
theorem rawEntry_7_00_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 11=sparseCoefficient rawEntry_7_00_11 r := by decide +kernel
theorem rawEntry_7_00_11_coordinates : sparsePolynomial 81 rawEntry_7_00_11=rawStandardCoordinates 0 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_11_physical : invariantSubst (rawCoordinate 7 0 11)=rawStandardPolynomial 0 11 := by
  rw [rawCoordinate_sparse 7 0 11 rawEntry_7_00_11 rawEntry_7_00_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_11)=_
  rw [rawEntry_7_00_11_coordinates]
  exact rawStandard_subst 0 11
theorem rawEntry_7_11_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 0=sparseCoefficient rawEntry_7_00_11 r := by decide +kernel
theorem rawEntry_7_11_00_physical : invariantSubst (rawCoordinate 7 11 0)=rawStandardPolynomial 11 0 := by
  have hh : rawCoordinate 7 11 0=rawCoordinate 7 0 11 := by
    rw [rawCoordinate_sparse 7 11 0 rawEntry_7_00_11 rawEntry_7_11_00_data,rawCoordinate_sparse 7 0 11 rawEntry_7_00_11 rawEntry_7_00_11_data]
  rw [hh,rawEntry_7_00_11_physical]
  exact rawStandardPolynomial_symm 0 11
def rawEntry_7_00_12 : SparseEntry := [(8,162),(9,-54),(10,12)]
theorem rawEntry_7_00_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 12=sparseCoefficient rawEntry_7_00_12 r := by decide +kernel
theorem rawEntry_7_00_12_coordinates : sparsePolynomial 81 rawEntry_7_00_12=rawStandardCoordinates 0 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_12_physical : invariantSubst (rawCoordinate 7 0 12)=rawStandardPolynomial 0 12 := by
  rw [rawCoordinate_sparse 7 0 12 rawEntry_7_00_12 rawEntry_7_00_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_12)=_
  rw [rawEntry_7_00_12_coordinates]
  exact rawStandard_subst 0 12
theorem rawEntry_7_12_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 0=sparseCoefficient rawEntry_7_00_12 r := by decide +kernel
theorem rawEntry_7_12_00_physical : invariantSubst (rawCoordinate 7 12 0)=rawStandardPolynomial 12 0 := by
  have hh : rawCoordinate 7 12 0=rawCoordinate 7 0 12 := by
    rw [rawCoordinate_sparse 7 12 0 rawEntry_7_00_12 rawEntry_7_12_00_data,rawCoordinate_sparse 7 0 12 rawEntry_7_00_12 rawEntry_7_00_12_data]
  rw [hh,rawEntry_7_00_12_physical]
  exact rawStandardPolynomial_symm 0 12
def rawEntry_7_00_13 : SparseEntry := [(11,162),(12,-54),(14,12)]
theorem rawEntry_7_00_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 13=sparseCoefficient rawEntry_7_00_13 r := by decide +kernel
theorem rawEntry_7_00_13_coordinates : sparsePolynomial 81 rawEntry_7_00_13=rawStandardCoordinates 0 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_13_physical : invariantSubst (rawCoordinate 7 0 13)=rawStandardPolynomial 0 13 := by
  rw [rawCoordinate_sparse 7 0 13 rawEntry_7_00_13 rawEntry_7_00_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_13)=_
  rw [rawEntry_7_00_13_coordinates]
  exact rawStandard_subst 0 13
theorem rawEntry_7_13_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 0=sparseCoefficient rawEntry_7_00_13 r := by decide +kernel
theorem rawEntry_7_13_00_physical : invariantSubst (rawCoordinate 7 13 0)=rawStandardPolynomial 13 0 := by
  have hh : rawCoordinate 7 13 0=rawCoordinate 7 0 13 := by
    rw [rawCoordinate_sparse 7 13 0 rawEntry_7_00_13 rawEntry_7_13_00_data,rawCoordinate_sparse 7 0 13 rawEntry_7_00_13 rawEntry_7_00_13_data]
  rw [hh,rawEntry_7_00_13_physical]
  exact rawStandardPolynomial_symm 0 13
def rawEntry_7_00_14 : SparseEntry := [(13,162),(14,-54),(15,12)]
theorem rawEntry_7_00_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 14=sparseCoefficient rawEntry_7_00_14 r := by decide +kernel
theorem rawEntry_7_00_14_coordinates : sparsePolynomial 81 rawEntry_7_00_14=rawStandardCoordinates 0 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_14_physical : invariantSubst (rawCoordinate 7 0 14)=rawStandardPolynomial 0 14 := by
  rw [rawCoordinate_sparse 7 0 14 rawEntry_7_00_14 rawEntry_7_00_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_14)=_
  rw [rawEntry_7_00_14_coordinates]
  exact rawStandard_subst 0 14
theorem rawEntry_7_14_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 0=sparseCoefficient rawEntry_7_00_14 r := by decide +kernel
theorem rawEntry_7_14_00_physical : invariantSubst (rawCoordinate 7 14 0)=rawStandardPolynomial 14 0 := by
  have hh : rawCoordinate 7 14 0=rawCoordinate 7 0 14 := by
    rw [rawCoordinate_sparse 7 14 0 rawEntry_7_00_14 rawEntry_7_14_00_data,rawCoordinate_sparse 7 0 14 rawEntry_7_00_14 rawEntry_7_00_14_data]
  rw [hh,rawEntry_7_00_14_physical]
  exact rawStandardPolynomial_symm 0 14
def rawEntry_7_00_15 : SparseEntry := [(16,162),(18,-54),(20,12)]
theorem rawEntry_7_00_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 15=sparseCoefficient rawEntry_7_00_15 r := by decide +kernel
theorem rawEntry_7_00_15_coordinates : sparsePolynomial 81 rawEntry_7_00_15=rawStandardCoordinates 0 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_15_physical : invariantSubst (rawCoordinate 7 0 15)=rawStandardPolynomial 0 15 := by
  rw [rawCoordinate_sparse 7 0 15 rawEntry_7_00_15 rawEntry_7_00_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_15)=_
  rw [rawEntry_7_00_15_coordinates]
  exact rawStandard_subst 0 15
theorem rawEntry_7_15_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 0=sparseCoefficient rawEntry_7_00_15 r := by decide +kernel
theorem rawEntry_7_15_00_physical : invariantSubst (rawCoordinate 7 15 0)=rawStandardPolynomial 15 0 := by
  have hh : rawCoordinate 7 15 0=rawCoordinate 7 0 15 := by
    rw [rawCoordinate_sparse 7 15 0 rawEntry_7_00_15 rawEntry_7_15_00_data,rawCoordinate_sparse 7 0 15 rawEntry_7_00_15 rawEntry_7_00_15_data]
  rw [hh,rawEntry_7_00_15_physical]
  exact rawStandardPolynomial_symm 0 15
def rawEntry_7_00_16 : SparseEntry := [(18,162),(19,-54),(21,12)]
theorem rawEntry_7_00_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 16=sparseCoefficient rawEntry_7_00_16 r := by decide +kernel
theorem rawEntry_7_00_16_coordinates : sparsePolynomial 81 rawEntry_7_00_16=rawStandardCoordinates 0 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_16_physical : invariantSubst (rawCoordinate 7 0 16)=rawStandardPolynomial 0 16 := by
  rw [rawCoordinate_sparse 7 0 16 rawEntry_7_00_16 rawEntry_7_00_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_16)=_
  rw [rawEntry_7_00_16_coordinates]
  exact rawStandard_subst 0 16
theorem rawEntry_7_16_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 0=sparseCoefficient rawEntry_7_00_16 r := by decide +kernel
theorem rawEntry_7_16_00_physical : invariantSubst (rawCoordinate 7 16 0)=rawStandardPolynomial 16 0 := by
  have hh : rawCoordinate 7 16 0=rawCoordinate 7 0 16 := by
    rw [rawCoordinate_sparse 7 16 0 rawEntry_7_00_16 rawEntry_7_16_00_data,rawCoordinate_sparse 7 0 16 rawEntry_7_00_16 rawEntry_7_00_16_data]
  rw [hh,rawEntry_7_00_16_physical]
  exact rawStandardPolynomial_symm 0 16
def rawEntry_7_00_17 : SparseEntry := [(20,162),(21,-54),(22,12)]
theorem rawEntry_7_00_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 0 17=sparseCoefficient rawEntry_7_00_17 r := by decide +kernel
theorem rawEntry_7_00_17_coordinates : sparsePolynomial 81 rawEntry_7_00_17=rawStandardCoordinates 0 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_00_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_00_17_physical : invariantSubst (rawCoordinate 7 0 17)=rawStandardPolynomial 0 17 := by
  rw [rawCoordinate_sparse 7 0 17 rawEntry_7_00_17 rawEntry_7_00_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_00_17)=_
  rw [rawEntry_7_00_17_coordinates]
  exact rawStandard_subst 0 17
theorem rawEntry_7_17_00_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 0=sparseCoefficient rawEntry_7_00_17 r := by decide +kernel
theorem rawEntry_7_17_00_physical : invariantSubst (rawCoordinate 7 17 0)=rawStandardPolynomial 17 0 := by
  have hh : rawCoordinate 7 17 0=rawCoordinate 7 0 17 := by
    rw [rawCoordinate_sparse 7 17 0 rawEntry_7_00_17 rawEntry_7_17_00_data,rawCoordinate_sparse 7 0 17 rawEntry_7_00_17 rawEntry_7_00_17_data]
  rw [hh,rawEntry_7_00_17_physical]
  exact rawStandardPolynomial_symm 0 17
def rawEntry_7_01_01 : SparseEntry := [(9,-108),(10,36)]
theorem rawEntry_7_01_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 1=sparseCoefficient rawEntry_7_01_01 r := by decide +kernel
theorem rawEntry_7_01_01_coordinates : sparsePolynomial 81 rawEntry_7_01_01=rawStandardCoordinates 1 1 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_01,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_01_physical : invariantSubst (rawCoordinate 7 1 1)=rawStandardPolynomial 1 1 := by
  rw [rawCoordinate_sparse 7 1 1 rawEntry_7_01_01 rawEntry_7_01_01_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_01)=_
  rw [rawEntry_7_01_01_coordinates]
  exact rawStandard_subst 1 1
def rawEntry_7_01_02 : SparseEntry := [(12,-108),(14,36)]
theorem rawEntry_7_01_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 2=sparseCoefficient rawEntry_7_01_02 r := by decide +kernel
theorem rawEntry_7_01_02_coordinates : sparsePolynomial 81 rawEntry_7_01_02=rawStandardCoordinates 1 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_02,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_02_physical : invariantSubst (rawCoordinate 7 1 2)=rawStandardPolynomial 1 2 := by
  rw [rawCoordinate_sparse 7 1 2 rawEntry_7_01_02 rawEntry_7_01_02_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_02)=_
  rw [rawEntry_7_01_02_coordinates]
  exact rawStandard_subst 1 2
theorem rawEntry_7_02_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 1=sparseCoefficient rawEntry_7_01_02 r := by decide +kernel
theorem rawEntry_7_02_01_physical : invariantSubst (rawCoordinate 7 2 1)=rawStandardPolynomial 2 1 := by
  have hh : rawCoordinate 7 2 1=rawCoordinate 7 1 2 := by
    rw [rawCoordinate_sparse 7 2 1 rawEntry_7_01_02 rawEntry_7_02_01_data,rawCoordinate_sparse 7 1 2 rawEntry_7_01_02 rawEntry_7_01_02_data]
  rw [hh,rawEntry_7_01_02_physical]
  exact rawStandardPolynomial_symm 1 2
end ThomsonNegative.Certificate.Bridges
