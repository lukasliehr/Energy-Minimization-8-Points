import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_01_03 : SparseEntry := [(14,-108),(15,36)]
theorem rawEntry_7_01_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 3=sparseCoefficient rawEntry_7_01_03 r := by decide +kernel
theorem rawEntry_7_01_03_coordinates : sparsePolynomial 81 rawEntry_7_01_03=rawStandardCoordinates 1 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_03,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_03_physical : invariantSubst (rawCoordinate 7 1 3)=rawStandardPolynomial 1 3 := by
  rw [rawCoordinate_sparse 7 1 3 rawEntry_7_01_03 rawEntry_7_01_03_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_03)=_
  rw [rawEntry_7_01_03_coordinates]
  exact rawStandard_subst 1 3
theorem rawEntry_7_03_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 1=sparseCoefficient rawEntry_7_01_03 r := by decide +kernel
theorem rawEntry_7_03_01_physical : invariantSubst (rawCoordinate 7 3 1)=rawStandardPolynomial 3 1 := by
  have hh : rawCoordinate 7 3 1=rawCoordinate 7 1 3 := by
    rw [rawCoordinate_sparse 7 3 1 rawEntry_7_01_03 rawEntry_7_03_01_data,rawCoordinate_sparse 7 1 3 rawEntry_7_01_03 rawEntry_7_01_03_data]
  rw [hh,rawEntry_7_01_03_physical]
  exact rawStandardPolynomial_symm 1 3
def rawEntry_7_01_04 : SparseEntry := [(18,-108),(20,36)]
theorem rawEntry_7_01_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 4=sparseCoefficient rawEntry_7_01_04 r := by decide +kernel
theorem rawEntry_7_01_04_coordinates : sparsePolynomial 81 rawEntry_7_01_04=rawStandardCoordinates 1 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_04,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_04_physical : invariantSubst (rawCoordinate 7 1 4)=rawStandardPolynomial 1 4 := by
  rw [rawCoordinate_sparse 7 1 4 rawEntry_7_01_04 rawEntry_7_01_04_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_04)=_
  rw [rawEntry_7_01_04_coordinates]
  exact rawStandard_subst 1 4
theorem rawEntry_7_04_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 1=sparseCoefficient rawEntry_7_01_04 r := by decide +kernel
theorem rawEntry_7_04_01_physical : invariantSubst (rawCoordinate 7 4 1)=rawStandardPolynomial 4 1 := by
  have hh : rawCoordinate 7 4 1=rawCoordinate 7 1 4 := by
    rw [rawCoordinate_sparse 7 4 1 rawEntry_7_01_04 rawEntry_7_04_01_data,rawCoordinate_sparse 7 1 4 rawEntry_7_01_04 rawEntry_7_01_04_data]
  rw [hh,rawEntry_7_01_04_physical]
  exact rawStandardPolynomial_symm 1 4
def rawEntry_7_01_05 : SparseEntry := [(19,-108),(21,36)]
theorem rawEntry_7_01_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 5=sparseCoefficient rawEntry_7_01_05 r := by decide +kernel
theorem rawEntry_7_01_05_coordinates : sparsePolynomial 81 rawEntry_7_01_05=rawStandardCoordinates 1 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_05_physical : invariantSubst (rawCoordinate 7 1 5)=rawStandardPolynomial 1 5 := by
  rw [rawCoordinate_sparse 7 1 5 rawEntry_7_01_05 rawEntry_7_01_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_05)=_
  rw [rawEntry_7_01_05_coordinates]
  exact rawStandard_subst 1 5
theorem rawEntry_7_05_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 1=sparseCoefficient rawEntry_7_01_05 r := by decide +kernel
theorem rawEntry_7_05_01_physical : invariantSubst (rawCoordinate 7 5 1)=rawStandardPolynomial 5 1 := by
  have hh : rawCoordinate 7 5 1=rawCoordinate 7 1 5 := by
    rw [rawCoordinate_sparse 7 5 1 rawEntry_7_01_05 rawEntry_7_05_01_data,rawCoordinate_sparse 7 1 5 rawEntry_7_01_05 rawEntry_7_01_05_data]
  rw [hh,rawEntry_7_01_05_physical]
  exact rawStandardPolynomial_symm 1 5
def rawEntry_7_01_06 : SparseEntry := [(21,-108),(22,36)]
theorem rawEntry_7_01_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 6=sparseCoefficient rawEntry_7_01_06 r := by decide +kernel
theorem rawEntry_7_01_06_coordinates : sparsePolynomial 81 rawEntry_7_01_06=rawStandardCoordinates 1 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_06_physical : invariantSubst (rawCoordinate 7 1 6)=rawStandardPolynomial 1 6 := by
  rw [rawCoordinate_sparse 7 1 6 rawEntry_7_01_06 rawEntry_7_01_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_06)=_
  rw [rawEntry_7_01_06_coordinates]
  exact rawStandard_subst 1 6
theorem rawEntry_7_06_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 1=sparseCoefficient rawEntry_7_01_06 r := by decide +kernel
theorem rawEntry_7_06_01_physical : invariantSubst (rawCoordinate 7 6 1)=rawStandardPolynomial 6 1 := by
  have hh : rawCoordinate 7 6 1=rawCoordinate 7 1 6 := by
    rw [rawCoordinate_sparse 7 6 1 rawEntry_7_01_06 rawEntry_7_06_01_data,rawCoordinate_sparse 7 1 6 rawEntry_7_01_06 rawEntry_7_01_06_data]
  rw [hh,rawEntry_7_01_06_physical]
  exact rawStandardPolynomial_symm 1 6
def rawEntry_7_01_07 : SparseEntry := [(25,-108),(27,36)]
theorem rawEntry_7_01_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 7=sparseCoefficient rawEntry_7_01_07 r := by decide +kernel
theorem rawEntry_7_01_07_coordinates : sparsePolynomial 81 rawEntry_7_01_07=rawStandardCoordinates 1 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_07_physical : invariantSubst (rawCoordinate 7 1 7)=rawStandardPolynomial 1 7 := by
  rw [rawCoordinate_sparse 7 1 7 rawEntry_7_01_07 rawEntry_7_01_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_07)=_
  rw [rawEntry_7_01_07_coordinates]
  exact rawStandard_subst 1 7
theorem rawEntry_7_07_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 1=sparseCoefficient rawEntry_7_01_07 r := by decide +kernel
theorem rawEntry_7_07_01_physical : invariantSubst (rawCoordinate 7 7 1)=rawStandardPolynomial 7 1 := by
  have hh : rawCoordinate 7 7 1=rawCoordinate 7 1 7 := by
    rw [rawCoordinate_sparse 7 7 1 rawEntry_7_01_07 rawEntry_7_07_01_data,rawCoordinate_sparse 7 1 7 rawEntry_7_01_07 rawEntry_7_01_07_data]
  rw [hh,rawEntry_7_01_07_physical]
  exact rawStandardPolynomial_symm 1 7
def rawEntry_7_01_08 : SparseEntry := [(26,-108),(28,36)]
theorem rawEntry_7_01_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 8=sparseCoefficient rawEntry_7_01_08 r := by decide +kernel
theorem rawEntry_7_01_08_coordinates : sparsePolynomial 81 rawEntry_7_01_08=rawStandardCoordinates 1 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_08_physical : invariantSubst (rawCoordinate 7 1 8)=rawStandardPolynomial 1 8 := by
  rw [rawCoordinate_sparse 7 1 8 rawEntry_7_01_08 rawEntry_7_01_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_08)=_
  rw [rawEntry_7_01_08_coordinates]
  exact rawStandard_subst 1 8
theorem rawEntry_7_08_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 1=sparseCoefficient rawEntry_7_01_08 r := by decide +kernel
theorem rawEntry_7_08_01_physical : invariantSubst (rawCoordinate 7 8 1)=rawStandardPolynomial 8 1 := by
  have hh : rawCoordinate 7 8 1=rawCoordinate 7 1 8 := by
    rw [rawCoordinate_sparse 7 8 1 rawEntry_7_01_08 rawEntry_7_08_01_data,rawCoordinate_sparse 7 1 8 rawEntry_7_01_08 rawEntry_7_01_08_data]
  rw [hh,rawEntry_7_01_08_physical]
  exact rawStandardPolynomial_symm 1 8
def rawEntry_7_01_09 : SparseEntry := [(27,-108),(29,36)]
theorem rawEntry_7_01_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 9=sparseCoefficient rawEntry_7_01_09 r := by decide +kernel
theorem rawEntry_7_01_09_coordinates : sparsePolynomial 81 rawEntry_7_01_09=rawStandardCoordinates 1 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_09_physical : invariantSubst (rawCoordinate 7 1 9)=rawStandardPolynomial 1 9 := by
  rw [rawCoordinate_sparse 7 1 9 rawEntry_7_01_09 rawEntry_7_01_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_09)=_
  rw [rawEntry_7_01_09_coordinates]
  exact rawStandard_subst 1 9
theorem rawEntry_7_09_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 1=sparseCoefficient rawEntry_7_01_09 r := by decide +kernel
theorem rawEntry_7_09_01_physical : invariantSubst (rawCoordinate 7 9 1)=rawStandardPolynomial 9 1 := by
  have hh : rawCoordinate 7 9 1=rawCoordinate 7 1 9 := by
    rw [rawCoordinate_sparse 7 9 1 rawEntry_7_01_09 rawEntry_7_09_01_data,rawCoordinate_sparse 7 1 9 rawEntry_7_01_09 rawEntry_7_01_09_data]
  rw [hh,rawEntry_7_01_09_physical]
  exact rawStandardPolynomial_symm 1 9
def rawEntry_7_01_10 : SparseEntry := [(29,-108),(30,36)]
theorem rawEntry_7_01_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 10=sparseCoefficient rawEntry_7_01_10 r := by decide +kernel
theorem rawEntry_7_01_10_coordinates : sparsePolynomial 81 rawEntry_7_01_10=rawStandardCoordinates 1 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_10_physical : invariantSubst (rawCoordinate 7 1 10)=rawStandardPolynomial 1 10 := by
  rw [rawCoordinate_sparse 7 1 10 rawEntry_7_01_10 rawEntry_7_01_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_10)=_
  rw [rawEntry_7_01_10_coordinates]
  exact rawStandard_subst 1 10
theorem rawEntry_7_10_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 1=sparseCoefficient rawEntry_7_01_10 r := by decide +kernel
theorem rawEntry_7_10_01_physical : invariantSubst (rawCoordinate 7 10 1)=rawStandardPolynomial 10 1 := by
  have hh : rawCoordinate 7 10 1=rawCoordinate 7 1 10 := by
    rw [rawCoordinate_sparse 7 10 1 rawEntry_7_01_10 rawEntry_7_10_01_data,rawCoordinate_sparse 7 1 10 rawEntry_7_01_10 rawEntry_7_01_10_data]
  rw [hh,rawEntry_7_01_10_physical]
  exact rawStandardPolynomial_symm 1 10
def rawEntry_7_01_11 : SparseEntry := [(8,162),(9,-54),(10,12)]
theorem rawEntry_7_01_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 11=sparseCoefficient rawEntry_7_01_11 r := by decide +kernel
theorem rawEntry_7_01_11_coordinates : sparsePolynomial 81 rawEntry_7_01_11=rawStandardCoordinates 1 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_11_physical : invariantSubst (rawCoordinate 7 1 11)=rawStandardPolynomial 1 11 := by
  rw [rawCoordinate_sparse 7 1 11 rawEntry_7_01_11 rawEntry_7_01_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_11)=_
  rw [rawEntry_7_01_11_coordinates]
  exact rawStandard_subst 1 11
theorem rawEntry_7_11_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 1=sparseCoefficient rawEntry_7_01_11 r := by decide +kernel
theorem rawEntry_7_11_01_physical : invariantSubst (rawCoordinate 7 11 1)=rawStandardPolynomial 11 1 := by
  have hh : rawCoordinate 7 11 1=rawCoordinate 7 1 11 := by
    rw [rawCoordinate_sparse 7 11 1 rawEntry_7_01_11 rawEntry_7_11_01_data,rawCoordinate_sparse 7 1 11 rawEntry_7_01_11 rawEntry_7_01_11_data]
  rw [hh,rawEntry_7_01_11_physical]
  exact rawStandardPolynomial_symm 1 11
def rawEntry_7_01_12 : SparseEntry := [(13,162),(14,-54),(15,12)]
theorem rawEntry_7_01_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 12=sparseCoefficient rawEntry_7_01_12 r := by decide +kernel
theorem rawEntry_7_01_12_coordinates : sparsePolynomial 81 rawEntry_7_01_12=rawStandardCoordinates 1 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_12_physical : invariantSubst (rawCoordinate 7 1 12)=rawStandardPolynomial 1 12 := by
  rw [rawCoordinate_sparse 7 1 12 rawEntry_7_01_12 rawEntry_7_01_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_12)=_
  rw [rawEntry_7_01_12_coordinates]
  exact rawStandard_subst 1 12
theorem rawEntry_7_12_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 1=sparseCoefficient rawEntry_7_01_12 r := by decide +kernel
theorem rawEntry_7_12_01_physical : invariantSubst (rawCoordinate 7 12 1)=rawStandardPolynomial 12 1 := by
  have hh : rawCoordinate 7 12 1=rawCoordinate 7 1 12 := by
    rw [rawCoordinate_sparse 7 12 1 rawEntry_7_01_12 rawEntry_7_12_01_data,rawCoordinate_sparse 7 1 12 rawEntry_7_01_12 rawEntry_7_01_12_data]
  rw [hh,rawEntry_7_01_12_physical]
  exact rawStandardPolynomial_symm 1 12
def rawEntry_7_01_13 : SparseEntry := [(18,162),(19,-54),(21,12)]
theorem rawEntry_7_01_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 13=sparseCoefficient rawEntry_7_01_13 r := by decide +kernel
theorem rawEntry_7_01_13_coordinates : sparsePolynomial 81 rawEntry_7_01_13=rawStandardCoordinates 1 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_13_physical : invariantSubst (rawCoordinate 7 1 13)=rawStandardPolynomial 1 13 := by
  rw [rawCoordinate_sparse 7 1 13 rawEntry_7_01_13 rawEntry_7_01_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_13)=_
  rw [rawEntry_7_01_13_coordinates]
  exact rawStandard_subst 1 13
theorem rawEntry_7_13_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 1=sparseCoefficient rawEntry_7_01_13 r := by decide +kernel
theorem rawEntry_7_13_01_physical : invariantSubst (rawCoordinate 7 13 1)=rawStandardPolynomial 13 1 := by
  have hh : rawCoordinate 7 13 1=rawCoordinate 7 1 13 := by
    rw [rawCoordinate_sparse 7 13 1 rawEntry_7_01_13 rawEntry_7_13_01_data,rawCoordinate_sparse 7 1 13 rawEntry_7_01_13 rawEntry_7_01_13_data]
  rw [hh,rawEntry_7_01_13_physical]
  exact rawStandardPolynomial_symm 1 13
def rawEntry_7_01_14 : SparseEntry := [(20,162),(21,-54),(22,12)]
theorem rawEntry_7_01_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 14=sparseCoefficient rawEntry_7_01_14 r := by decide +kernel
theorem rawEntry_7_01_14_coordinates : sparsePolynomial 81 rawEntry_7_01_14=rawStandardCoordinates 1 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_14_physical : invariantSubst (rawCoordinate 7 1 14)=rawStandardPolynomial 1 14 := by
  rw [rawCoordinate_sparse 7 1 14 rawEntry_7_01_14 rawEntry_7_01_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_14)=_
  rw [rawEntry_7_01_14_coordinates]
  exact rawStandard_subst 1 14
theorem rawEntry_7_14_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 1=sparseCoefficient rawEntry_7_01_14 r := by decide +kernel
theorem rawEntry_7_14_01_physical : invariantSubst (rawCoordinate 7 14 1)=rawStandardPolynomial 14 1 := by
  have hh : rawCoordinate 7 14 1=rawCoordinate 7 1 14 := by
    rw [rawCoordinate_sparse 7 14 1 rawEntry_7_01_14 rawEntry_7_14_01_data,rawCoordinate_sparse 7 1 14 rawEntry_7_01_14 rawEntry_7_01_14_data]
  rw [hh,rawEntry_7_01_14_physical]
  exact rawStandardPolynomial_symm 1 14
def rawEntry_7_01_15 : SparseEntry := [(24,162),(26,-54),(28,12)]
theorem rawEntry_7_01_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 15=sparseCoefficient rawEntry_7_01_15 r := by decide +kernel
theorem rawEntry_7_01_15_coordinates : sparsePolynomial 81 rawEntry_7_01_15=rawStandardCoordinates 1 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_15_physical : invariantSubst (rawCoordinate 7 1 15)=rawStandardPolynomial 1 15 := by
  rw [rawCoordinate_sparse 7 1 15 rawEntry_7_01_15 rawEntry_7_01_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_15)=_
  rw [rawEntry_7_01_15_coordinates]
  exact rawStandard_subst 1 15
theorem rawEntry_7_15_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 1=sparseCoefficient rawEntry_7_01_15 r := by decide +kernel
theorem rawEntry_7_15_01_physical : invariantSubst (rawCoordinate 7 15 1)=rawStandardPolynomial 15 1 := by
  have hh : rawCoordinate 7 15 1=rawCoordinate 7 1 15 := by
    rw [rawCoordinate_sparse 7 15 1 rawEntry_7_01_15 rawEntry_7_15_01_data,rawCoordinate_sparse 7 1 15 rawEntry_7_01_15 rawEntry_7_01_15_data]
  rw [hh,rawEntry_7_01_15_physical]
  exact rawStandardPolynomial_symm 1 15
def rawEntry_7_01_16 : SparseEntry := [(26,162),(27,-54),(29,12)]
theorem rawEntry_7_01_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 16=sparseCoefficient rawEntry_7_01_16 r := by decide +kernel
theorem rawEntry_7_01_16_coordinates : sparsePolynomial 81 rawEntry_7_01_16=rawStandardCoordinates 1 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_16_physical : invariantSubst (rawCoordinate 7 1 16)=rawStandardPolynomial 1 16 := by
  rw [rawCoordinate_sparse 7 1 16 rawEntry_7_01_16 rawEntry_7_01_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_16)=_
  rw [rawEntry_7_01_16_coordinates]
  exact rawStandard_subst 1 16
theorem rawEntry_7_16_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 1=sparseCoefficient rawEntry_7_01_16 r := by decide +kernel
theorem rawEntry_7_16_01_physical : invariantSubst (rawCoordinate 7 16 1)=rawStandardPolynomial 16 1 := by
  have hh : rawCoordinate 7 16 1=rawCoordinate 7 1 16 := by
    rw [rawCoordinate_sparse 7 16 1 rawEntry_7_01_16 rawEntry_7_16_01_data,rawCoordinate_sparse 7 1 16 rawEntry_7_01_16 rawEntry_7_01_16_data]
  rw [hh,rawEntry_7_01_16_physical]
  exact rawStandardPolynomial_symm 1 16
def rawEntry_7_01_17 : SparseEntry := [(28,162),(29,-54),(30,12)]
theorem rawEntry_7_01_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 1 17=sparseCoefficient rawEntry_7_01_17 r := by decide +kernel
theorem rawEntry_7_01_17_coordinates : sparsePolynomial 81 rawEntry_7_01_17=rawStandardCoordinates 1 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_01_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_01_17_physical : invariantSubst (rawCoordinate 7 1 17)=rawStandardPolynomial 1 17 := by
  rw [rawCoordinate_sparse 7 1 17 rawEntry_7_01_17 rawEntry_7_01_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_01_17)=_
  rw [rawEntry_7_01_17_coordinates]
  exact rawStandard_subst 1 17
theorem rawEntry_7_17_01_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 1=sparseCoefficient rawEntry_7_01_17 r := by decide +kernel
theorem rawEntry_7_17_01_physical : invariantSubst (rawCoordinate 7 17 1)=rawStandardPolynomial 17 1 := by
  have hh : rawCoordinate 7 17 1=rawCoordinate 7 1 17 := by
    rw [rawCoordinate_sparse 7 17 1 rawEntry_7_01_17 rawEntry_7_17_01_data,rawCoordinate_sparse 7 1 17 rawEntry_7_01_17 rawEntry_7_01_17_data]
  rw [hh,rawEntry_7_01_17_physical]
  exact rawStandardPolynomial_symm 1 17
def rawEntry_7_02_02 : SparseEntry := [(17,-108),(19,36)]
theorem rawEntry_7_02_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 2=sparseCoefficient rawEntry_7_02_02 r := by decide +kernel
theorem rawEntry_7_02_02_coordinates : sparsePolynomial 81 rawEntry_7_02_02=rawStandardCoordinates 2 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_02,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_02_physical : invariantSubst (rawCoordinate 7 2 2)=rawStandardPolynomial 2 2 := by
  rw [rawCoordinate_sparse 7 2 2 rawEntry_7_02_02 rawEntry_7_02_02_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_02)=_
  rw [rawEntry_7_02_02_coordinates]
  exact rawStandard_subst 2 2
def rawEntry_7_02_03 : SparseEntry := [(19,-108),(21,36)]
theorem rawEntry_7_02_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 3=sparseCoefficient rawEntry_7_02_03 r := by decide +kernel
theorem rawEntry_7_02_03_coordinates : sparsePolynomial 81 rawEntry_7_02_03=rawStandardCoordinates 2 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_03,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_03_physical : invariantSubst (rawCoordinate 7 2 3)=rawStandardPolynomial 2 3 := by
  rw [rawCoordinate_sparse 7 2 3 rawEntry_7_02_03 rawEntry_7_02_03_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_03)=_
  rw [rawEntry_7_02_03_coordinates]
  exact rawStandard_subst 2 3
theorem rawEntry_7_03_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 2=sparseCoefficient rawEntry_7_02_03 r := by decide +kernel
theorem rawEntry_7_03_02_physical : invariantSubst (rawCoordinate 7 3 2)=rawStandardPolynomial 3 2 := by
  have hh : rawCoordinate 7 3 2=rawCoordinate 7 2 3 := by
    rw [rawCoordinate_sparse 7 3 2 rawEntry_7_02_03 rawEntry_7_03_02_data,rawCoordinate_sparse 7 2 3 rawEntry_7_02_03 rawEntry_7_02_03_data]
  rw [hh,rawEntry_7_02_03_physical]
  exact rawStandardPolynomial_symm 2 3
def rawEntry_7_02_04 : SparseEntry := [(23,-108),(26,36)]
theorem rawEntry_7_02_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 4=sparseCoefficient rawEntry_7_02_04 r := by decide +kernel
theorem rawEntry_7_02_04_coordinates : sparsePolynomial 81 rawEntry_7_02_04=rawStandardCoordinates 2 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_04,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_04_physical : invariantSubst (rawCoordinate 7 2 4)=rawStandardPolynomial 2 4 := by
  rw [rawCoordinate_sparse 7 2 4 rawEntry_7_02_04 rawEntry_7_02_04_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_04)=_
  rw [rawEntry_7_02_04_coordinates]
  exact rawStandard_subst 2 4
theorem rawEntry_7_04_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 2=sparseCoefficient rawEntry_7_02_04 r := by decide +kernel
theorem rawEntry_7_04_02_physical : invariantSubst (rawCoordinate 7 4 2)=rawStandardPolynomial 4 2 := by
  have hh : rawCoordinate 7 4 2=rawCoordinate 7 2 4 := by
    rw [rawCoordinate_sparse 7 4 2 rawEntry_7_02_04 rawEntry_7_04_02_data,rawCoordinate_sparse 7 2 4 rawEntry_7_02_04 rawEntry_7_02_04_data]
  rw [hh,rawEntry_7_02_04_physical]
  exact rawStandardPolynomial_symm 2 4
def rawEntry_7_02_05 : SparseEntry := [(25,-108),(27,36)]
theorem rawEntry_7_02_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 5=sparseCoefficient rawEntry_7_02_05 r := by decide +kernel
theorem rawEntry_7_02_05_coordinates : sparsePolynomial 81 rawEntry_7_02_05=rawStandardCoordinates 2 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_05_physical : invariantSubst (rawCoordinate 7 2 5)=rawStandardPolynomial 2 5 := by
  rw [rawCoordinate_sparse 7 2 5 rawEntry_7_02_05 rawEntry_7_02_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_05)=_
  rw [rawEntry_7_02_05_coordinates]
  exact rawStandard_subst 2 5
theorem rawEntry_7_05_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 2=sparseCoefficient rawEntry_7_02_05 r := by decide +kernel
theorem rawEntry_7_05_02_physical : invariantSubst (rawCoordinate 7 5 2)=rawStandardPolynomial 5 2 := by
  have hh : rawCoordinate 7 5 2=rawCoordinate 7 2 5 := by
    rw [rawCoordinate_sparse 7 5 2 rawEntry_7_02_05 rawEntry_7_05_02_data,rawCoordinate_sparse 7 2 5 rawEntry_7_02_05 rawEntry_7_02_05_data]
  rw [hh,rawEntry_7_02_05_physical]
  exact rawStandardPolynomial_symm 2 5
def rawEntry_7_02_06 : SparseEntry := [(27,-108),(29,36)]
theorem rawEntry_7_02_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 6=sparseCoefficient rawEntry_7_02_06 r := by decide +kernel
theorem rawEntry_7_02_06_coordinates : sparsePolynomial 81 rawEntry_7_02_06=rawStandardCoordinates 2 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_06_physical : invariantSubst (rawCoordinate 7 2 6)=rawStandardPolynomial 2 6 := by
  rw [rawCoordinate_sparse 7 2 6 rawEntry_7_02_06 rawEntry_7_02_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_06)=_
  rw [rawEntry_7_02_06_coordinates]
  exact rawStandard_subst 2 6
theorem rawEntry_7_06_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 2=sparseCoefficient rawEntry_7_02_06 r := by decide +kernel
theorem rawEntry_7_06_02_physical : invariantSubst (rawCoordinate 7 6 2)=rawStandardPolynomial 6 2 := by
  have hh : rawCoordinate 7 6 2=rawCoordinate 7 2 6 := by
    rw [rawCoordinate_sparse 7 6 2 rawEntry_7_02_06 rawEntry_7_06_02_data,rawCoordinate_sparse 7 2 6 rawEntry_7_02_06 rawEntry_7_02_06_data]
  rw [hh,rawEntry_7_02_06_physical]
  exact rawStandardPolynomial_symm 2 6
end ThomsonNegative.Certificate.Bridges
