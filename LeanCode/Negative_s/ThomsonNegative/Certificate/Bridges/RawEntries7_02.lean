import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_02_07 : SparseEntry := [(32,-108),(35,36)]
theorem rawEntry_7_02_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 7=sparseCoefficient rawEntry_7_02_07 r := by decide +kernel
theorem rawEntry_7_02_07_coordinates : sparsePolynomial 81 rawEntry_7_02_07=rawStandardCoordinates 2 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_07_physical : invariantSubst (rawCoordinate 7 2 7)=rawStandardPolynomial 2 7 := by
  rw [rawCoordinate_sparse 7 2 7 rawEntry_7_02_07 rawEntry_7_02_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_07)=_
  rw [rawEntry_7_02_07_coordinates]
  exact rawStandard_subst 2 7
theorem rawEntry_7_07_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 2=sparseCoefficient rawEntry_7_02_07 r := by decide +kernel
theorem rawEntry_7_07_02_physical : invariantSubst (rawCoordinate 7 7 2)=rawStandardPolynomial 7 2 := by
  have hh : rawCoordinate 7 7 2=rawCoordinate 7 2 7 := by
    rw [rawCoordinate_sparse 7 7 2 rawEntry_7_02_07 rawEntry_7_07_02_data,rawCoordinate_sparse 7 2 7 rawEntry_7_02_07 rawEntry_7_02_07_data]
  rw [hh,rawEntry_7_02_07_physical]
  exact rawStandardPolynomial_symm 2 7
def rawEntry_7_02_08 : SparseEntry := [(33,-108),(36,36)]
theorem rawEntry_7_02_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 8=sparseCoefficient rawEntry_7_02_08 r := by decide +kernel
theorem rawEntry_7_02_08_coordinates : sparsePolynomial 81 rawEntry_7_02_08=rawStandardCoordinates 2 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_08_physical : invariantSubst (rawCoordinate 7 2 8)=rawStandardPolynomial 2 8 := by
  rw [rawCoordinate_sparse 7 2 8 rawEntry_7_02_08 rawEntry_7_02_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_08)=_
  rw [rawEntry_7_02_08_coordinates]
  exact rawStandard_subst 2 8
theorem rawEntry_7_08_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 2=sparseCoefficient rawEntry_7_02_08 r := by decide +kernel
theorem rawEntry_7_08_02_physical : invariantSubst (rawCoordinate 7 8 2)=rawStandardPolynomial 8 2 := by
  have hh : rawCoordinate 7 8 2=rawCoordinate 7 2 8 := by
    rw [rawCoordinate_sparse 7 8 2 rawEntry_7_02_08 rawEntry_7_08_02_data,rawCoordinate_sparse 7 2 8 rawEntry_7_02_08 rawEntry_7_02_08_data]
  rw [hh,rawEntry_7_02_08_physical]
  exact rawStandardPolynomial_symm 2 8
def rawEntry_7_02_09 : SparseEntry := [(35,-108),(37,36)]
theorem rawEntry_7_02_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 9=sparseCoefficient rawEntry_7_02_09 r := by decide +kernel
theorem rawEntry_7_02_09_coordinates : sparsePolynomial 81 rawEntry_7_02_09=rawStandardCoordinates 2 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_09_physical : invariantSubst (rawCoordinate 7 2 9)=rawStandardPolynomial 2 9 := by
  rw [rawCoordinate_sparse 7 2 9 rawEntry_7_02_09 rawEntry_7_02_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_09)=_
  rw [rawEntry_7_02_09_coordinates]
  exact rawStandard_subst 2 9
theorem rawEntry_7_09_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 2=sparseCoefficient rawEntry_7_02_09 r := by decide +kernel
theorem rawEntry_7_09_02_physical : invariantSubst (rawCoordinate 7 9 2)=rawStandardPolynomial 9 2 := by
  have hh : rawCoordinate 7 9 2=rawCoordinate 7 2 9 := by
    rw [rawCoordinate_sparse 7 9 2 rawEntry_7_02_09 rawEntry_7_09_02_data,rawCoordinate_sparse 7 2 9 rawEntry_7_02_09 rawEntry_7_02_09_data]
  rw [hh,rawEntry_7_02_09_physical]
  exact rawStandardPolynomial_symm 2 9
def rawEntry_7_02_10 : SparseEntry := [(37,-108),(39,36)]
theorem rawEntry_7_02_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 10=sparseCoefficient rawEntry_7_02_10 r := by decide +kernel
theorem rawEntry_7_02_10_coordinates : sparsePolynomial 81 rawEntry_7_02_10=rawStandardCoordinates 2 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_10_physical : invariantSubst (rawCoordinate 7 2 10)=rawStandardPolynomial 2 10 := by
  rw [rawCoordinate_sparse 7 2 10 rawEntry_7_02_10 rawEntry_7_02_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_10)=_
  rw [rawEntry_7_02_10_coordinates]
  exact rawStandard_subst 2 10
theorem rawEntry_7_10_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 2=sparseCoefficient rawEntry_7_02_10 r := by decide +kernel
theorem rawEntry_7_10_02_physical : invariantSubst (rawCoordinate 7 10 2)=rawStandardPolynomial 10 2 := by
  have hh : rawCoordinate 7 10 2=rawCoordinate 7 2 10 := by
    rw [rawCoordinate_sparse 7 10 2 rawEntry_7_02_10 rawEntry_7_10_02_data,rawCoordinate_sparse 7 2 10 rawEntry_7_02_10 rawEntry_7_02_10_data]
  rw [hh,rawEntry_7_02_10_physical]
  exact rawStandardPolynomial_symm 2 10
def rawEntry_7_02_11 : SparseEntry := [(11,162),(12,-54),(14,12)]
theorem rawEntry_7_02_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 11=sparseCoefficient rawEntry_7_02_11 r := by decide +kernel
theorem rawEntry_7_02_11_coordinates : sparsePolynomial 81 rawEntry_7_02_11=rawStandardCoordinates 2 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_11_physical : invariantSubst (rawCoordinate 7 2 11)=rawStandardPolynomial 2 11 := by
  rw [rawCoordinate_sparse 7 2 11 rawEntry_7_02_11 rawEntry_7_02_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_11)=_
  rw [rawEntry_7_02_11_coordinates]
  exact rawStandard_subst 2 11
theorem rawEntry_7_11_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 2=sparseCoefficient rawEntry_7_02_11 r := by decide +kernel
theorem rawEntry_7_11_02_physical : invariantSubst (rawCoordinate 7 11 2)=rawStandardPolynomial 11 2 := by
  have hh : rawCoordinate 7 11 2=rawCoordinate 7 2 11 := by
    rw [rawCoordinate_sparse 7 11 2 rawEntry_7_02_11 rawEntry_7_11_02_data,rawCoordinate_sparse 7 2 11 rawEntry_7_02_11 rawEntry_7_02_11_data]
  rw [hh,rawEntry_7_02_11_physical]
  exact rawStandardPolynomial_symm 2 11
def rawEntry_7_02_12 : SparseEntry := [(18,162),(19,-54),(21,12)]
theorem rawEntry_7_02_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 12=sparseCoefficient rawEntry_7_02_12 r := by decide +kernel
theorem rawEntry_7_02_12_coordinates : sparsePolynomial 81 rawEntry_7_02_12=rawStandardCoordinates 2 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_12_physical : invariantSubst (rawCoordinate 7 2 12)=rawStandardPolynomial 2 12 := by
  rw [rawCoordinate_sparse 7 2 12 rawEntry_7_02_12 rawEntry_7_02_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_12)=_
  rw [rawEntry_7_02_12_coordinates]
  exact rawStandard_subst 2 12
theorem rawEntry_7_12_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 2=sparseCoefficient rawEntry_7_02_12 r := by decide +kernel
theorem rawEntry_7_12_02_physical : invariantSubst (rawCoordinate 7 12 2)=rawStandardPolynomial 12 2 := by
  have hh : rawCoordinate 7 12 2=rawCoordinate 7 2 12 := by
    rw [rawCoordinate_sparse 7 12 2 rawEntry_7_02_12 rawEntry_7_12_02_data,rawCoordinate_sparse 7 2 12 rawEntry_7_02_12 rawEntry_7_02_12_data]
  rw [hh,rawEntry_7_02_12_physical]
  exact rawStandardPolynomial_symm 2 12
def rawEntry_7_02_13 : SparseEntry := [(23,162),(25,-54),(27,12)]
theorem rawEntry_7_02_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 13=sparseCoefficient rawEntry_7_02_13 r := by decide +kernel
theorem rawEntry_7_02_13_coordinates : sparsePolynomial 81 rawEntry_7_02_13=rawStandardCoordinates 2 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_13_physical : invariantSubst (rawCoordinate 7 2 13)=rawStandardPolynomial 2 13 := by
  rw [rawCoordinate_sparse 7 2 13 rawEntry_7_02_13 rawEntry_7_02_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_13)=_
  rw [rawEntry_7_02_13_coordinates]
  exact rawStandard_subst 2 13
theorem rawEntry_7_13_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 2=sparseCoefficient rawEntry_7_02_13 r := by decide +kernel
theorem rawEntry_7_13_02_physical : invariantSubst (rawCoordinate 7 13 2)=rawStandardPolynomial 13 2 := by
  have hh : rawCoordinate 7 13 2=rawCoordinate 7 2 13 := by
    rw [rawCoordinate_sparse 7 13 2 rawEntry_7_02_13 rawEntry_7_13_02_data,rawCoordinate_sparse 7 2 13 rawEntry_7_02_13 rawEntry_7_02_13_data]
  rw [hh,rawEntry_7_02_13_physical]
  exact rawStandardPolynomial_symm 2 13
def rawEntry_7_02_14 : SparseEntry := [(26,162),(27,-54),(29,12)]
theorem rawEntry_7_02_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 14=sparseCoefficient rawEntry_7_02_14 r := by decide +kernel
theorem rawEntry_7_02_14_coordinates : sparsePolynomial 81 rawEntry_7_02_14=rawStandardCoordinates 2 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_14_physical : invariantSubst (rawCoordinate 7 2 14)=rawStandardPolynomial 2 14 := by
  rw [rawCoordinate_sparse 7 2 14 rawEntry_7_02_14 rawEntry_7_02_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_14)=_
  rw [rawEntry_7_02_14_coordinates]
  exact rawStandard_subst 2 14
theorem rawEntry_7_14_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 2=sparseCoefficient rawEntry_7_02_14 r := by decide +kernel
theorem rawEntry_7_14_02_physical : invariantSubst (rawCoordinate 7 14 2)=rawStandardPolynomial 14 2 := by
  have hh : rawCoordinate 7 14 2=rawCoordinate 7 2 14 := by
    rw [rawCoordinate_sparse 7 14 2 rawEntry_7_02_14 rawEntry_7_14_02_data,rawCoordinate_sparse 7 2 14 rawEntry_7_02_14 rawEntry_7_02_14_data]
  rw [hh,rawEntry_7_02_14_physical]
  exact rawStandardPolynomial_symm 2 14
def rawEntry_7_02_15 : SparseEntry := [(31,162),(33,-54),(36,12)]
theorem rawEntry_7_02_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 15=sparseCoefficient rawEntry_7_02_15 r := by decide +kernel
theorem rawEntry_7_02_15_coordinates : sparsePolynomial 81 rawEntry_7_02_15=rawStandardCoordinates 2 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_15_physical : invariantSubst (rawCoordinate 7 2 15)=rawStandardPolynomial 2 15 := by
  rw [rawCoordinate_sparse 7 2 15 rawEntry_7_02_15 rawEntry_7_02_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_15)=_
  rw [rawEntry_7_02_15_coordinates]
  exact rawStandard_subst 2 15
theorem rawEntry_7_15_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 2=sparseCoefficient rawEntry_7_02_15 r := by decide +kernel
theorem rawEntry_7_15_02_physical : invariantSubst (rawCoordinate 7 15 2)=rawStandardPolynomial 15 2 := by
  have hh : rawCoordinate 7 15 2=rawCoordinate 7 2 15 := by
    rw [rawCoordinate_sparse 7 15 2 rawEntry_7_02_15 rawEntry_7_15_02_data,rawCoordinate_sparse 7 2 15 rawEntry_7_02_15 rawEntry_7_02_15_data]
  rw [hh,rawEntry_7_02_15_physical]
  exact rawStandardPolynomial_symm 2 15
def rawEntry_7_02_16 : SparseEntry := [(33,162),(35,-54),(37,12)]
theorem rawEntry_7_02_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 16=sparseCoefficient rawEntry_7_02_16 r := by decide +kernel
theorem rawEntry_7_02_16_coordinates : sparsePolynomial 81 rawEntry_7_02_16=rawStandardCoordinates 2 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_16_physical : invariantSubst (rawCoordinate 7 2 16)=rawStandardPolynomial 2 16 := by
  rw [rawCoordinate_sparse 7 2 16 rawEntry_7_02_16 rawEntry_7_02_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_16)=_
  rw [rawEntry_7_02_16_coordinates]
  exact rawStandard_subst 2 16
theorem rawEntry_7_16_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 2=sparseCoefficient rawEntry_7_02_16 r := by decide +kernel
theorem rawEntry_7_16_02_physical : invariantSubst (rawCoordinate 7 16 2)=rawStandardPolynomial 16 2 := by
  have hh : rawCoordinate 7 16 2=rawCoordinate 7 2 16 := by
    rw [rawCoordinate_sparse 7 16 2 rawEntry_7_02_16 rawEntry_7_16_02_data,rawCoordinate_sparse 7 2 16 rawEntry_7_02_16 rawEntry_7_02_16_data]
  rw [hh,rawEntry_7_02_16_physical]
  exact rawStandardPolynomial_symm 2 16
def rawEntry_7_02_17 : SparseEntry := [(36,162),(37,-54),(39,12)]
theorem rawEntry_7_02_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 2 17=sparseCoefficient rawEntry_7_02_17 r := by decide +kernel
theorem rawEntry_7_02_17_coordinates : sparsePolynomial 81 rawEntry_7_02_17=rawStandardCoordinates 2 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_02_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_02_17_physical : invariantSubst (rawCoordinate 7 2 17)=rawStandardPolynomial 2 17 := by
  rw [rawCoordinate_sparse 7 2 17 rawEntry_7_02_17 rawEntry_7_02_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_02_17)=_
  rw [rawEntry_7_02_17_coordinates]
  exact rawStandard_subst 2 17
theorem rawEntry_7_17_02_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 2=sparseCoefficient rawEntry_7_02_17 r := by decide +kernel
theorem rawEntry_7_17_02_physical : invariantSubst (rawCoordinate 7 17 2)=rawStandardPolynomial 17 2 := by
  have hh : rawCoordinate 7 17 2=rawCoordinate 7 2 17 := by
    rw [rawCoordinate_sparse 7 17 2 rawEntry_7_02_17 rawEntry_7_17_02_data,rawCoordinate_sparse 7 2 17 rawEntry_7_02_17 rawEntry_7_02_17_data]
  rw [hh,rawEntry_7_02_17_physical]
  exact rawStandardPolynomial_symm 2 17
def rawEntry_7_03_03 : SparseEntry := [(21,-108),(22,36)]
theorem rawEntry_7_03_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 3=sparseCoefficient rawEntry_7_03_03 r := by decide +kernel
theorem rawEntry_7_03_03_coordinates : sparsePolynomial 81 rawEntry_7_03_03=rawStandardCoordinates 3 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_03,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_03_physical : invariantSubst (rawCoordinate 7 3 3)=rawStandardPolynomial 3 3 := by
  rw [rawCoordinate_sparse 7 3 3 rawEntry_7_03_03 rawEntry_7_03_03_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_03)=_
  rw [rawEntry_7_03_03_coordinates]
  exact rawStandard_subst 3 3
def rawEntry_7_03_04 : SparseEntry := [(26,-108),(28,36)]
theorem rawEntry_7_03_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 4=sparseCoefficient rawEntry_7_03_04 r := by decide +kernel
theorem rawEntry_7_03_04_coordinates : sparsePolynomial 81 rawEntry_7_03_04=rawStandardCoordinates 3 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_04,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_04_physical : invariantSubst (rawCoordinate 7 3 4)=rawStandardPolynomial 3 4 := by
  rw [rawCoordinate_sparse 7 3 4 rawEntry_7_03_04 rawEntry_7_03_04_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_04)=_
  rw [rawEntry_7_03_04_coordinates]
  exact rawStandard_subst 3 4
theorem rawEntry_7_04_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 3=sparseCoefficient rawEntry_7_03_04 r := by decide +kernel
theorem rawEntry_7_04_03_physical : invariantSubst (rawCoordinate 7 4 3)=rawStandardPolynomial 4 3 := by
  have hh : rawCoordinate 7 4 3=rawCoordinate 7 3 4 := by
    rw [rawCoordinate_sparse 7 4 3 rawEntry_7_03_04 rawEntry_7_04_03_data,rawCoordinate_sparse 7 3 4 rawEntry_7_03_04 rawEntry_7_03_04_data]
  rw [hh,rawEntry_7_03_04_physical]
  exact rawStandardPolynomial_symm 3 4
def rawEntry_7_03_05 : SparseEntry := [(27,-108),(29,36)]
theorem rawEntry_7_03_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 5=sparseCoefficient rawEntry_7_03_05 r := by decide +kernel
theorem rawEntry_7_03_05_coordinates : sparsePolynomial 81 rawEntry_7_03_05=rawStandardCoordinates 3 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_05_physical : invariantSubst (rawCoordinate 7 3 5)=rawStandardPolynomial 3 5 := by
  rw [rawCoordinate_sparse 7 3 5 rawEntry_7_03_05 rawEntry_7_03_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_05)=_
  rw [rawEntry_7_03_05_coordinates]
  exact rawStandard_subst 3 5
theorem rawEntry_7_05_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 3=sparseCoefficient rawEntry_7_03_05 r := by decide +kernel
theorem rawEntry_7_05_03_physical : invariantSubst (rawCoordinate 7 5 3)=rawStandardPolynomial 5 3 := by
  have hh : rawCoordinate 7 5 3=rawCoordinate 7 3 5 := by
    rw [rawCoordinate_sparse 7 5 3 rawEntry_7_03_05 rawEntry_7_05_03_data,rawCoordinate_sparse 7 3 5 rawEntry_7_03_05 rawEntry_7_03_05_data]
  rw [hh,rawEntry_7_03_05_physical]
  exact rawStandardPolynomial_symm 3 5
def rawEntry_7_03_06 : SparseEntry := [(29,-108),(30,36)]
theorem rawEntry_7_03_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 6=sparseCoefficient rawEntry_7_03_06 r := by decide +kernel
theorem rawEntry_7_03_06_coordinates : sparsePolynomial 81 rawEntry_7_03_06=rawStandardCoordinates 3 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_06_physical : invariantSubst (rawCoordinate 7 3 6)=rawStandardPolynomial 3 6 := by
  rw [rawCoordinate_sparse 7 3 6 rawEntry_7_03_06 rawEntry_7_03_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_06)=_
  rw [rawEntry_7_03_06_coordinates]
  exact rawStandard_subst 3 6
theorem rawEntry_7_06_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 3=sparseCoefficient rawEntry_7_03_06 r := by decide +kernel
theorem rawEntry_7_06_03_physical : invariantSubst (rawCoordinate 7 6 3)=rawStandardPolynomial 6 3 := by
  have hh : rawCoordinate 7 6 3=rawCoordinate 7 3 6 := by
    rw [rawCoordinate_sparse 7 6 3 rawEntry_7_03_06 rawEntry_7_06_03_data,rawCoordinate_sparse 7 3 6 rawEntry_7_03_06 rawEntry_7_03_06_data]
  rw [hh,rawEntry_7_03_06_physical]
  exact rawStandardPolynomial_symm 3 6
def rawEntry_7_03_07 : SparseEntry := [(35,-108),(37,36)]
theorem rawEntry_7_03_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 7=sparseCoefficient rawEntry_7_03_07 r := by decide +kernel
theorem rawEntry_7_03_07_coordinates : sparsePolynomial 81 rawEntry_7_03_07=rawStandardCoordinates 3 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_07_physical : invariantSubst (rawCoordinate 7 3 7)=rawStandardPolynomial 3 7 := by
  rw [rawCoordinate_sparse 7 3 7 rawEntry_7_03_07 rawEntry_7_03_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_07)=_
  rw [rawEntry_7_03_07_coordinates]
  exact rawStandard_subst 3 7
theorem rawEntry_7_07_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 3=sparseCoefficient rawEntry_7_03_07 r := by decide +kernel
theorem rawEntry_7_07_03_physical : invariantSubst (rawCoordinate 7 7 3)=rawStandardPolynomial 7 3 := by
  have hh : rawCoordinate 7 7 3=rawCoordinate 7 3 7 := by
    rw [rawCoordinate_sparse 7 7 3 rawEntry_7_03_07 rawEntry_7_07_03_data,rawCoordinate_sparse 7 3 7 rawEntry_7_03_07 rawEntry_7_03_07_data]
  rw [hh,rawEntry_7_03_07_physical]
  exact rawStandardPolynomial_symm 3 7
def rawEntry_7_03_08 : SparseEntry := [(36,-108),(38,36)]
theorem rawEntry_7_03_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 8=sparseCoefficient rawEntry_7_03_08 r := by decide +kernel
theorem rawEntry_7_03_08_coordinates : sparsePolynomial 81 rawEntry_7_03_08=rawStandardCoordinates 3 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_08_physical : invariantSubst (rawCoordinate 7 3 8)=rawStandardPolynomial 3 8 := by
  rw [rawCoordinate_sparse 7 3 8 rawEntry_7_03_08 rawEntry_7_03_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_08)=_
  rw [rawEntry_7_03_08_coordinates]
  exact rawStandard_subst 3 8
theorem rawEntry_7_08_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 3=sparseCoefficient rawEntry_7_03_08 r := by decide +kernel
theorem rawEntry_7_08_03_physical : invariantSubst (rawCoordinate 7 8 3)=rawStandardPolynomial 8 3 := by
  have hh : rawCoordinate 7 8 3=rawCoordinate 7 3 8 := by
    rw [rawCoordinate_sparse 7 8 3 rawEntry_7_03_08 rawEntry_7_08_03_data,rawCoordinate_sparse 7 3 8 rawEntry_7_03_08 rawEntry_7_03_08_data]
  rw [hh,rawEntry_7_03_08_physical]
  exact rawStandardPolynomial_symm 3 8
def rawEntry_7_03_09 : SparseEntry := [(37,-108),(39,36)]
theorem rawEntry_7_03_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 9=sparseCoefficient rawEntry_7_03_09 r := by decide +kernel
theorem rawEntry_7_03_09_coordinates : sparsePolynomial 81 rawEntry_7_03_09=rawStandardCoordinates 3 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_09_physical : invariantSubst (rawCoordinate 7 3 9)=rawStandardPolynomial 3 9 := by
  rw [rawCoordinate_sparse 7 3 9 rawEntry_7_03_09 rawEntry_7_03_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_09)=_
  rw [rawEntry_7_03_09_coordinates]
  exact rawStandard_subst 3 9
theorem rawEntry_7_09_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 3=sparseCoefficient rawEntry_7_03_09 r := by decide +kernel
theorem rawEntry_7_09_03_physical : invariantSubst (rawCoordinate 7 9 3)=rawStandardPolynomial 9 3 := by
  have hh : rawCoordinate 7 9 3=rawCoordinate 7 3 9 := by
    rw [rawCoordinate_sparse 7 9 3 rawEntry_7_03_09 rawEntry_7_09_03_data,rawCoordinate_sparse 7 3 9 rawEntry_7_03_09 rawEntry_7_03_09_data]
  rw [hh,rawEntry_7_03_09_physical]
  exact rawStandardPolynomial_symm 3 9
def rawEntry_7_03_10 : SparseEntry := [(39,-108),(40,36)]
theorem rawEntry_7_03_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 10=sparseCoefficient rawEntry_7_03_10 r := by decide +kernel
theorem rawEntry_7_03_10_coordinates : sparsePolynomial 81 rawEntry_7_03_10=rawStandardCoordinates 3 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_10_physical : invariantSubst (rawCoordinate 7 3 10)=rawStandardPolynomial 3 10 := by
  rw [rawCoordinate_sparse 7 3 10 rawEntry_7_03_10 rawEntry_7_03_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_10)=_
  rw [rawEntry_7_03_10_coordinates]
  exact rawStandard_subst 3 10
theorem rawEntry_7_10_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 3=sparseCoefficient rawEntry_7_03_10 r := by decide +kernel
theorem rawEntry_7_10_03_physical : invariantSubst (rawCoordinate 7 10 3)=rawStandardPolynomial 10 3 := by
  have hh : rawCoordinate 7 10 3=rawCoordinate 7 3 10 := by
    rw [rawCoordinate_sparse 7 10 3 rawEntry_7_03_10 rawEntry_7_10_03_data,rawCoordinate_sparse 7 3 10 rawEntry_7_03_10 rawEntry_7_03_10_data]
  rw [hh,rawEntry_7_03_10_physical]
  exact rawStandardPolynomial_symm 3 10
def rawEntry_7_03_11 : SparseEntry := [(13,162),(14,-54),(15,12)]
theorem rawEntry_7_03_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 11=sparseCoefficient rawEntry_7_03_11 r := by decide +kernel
theorem rawEntry_7_03_11_coordinates : sparsePolynomial 81 rawEntry_7_03_11=rawStandardCoordinates 3 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_11_physical : invariantSubst (rawCoordinate 7 3 11)=rawStandardPolynomial 3 11 := by
  rw [rawCoordinate_sparse 7 3 11 rawEntry_7_03_11 rawEntry_7_03_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_11)=_
  rw [rawEntry_7_03_11_coordinates]
  exact rawStandard_subst 3 11
theorem rawEntry_7_11_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 3=sparseCoefficient rawEntry_7_03_11 r := by decide +kernel
theorem rawEntry_7_11_03_physical : invariantSubst (rawCoordinate 7 11 3)=rawStandardPolynomial 11 3 := by
  have hh : rawCoordinate 7 11 3=rawCoordinate 7 3 11 := by
    rw [rawCoordinate_sparse 7 11 3 rawEntry_7_03_11 rawEntry_7_11_03_data,rawCoordinate_sparse 7 3 11 rawEntry_7_03_11 rawEntry_7_03_11_data]
  rw [hh,rawEntry_7_03_11_physical]
  exact rawStandardPolynomial_symm 3 11
end ThomsonNegative.Certificate.Bridges
