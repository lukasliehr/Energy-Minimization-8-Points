import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_03_12 : SparseEntry := [(20,162),(21,-54),(22,12)]
theorem rawEntry_7_03_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 12=sparseCoefficient rawEntry_7_03_12 r := by decide +kernel
theorem rawEntry_7_03_12_coordinates : sparsePolynomial 81 rawEntry_7_03_12=rawStandardCoordinates 3 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_12_physical : invariantSubst (rawCoordinate 7 3 12)=rawStandardPolynomial 3 12 := by
  rw [rawCoordinate_sparse 7 3 12 rawEntry_7_03_12 rawEntry_7_03_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_12)=_
  rw [rawEntry_7_03_12_coordinates]
  exact rawStandard_subst 3 12
theorem rawEntry_7_12_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 3=sparseCoefficient rawEntry_7_03_12 r := by decide +kernel
theorem rawEntry_7_12_03_physical : invariantSubst (rawCoordinate 7 12 3)=rawStandardPolynomial 12 3 := by
  have hh : rawCoordinate 7 12 3=rawCoordinate 7 3 12 := by
    rw [rawCoordinate_sparse 7 12 3 rawEntry_7_03_12 rawEntry_7_12_03_data,rawCoordinate_sparse 7 3 12 rawEntry_7_03_12 rawEntry_7_03_12_data]
  rw [hh,rawEntry_7_03_12_physical]
  exact rawStandardPolynomial_symm 3 12
def rawEntry_7_03_13 : SparseEntry := [(26,162),(27,-54),(29,12)]
theorem rawEntry_7_03_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 13=sparseCoefficient rawEntry_7_03_13 r := by decide +kernel
theorem rawEntry_7_03_13_coordinates : sparsePolynomial 81 rawEntry_7_03_13=rawStandardCoordinates 3 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_13_physical : invariantSubst (rawCoordinate 7 3 13)=rawStandardPolynomial 3 13 := by
  rw [rawCoordinate_sparse 7 3 13 rawEntry_7_03_13 rawEntry_7_03_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_13)=_
  rw [rawEntry_7_03_13_coordinates]
  exact rawStandard_subst 3 13
theorem rawEntry_7_13_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 3=sparseCoefficient rawEntry_7_03_13 r := by decide +kernel
theorem rawEntry_7_13_03_physical : invariantSubst (rawCoordinate 7 13 3)=rawStandardPolynomial 13 3 := by
  have hh : rawCoordinate 7 13 3=rawCoordinate 7 3 13 := by
    rw [rawCoordinate_sparse 7 13 3 rawEntry_7_03_13 rawEntry_7_13_03_data,rawCoordinate_sparse 7 3 13 rawEntry_7_03_13 rawEntry_7_03_13_data]
  rw [hh,rawEntry_7_03_13_physical]
  exact rawStandardPolynomial_symm 3 13
def rawEntry_7_03_14 : SparseEntry := [(28,162),(29,-54),(30,12)]
theorem rawEntry_7_03_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 14=sparseCoefficient rawEntry_7_03_14 r := by decide +kernel
theorem rawEntry_7_03_14_coordinates : sparsePolynomial 81 rawEntry_7_03_14=rawStandardCoordinates 3 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_14_physical : invariantSubst (rawCoordinate 7 3 14)=rawStandardPolynomial 3 14 := by
  rw [rawCoordinate_sparse 7 3 14 rawEntry_7_03_14 rawEntry_7_03_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_14)=_
  rw [rawEntry_7_03_14_coordinates]
  exact rawStandard_subst 3 14
theorem rawEntry_7_14_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 3=sparseCoefficient rawEntry_7_03_14 r := by decide +kernel
theorem rawEntry_7_14_03_physical : invariantSubst (rawCoordinate 7 14 3)=rawStandardPolynomial 14 3 := by
  have hh : rawCoordinate 7 14 3=rawCoordinate 7 3 14 := by
    rw [rawCoordinate_sparse 7 14 3 rawEntry_7_03_14 rawEntry_7_14_03_data,rawCoordinate_sparse 7 3 14 rawEntry_7_03_14 rawEntry_7_03_14_data]
  rw [hh,rawEntry_7_03_14_physical]
  exact rawStandardPolynomial_symm 3 14
def rawEntry_7_03_15 : SparseEntry := [(34,162),(36,-54),(38,12)]
theorem rawEntry_7_03_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 15=sparseCoefficient rawEntry_7_03_15 r := by decide +kernel
theorem rawEntry_7_03_15_coordinates : sparsePolynomial 81 rawEntry_7_03_15=rawStandardCoordinates 3 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_15_physical : invariantSubst (rawCoordinate 7 3 15)=rawStandardPolynomial 3 15 := by
  rw [rawCoordinate_sparse 7 3 15 rawEntry_7_03_15 rawEntry_7_03_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_15)=_
  rw [rawEntry_7_03_15_coordinates]
  exact rawStandard_subst 3 15
theorem rawEntry_7_15_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 3=sparseCoefficient rawEntry_7_03_15 r := by decide +kernel
theorem rawEntry_7_15_03_physical : invariantSubst (rawCoordinate 7 15 3)=rawStandardPolynomial 15 3 := by
  have hh : rawCoordinate 7 15 3=rawCoordinate 7 3 15 := by
    rw [rawCoordinate_sparse 7 15 3 rawEntry_7_03_15 rawEntry_7_15_03_data,rawCoordinate_sparse 7 3 15 rawEntry_7_03_15 rawEntry_7_03_15_data]
  rw [hh,rawEntry_7_03_15_physical]
  exact rawStandardPolynomial_symm 3 15
def rawEntry_7_03_16 : SparseEntry := [(36,162),(37,-54),(39,12)]
theorem rawEntry_7_03_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 16=sparseCoefficient rawEntry_7_03_16 r := by decide +kernel
theorem rawEntry_7_03_16_coordinates : sparsePolynomial 81 rawEntry_7_03_16=rawStandardCoordinates 3 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_16_physical : invariantSubst (rawCoordinate 7 3 16)=rawStandardPolynomial 3 16 := by
  rw [rawCoordinate_sparse 7 3 16 rawEntry_7_03_16 rawEntry_7_03_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_16)=_
  rw [rawEntry_7_03_16_coordinates]
  exact rawStandard_subst 3 16
theorem rawEntry_7_16_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 3=sparseCoefficient rawEntry_7_03_16 r := by decide +kernel
theorem rawEntry_7_16_03_physical : invariantSubst (rawCoordinate 7 16 3)=rawStandardPolynomial 16 3 := by
  have hh : rawCoordinate 7 16 3=rawCoordinate 7 3 16 := by
    rw [rawCoordinate_sparse 7 16 3 rawEntry_7_03_16 rawEntry_7_16_03_data,rawCoordinate_sparse 7 3 16 rawEntry_7_03_16 rawEntry_7_03_16_data]
  rw [hh,rawEntry_7_03_16_physical]
  exact rawStandardPolynomial_symm 3 16
def rawEntry_7_03_17 : SparseEntry := [(38,162),(39,-54),(40,12)]
theorem rawEntry_7_03_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 3 17=sparseCoefficient rawEntry_7_03_17 r := by decide +kernel
theorem rawEntry_7_03_17_coordinates : sparsePolynomial 81 rawEntry_7_03_17=rawStandardCoordinates 3 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_03_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_03_17_physical : invariantSubst (rawCoordinate 7 3 17)=rawStandardPolynomial 3 17 := by
  rw [rawCoordinate_sparse 7 3 17 rawEntry_7_03_17 rawEntry_7_03_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_03_17)=_
  rw [rawEntry_7_03_17_coordinates]
  exact rawStandard_subst 3 17
theorem rawEntry_7_17_03_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 3=sparseCoefficient rawEntry_7_03_17 r := by decide +kernel
theorem rawEntry_7_17_03_physical : invariantSubst (rawCoordinate 7 17 3)=rawStandardPolynomial 17 3 := by
  have hh : rawCoordinate 7 17 3=rawCoordinate 7 3 17 := by
    rw [rawCoordinate_sparse 7 17 3 rawEntry_7_03_17 rawEntry_7_17_03_data,rawCoordinate_sparse 7 3 17 rawEntry_7_03_17 rawEntry_7_03_17_data]
  rw [hh,rawEntry_7_03_17_physical]
  exact rawStandardPolynomial_symm 3 17
def rawEntry_7_04_04 : SparseEntry := [(31,-108),(34,36)]
theorem rawEntry_7_04_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 4=sparseCoefficient rawEntry_7_04_04 r := by decide +kernel
theorem rawEntry_7_04_04_coordinates : sparsePolynomial 81 rawEntry_7_04_04=rawStandardCoordinates 4 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_04,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_04_physical : invariantSubst (rawCoordinate 7 4 4)=rawStandardPolynomial 4 4 := by
  rw [rawCoordinate_sparse 7 4 4 rawEntry_7_04_04 rawEntry_7_04_04_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_04)=_
  rw [rawEntry_7_04_04_coordinates]
  exact rawStandard_subst 4 4
def rawEntry_7_04_05 : SparseEntry := [(33,-108),(36,36)]
theorem rawEntry_7_04_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 5=sparseCoefficient rawEntry_7_04_05 r := by decide +kernel
theorem rawEntry_7_04_05_coordinates : sparsePolynomial 81 rawEntry_7_04_05=rawStandardCoordinates 4 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_05_physical : invariantSubst (rawCoordinate 7 4 5)=rawStandardPolynomial 4 5 := by
  rw [rawCoordinate_sparse 7 4 5 rawEntry_7_04_05 rawEntry_7_04_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_05)=_
  rw [rawEntry_7_04_05_coordinates]
  exact rawStandard_subst 4 5
theorem rawEntry_7_05_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 4=sparseCoefficient rawEntry_7_04_05 r := by decide +kernel
theorem rawEntry_7_05_04_physical : invariantSubst (rawCoordinate 7 5 4)=rawStandardPolynomial 5 4 := by
  have hh : rawCoordinate 7 5 4=rawCoordinate 7 4 5 := by
    rw [rawCoordinate_sparse 7 5 4 rawEntry_7_04_05 rawEntry_7_05_04_data,rawCoordinate_sparse 7 4 5 rawEntry_7_04_05 rawEntry_7_04_05_data]
  rw [hh,rawEntry_7_04_05_physical]
  exact rawStandardPolynomial_symm 4 5
def rawEntry_7_04_06 : SparseEntry := [(36,-108),(38,36)]
theorem rawEntry_7_04_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 6=sparseCoefficient rawEntry_7_04_06 r := by decide +kernel
theorem rawEntry_7_04_06_coordinates : sparsePolynomial 81 rawEntry_7_04_06=rawStandardCoordinates 4 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_06_physical : invariantSubst (rawCoordinate 7 4 6)=rawStandardPolynomial 4 6 := by
  rw [rawCoordinate_sparse 7 4 6 rawEntry_7_04_06 rawEntry_7_04_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_06)=_
  rw [rawEntry_7_04_06_coordinates]
  exact rawStandard_subst 4 6
theorem rawEntry_7_06_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 4=sparseCoefficient rawEntry_7_04_06 r := by decide +kernel
theorem rawEntry_7_06_04_physical : invariantSubst (rawCoordinate 7 6 4)=rawStandardPolynomial 6 4 := by
  have hh : rawCoordinate 7 6 4=rawCoordinate 7 4 6 := by
    rw [rawCoordinate_sparse 7 6 4 rawEntry_7_04_06 rawEntry_7_06_04_data,rawCoordinate_sparse 7 4 6 rawEntry_7_04_06 rawEntry_7_04_06_data]
  rw [hh,rawEntry_7_04_06_physical]
  exact rawStandardPolynomial_symm 4 6
def rawEntry_7_04_07 : SparseEntry := [(42,-108),(45,36)]
theorem rawEntry_7_04_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 7=sparseCoefficient rawEntry_7_04_07 r := by decide +kernel
theorem rawEntry_7_04_07_coordinates : sparsePolynomial 81 rawEntry_7_04_07=rawStandardCoordinates 4 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_07_physical : invariantSubst (rawCoordinate 7 4 7)=rawStandardPolynomial 4 7 := by
  rw [rawCoordinate_sparse 7 4 7 rawEntry_7_04_07 rawEntry_7_04_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_07)=_
  rw [rawEntry_7_04_07_coordinates]
  exact rawStandard_subst 4 7
theorem rawEntry_7_07_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 4=sparseCoefficient rawEntry_7_04_07 r := by decide +kernel
theorem rawEntry_7_07_04_physical : invariantSubst (rawCoordinate 7 7 4)=rawStandardPolynomial 7 4 := by
  have hh : rawCoordinate 7 7 4=rawCoordinate 7 4 7 := by
    rw [rawCoordinate_sparse 7 7 4 rawEntry_7_04_07 rawEntry_7_07_04_data,rawCoordinate_sparse 7 4 7 rawEntry_7_04_07 rawEntry_7_04_07_data]
  rw [hh,rawEntry_7_04_07_physical]
  exact rawStandardPolynomial_symm 4 7
def rawEntry_7_04_08 : SparseEntry := [(43,-108),(46,36)]
theorem rawEntry_7_04_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 8=sparseCoefficient rawEntry_7_04_08 r := by decide +kernel
theorem rawEntry_7_04_08_coordinates : sparsePolynomial 81 rawEntry_7_04_08=rawStandardCoordinates 4 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_08_physical : invariantSubst (rawCoordinate 7 4 8)=rawStandardPolynomial 4 8 := by
  rw [rawCoordinate_sparse 7 4 8 rawEntry_7_04_08 rawEntry_7_04_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_08)=_
  rw [rawEntry_7_04_08_coordinates]
  exact rawStandard_subst 4 8
theorem rawEntry_7_08_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 4=sparseCoefficient rawEntry_7_04_08 r := by decide +kernel
theorem rawEntry_7_08_04_physical : invariantSubst (rawCoordinate 7 8 4)=rawStandardPolynomial 8 4 := by
  have hh : rawCoordinate 7 8 4=rawCoordinate 7 4 8 := by
    rw [rawCoordinate_sparse 7 8 4 rawEntry_7_04_08 rawEntry_7_08_04_data,rawCoordinate_sparse 7 4 8 rawEntry_7_04_08 rawEntry_7_04_08_data]
  rw [hh,rawEntry_7_04_08_physical]
  exact rawStandardPolynomial_symm 4 8
def rawEntry_7_04_09 : SparseEntry := [(45,-108),(48,36)]
theorem rawEntry_7_04_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 9=sparseCoefficient rawEntry_7_04_09 r := by decide +kernel
theorem rawEntry_7_04_09_coordinates : sparsePolynomial 81 rawEntry_7_04_09=rawStandardCoordinates 4 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_09_physical : invariantSubst (rawCoordinate 7 4 9)=rawStandardPolynomial 4 9 := by
  rw [rawCoordinate_sparse 7 4 9 rawEntry_7_04_09 rawEntry_7_04_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_09)=_
  rw [rawEntry_7_04_09_coordinates]
  exact rawStandard_subst 4 9
theorem rawEntry_7_09_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 4=sparseCoefficient rawEntry_7_04_09 r := by decide +kernel
theorem rawEntry_7_09_04_physical : invariantSubst (rawCoordinate 7 9 4)=rawStandardPolynomial 9 4 := by
  have hh : rawCoordinate 7 9 4=rawCoordinate 7 4 9 := by
    rw [rawCoordinate_sparse 7 9 4 rawEntry_7_04_09 rawEntry_7_09_04_data,rawCoordinate_sparse 7 4 9 rawEntry_7_04_09 rawEntry_7_04_09_data]
  rw [hh,rawEntry_7_04_09_physical]
  exact rawStandardPolynomial_symm 4 9
def rawEntry_7_04_10 : SparseEntry := [(48,-108),(50,36)]
theorem rawEntry_7_04_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 10=sparseCoefficient rawEntry_7_04_10 r := by decide +kernel
theorem rawEntry_7_04_10_coordinates : sparsePolynomial 81 rawEntry_7_04_10=rawStandardCoordinates 4 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_10_physical : invariantSubst (rawCoordinate 7 4 10)=rawStandardPolynomial 4 10 := by
  rw [rawCoordinate_sparse 7 4 10 rawEntry_7_04_10 rawEntry_7_04_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_10)=_
  rw [rawEntry_7_04_10_coordinates]
  exact rawStandard_subst 4 10
theorem rawEntry_7_10_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 4=sparseCoefficient rawEntry_7_04_10 r := by decide +kernel
theorem rawEntry_7_10_04_physical : invariantSubst (rawCoordinate 7 10 4)=rawStandardPolynomial 10 4 := by
  have hh : rawCoordinate 7 10 4=rawCoordinate 7 4 10 := by
    rw [rawCoordinate_sparse 7 10 4 rawEntry_7_04_10 rawEntry_7_10_04_data,rawCoordinate_sparse 7 4 10 rawEntry_7_04_10 rawEntry_7_04_10_data]
  rw [hh,rawEntry_7_04_10_physical]
  exact rawStandardPolynomial_symm 4 10
def rawEntry_7_04_11 : SparseEntry := [(16,162),(18,-54),(20,12)]
theorem rawEntry_7_04_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 11=sparseCoefficient rawEntry_7_04_11 r := by decide +kernel
theorem rawEntry_7_04_11_coordinates : sparsePolynomial 81 rawEntry_7_04_11=rawStandardCoordinates 4 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_11_physical : invariantSubst (rawCoordinate 7 4 11)=rawStandardPolynomial 4 11 := by
  rw [rawCoordinate_sparse 7 4 11 rawEntry_7_04_11 rawEntry_7_04_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_11)=_
  rw [rawEntry_7_04_11_coordinates]
  exact rawStandard_subst 4 11
theorem rawEntry_7_11_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 4=sparseCoefficient rawEntry_7_04_11 r := by decide +kernel
theorem rawEntry_7_11_04_physical : invariantSubst (rawCoordinate 7 11 4)=rawStandardPolynomial 11 4 := by
  have hh : rawCoordinate 7 11 4=rawCoordinate 7 4 11 := by
    rw [rawCoordinate_sparse 7 11 4 rawEntry_7_04_11 rawEntry_7_11_04_data,rawCoordinate_sparse 7 4 11 rawEntry_7_04_11 rawEntry_7_04_11_data]
  rw [hh,rawEntry_7_04_11_physical]
  exact rawStandardPolynomial_symm 4 11
def rawEntry_7_04_12 : SparseEntry := [(24,162),(26,-54),(28,12)]
theorem rawEntry_7_04_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 12=sparseCoefficient rawEntry_7_04_12 r := by decide +kernel
theorem rawEntry_7_04_12_coordinates : sparsePolynomial 81 rawEntry_7_04_12=rawStandardCoordinates 4 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_12_physical : invariantSubst (rawCoordinate 7 4 12)=rawStandardPolynomial 4 12 := by
  rw [rawCoordinate_sparse 7 4 12 rawEntry_7_04_12 rawEntry_7_04_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_12)=_
  rw [rawEntry_7_04_12_coordinates]
  exact rawStandard_subst 4 12
theorem rawEntry_7_12_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 4=sparseCoefficient rawEntry_7_04_12 r := by decide +kernel
theorem rawEntry_7_12_04_physical : invariantSubst (rawCoordinate 7 12 4)=rawStandardPolynomial 12 4 := by
  have hh : rawCoordinate 7 12 4=rawCoordinate 7 4 12 := by
    rw [rawCoordinate_sparse 7 12 4 rawEntry_7_04_12 rawEntry_7_12_04_data,rawCoordinate_sparse 7 4 12 rawEntry_7_04_12 rawEntry_7_04_12_data]
  rw [hh,rawEntry_7_04_12_physical]
  exact rawStandardPolynomial_symm 4 12
def rawEntry_7_04_13 : SparseEntry := [(31,162),(33,-54),(36,12)]
theorem rawEntry_7_04_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 13=sparseCoefficient rawEntry_7_04_13 r := by decide +kernel
theorem rawEntry_7_04_13_coordinates : sparsePolynomial 81 rawEntry_7_04_13=rawStandardCoordinates 4 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_13_physical : invariantSubst (rawCoordinate 7 4 13)=rawStandardPolynomial 4 13 := by
  rw [rawCoordinate_sparse 7 4 13 rawEntry_7_04_13 rawEntry_7_04_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_13)=_
  rw [rawEntry_7_04_13_coordinates]
  exact rawStandard_subst 4 13
theorem rawEntry_7_13_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 4=sparseCoefficient rawEntry_7_04_13 r := by decide +kernel
theorem rawEntry_7_13_04_physical : invariantSubst (rawCoordinate 7 13 4)=rawStandardPolynomial 13 4 := by
  have hh : rawCoordinate 7 13 4=rawCoordinate 7 4 13 := by
    rw [rawCoordinate_sparse 7 13 4 rawEntry_7_04_13 rawEntry_7_13_04_data,rawCoordinate_sparse 7 4 13 rawEntry_7_04_13 rawEntry_7_04_13_data]
  rw [hh,rawEntry_7_04_13_physical]
  exact rawStandardPolynomial_symm 4 13
def rawEntry_7_04_14 : SparseEntry := [(34,162),(36,-54),(38,12)]
theorem rawEntry_7_04_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 14=sparseCoefficient rawEntry_7_04_14 r := by decide +kernel
theorem rawEntry_7_04_14_coordinates : sparsePolynomial 81 rawEntry_7_04_14=rawStandardCoordinates 4 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_14_physical : invariantSubst (rawCoordinate 7 4 14)=rawStandardPolynomial 4 14 := by
  rw [rawCoordinate_sparse 7 4 14 rawEntry_7_04_14 rawEntry_7_04_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_14)=_
  rw [rawEntry_7_04_14_coordinates]
  exact rawStandard_subst 4 14
theorem rawEntry_7_14_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 4=sparseCoefficient rawEntry_7_04_14 r := by decide +kernel
theorem rawEntry_7_14_04_physical : invariantSubst (rawCoordinate 7 14 4)=rawStandardPolynomial 14 4 := by
  have hh : rawCoordinate 7 14 4=rawCoordinate 7 4 14 := by
    rw [rawCoordinate_sparse 7 14 4 rawEntry_7_04_14 rawEntry_7_14_04_data,rawCoordinate_sparse 7 4 14 rawEntry_7_04_14 rawEntry_7_04_14_data]
  rw [hh,rawEntry_7_04_14_physical]
  exact rawStandardPolynomial_symm 4 14
def rawEntry_7_04_15 : SparseEntry := [(41,162),(43,-54),(46,12)]
theorem rawEntry_7_04_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 15=sparseCoefficient rawEntry_7_04_15 r := by decide +kernel
theorem rawEntry_7_04_15_coordinates : sparsePolynomial 81 rawEntry_7_04_15=rawStandardCoordinates 4 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_15_physical : invariantSubst (rawCoordinate 7 4 15)=rawStandardPolynomial 4 15 := by
  rw [rawCoordinate_sparse 7 4 15 rawEntry_7_04_15 rawEntry_7_04_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_15)=_
  rw [rawEntry_7_04_15_coordinates]
  exact rawStandard_subst 4 15
theorem rawEntry_7_15_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 4=sparseCoefficient rawEntry_7_04_15 r := by decide +kernel
theorem rawEntry_7_15_04_physical : invariantSubst (rawCoordinate 7 15 4)=rawStandardPolynomial 15 4 := by
  have hh : rawCoordinate 7 15 4=rawCoordinate 7 4 15 := by
    rw [rawCoordinate_sparse 7 15 4 rawEntry_7_04_15 rawEntry_7_15_04_data,rawCoordinate_sparse 7 4 15 rawEntry_7_04_15 rawEntry_7_04_15_data]
  rw [hh,rawEntry_7_04_15_physical]
  exact rawStandardPolynomial_symm 4 15
def rawEntry_7_04_16 : SparseEntry := [(43,162),(45,-54),(48,12)]
theorem rawEntry_7_04_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 16=sparseCoefficient rawEntry_7_04_16 r := by decide +kernel
theorem rawEntry_7_04_16_coordinates : sparsePolynomial 81 rawEntry_7_04_16=rawStandardCoordinates 4 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_16_physical : invariantSubst (rawCoordinate 7 4 16)=rawStandardPolynomial 4 16 := by
  rw [rawCoordinate_sparse 7 4 16 rawEntry_7_04_16 rawEntry_7_04_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_16)=_
  rw [rawEntry_7_04_16_coordinates]
  exact rawStandard_subst 4 16
theorem rawEntry_7_16_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 4=sparseCoefficient rawEntry_7_04_16 r := by decide +kernel
theorem rawEntry_7_16_04_physical : invariantSubst (rawCoordinate 7 16 4)=rawStandardPolynomial 16 4 := by
  have hh : rawCoordinate 7 16 4=rawCoordinate 7 4 16 := by
    rw [rawCoordinate_sparse 7 16 4 rawEntry_7_04_16 rawEntry_7_16_04_data,rawCoordinate_sparse 7 4 16 rawEntry_7_04_16 rawEntry_7_04_16_data]
  rw [hh,rawEntry_7_04_16_physical]
  exact rawStandardPolynomial_symm 4 16
def rawEntry_7_04_17 : SparseEntry := [(46,162),(48,-54),(50,12)]
theorem rawEntry_7_04_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 4 17=sparseCoefficient rawEntry_7_04_17 r := by decide +kernel
theorem rawEntry_7_04_17_coordinates : sparsePolynomial 81 rawEntry_7_04_17=rawStandardCoordinates 4 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_04_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_04_17_physical : invariantSubst (rawCoordinate 7 4 17)=rawStandardPolynomial 4 17 := by
  rw [rawCoordinate_sparse 7 4 17 rawEntry_7_04_17 rawEntry_7_04_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_04_17)=_
  rw [rawEntry_7_04_17_coordinates]
  exact rawStandard_subst 4 17
theorem rawEntry_7_17_04_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 4=sparseCoefficient rawEntry_7_04_17 r := by decide +kernel
theorem rawEntry_7_17_04_physical : invariantSubst (rawCoordinate 7 17 4)=rawStandardPolynomial 17 4 := by
  have hh : rawCoordinate 7 17 4=rawCoordinate 7 4 17 := by
    rw [rawCoordinate_sparse 7 17 4 rawEntry_7_04_17 rawEntry_7_17_04_data,rawCoordinate_sparse 7 4 17 rawEntry_7_04_17 rawEntry_7_04_17_data]
  rw [hh,rawEntry_7_04_17_physical]
  exact rawStandardPolynomial_symm 4 17
end ThomsonNegative.Certificate.Bridges
