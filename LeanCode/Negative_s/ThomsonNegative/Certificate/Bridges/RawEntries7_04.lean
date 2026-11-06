import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_05_05 : SparseEntry := [(35,-108),(37,36)]
theorem rawEntry_7_05_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 5=sparseCoefficient rawEntry_7_05_05 r := by decide +kernel
theorem rawEntry_7_05_05_coordinates : sparsePolynomial 81 rawEntry_7_05_05=rawStandardCoordinates 5 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_05,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_05_physical : invariantSubst (rawCoordinate 7 5 5)=rawStandardPolynomial 5 5 := by
  rw [rawCoordinate_sparse 7 5 5 rawEntry_7_05_05 rawEntry_7_05_05_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_05)=_
  rw [rawEntry_7_05_05_coordinates]
  exact rawStandard_subst 5 5
def rawEntry_7_05_06 : SparseEntry := [(37,-108),(39,36)]
theorem rawEntry_7_05_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 6=sparseCoefficient rawEntry_7_05_06 r := by decide +kernel
theorem rawEntry_7_05_06_coordinates : sparsePolynomial 81 rawEntry_7_05_06=rawStandardCoordinates 5 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_06_physical : invariantSubst (rawCoordinate 7 5 6)=rawStandardPolynomial 5 6 := by
  rw [rawCoordinate_sparse 7 5 6 rawEntry_7_05_06 rawEntry_7_05_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_06)=_
  rw [rawEntry_7_05_06_coordinates]
  exact rawStandard_subst 5 6
theorem rawEntry_7_06_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 5=sparseCoefficient rawEntry_7_05_06 r := by decide +kernel
theorem rawEntry_7_06_05_physical : invariantSubst (rawCoordinate 7 6 5)=rawStandardPolynomial 6 5 := by
  have hh : rawCoordinate 7 6 5=rawCoordinate 7 5 6 := by
    rw [rawCoordinate_sparse 7 6 5 rawEntry_7_05_06 rawEntry_7_06_05_data,rawCoordinate_sparse 7 5 6 rawEntry_7_05_06 rawEntry_7_05_06_data]
  rw [hh,rawEntry_7_05_06_physical]
  exact rawStandardPolynomial_symm 5 6
def rawEntry_7_05_07 : SparseEntry := [(44,-108),(47,36)]
theorem rawEntry_7_05_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 7=sparseCoefficient rawEntry_7_05_07 r := by decide +kernel
theorem rawEntry_7_05_07_coordinates : sparsePolynomial 81 rawEntry_7_05_07=rawStandardCoordinates 5 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_07_physical : invariantSubst (rawCoordinate 7 5 7)=rawStandardPolynomial 5 7 := by
  rw [rawCoordinate_sparse 7 5 7 rawEntry_7_05_07 rawEntry_7_05_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_07)=_
  rw [rawEntry_7_05_07_coordinates]
  exact rawStandard_subst 5 7
theorem rawEntry_7_07_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 5=sparseCoefficient rawEntry_7_05_07 r := by decide +kernel
theorem rawEntry_7_07_05_physical : invariantSubst (rawCoordinate 7 7 5)=rawStandardPolynomial 7 5 := by
  have hh : rawCoordinate 7 7 5=rawCoordinate 7 5 7 := by
    rw [rawCoordinate_sparse 7 7 5 rawEntry_7_05_07 rawEntry_7_07_05_data,rawCoordinate_sparse 7 5 7 rawEntry_7_05_07 rawEntry_7_05_07_data]
  rw [hh,rawEntry_7_05_07_physical]
  exact rawStandardPolynomial_symm 5 7
def rawEntry_7_05_08 : SparseEntry := [(45,-108),(48,36)]
theorem rawEntry_7_05_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 8=sparseCoefficient rawEntry_7_05_08 r := by decide +kernel
theorem rawEntry_7_05_08_coordinates : sparsePolynomial 81 rawEntry_7_05_08=rawStandardCoordinates 5 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_08_physical : invariantSubst (rawCoordinate 7 5 8)=rawStandardPolynomial 5 8 := by
  rw [rawCoordinate_sparse 7 5 8 rawEntry_7_05_08 rawEntry_7_05_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_08)=_
  rw [rawEntry_7_05_08_coordinates]
  exact rawStandard_subst 5 8
theorem rawEntry_7_08_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 5=sparseCoefficient rawEntry_7_05_08 r := by decide +kernel
theorem rawEntry_7_08_05_physical : invariantSubst (rawCoordinate 7 8 5)=rawStandardPolynomial 8 5 := by
  have hh : rawCoordinate 7 8 5=rawCoordinate 7 5 8 := by
    rw [rawCoordinate_sparse 7 8 5 rawEntry_7_05_08 rawEntry_7_08_05_data,rawCoordinate_sparse 7 5 8 rawEntry_7_05_08 rawEntry_7_05_08_data]
  rw [hh,rawEntry_7_05_08_physical]
  exact rawStandardPolynomial_symm 5 8
def rawEntry_7_05_09 : SparseEntry := [(47,-108),(49,36)]
theorem rawEntry_7_05_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 9=sparseCoefficient rawEntry_7_05_09 r := by decide +kernel
theorem rawEntry_7_05_09_coordinates : sparsePolynomial 81 rawEntry_7_05_09=rawStandardCoordinates 5 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_09_physical : invariantSubst (rawCoordinate 7 5 9)=rawStandardPolynomial 5 9 := by
  rw [rawCoordinate_sparse 7 5 9 rawEntry_7_05_09 rawEntry_7_05_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_09)=_
  rw [rawEntry_7_05_09_coordinates]
  exact rawStandard_subst 5 9
theorem rawEntry_7_09_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 5=sparseCoefficient rawEntry_7_05_09 r := by decide +kernel
theorem rawEntry_7_09_05_physical : invariantSubst (rawCoordinate 7 9 5)=rawStandardPolynomial 9 5 := by
  have hh : rawCoordinate 7 9 5=rawCoordinate 7 5 9 := by
    rw [rawCoordinate_sparse 7 9 5 rawEntry_7_05_09 rawEntry_7_09_05_data,rawCoordinate_sparse 7 5 9 rawEntry_7_05_09 rawEntry_7_05_09_data]
  rw [hh,rawEntry_7_05_09_physical]
  exact rawStandardPolynomial_symm 5 9
def rawEntry_7_05_10 : SparseEntry := [(49,-108),(51,36)]
theorem rawEntry_7_05_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 10=sparseCoefficient rawEntry_7_05_10 r := by decide +kernel
theorem rawEntry_7_05_10_coordinates : sparsePolynomial 81 rawEntry_7_05_10=rawStandardCoordinates 5 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_10_physical : invariantSubst (rawCoordinate 7 5 10)=rawStandardPolynomial 5 10 := by
  rw [rawCoordinate_sparse 7 5 10 rawEntry_7_05_10 rawEntry_7_05_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_10)=_
  rw [rawEntry_7_05_10_coordinates]
  exact rawStandard_subst 5 10
theorem rawEntry_7_10_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 5=sparseCoefficient rawEntry_7_05_10 r := by decide +kernel
theorem rawEntry_7_10_05_physical : invariantSubst (rawCoordinate 7 10 5)=rawStandardPolynomial 10 5 := by
  have hh : rawCoordinate 7 10 5=rawCoordinate 7 5 10 := by
    rw [rawCoordinate_sparse 7 10 5 rawEntry_7_05_10 rawEntry_7_10_05_data,rawCoordinate_sparse 7 5 10 rawEntry_7_05_10 rawEntry_7_05_10_data]
  rw [hh,rawEntry_7_05_10_physical]
  exact rawStandardPolynomial_symm 5 10
def rawEntry_7_05_11 : SparseEntry := [(18,162),(19,-54),(21,12)]
theorem rawEntry_7_05_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 11=sparseCoefficient rawEntry_7_05_11 r := by decide +kernel
theorem rawEntry_7_05_11_coordinates : sparsePolynomial 81 rawEntry_7_05_11=rawStandardCoordinates 5 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_11_physical : invariantSubst (rawCoordinate 7 5 11)=rawStandardPolynomial 5 11 := by
  rw [rawCoordinate_sparse 7 5 11 rawEntry_7_05_11 rawEntry_7_05_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_11)=_
  rw [rawEntry_7_05_11_coordinates]
  exact rawStandard_subst 5 11
theorem rawEntry_7_11_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 5=sparseCoefficient rawEntry_7_05_11 r := by decide +kernel
theorem rawEntry_7_11_05_physical : invariantSubst (rawCoordinate 7 11 5)=rawStandardPolynomial 11 5 := by
  have hh : rawCoordinate 7 11 5=rawCoordinate 7 5 11 := by
    rw [rawCoordinate_sparse 7 11 5 rawEntry_7_05_11 rawEntry_7_11_05_data,rawCoordinate_sparse 7 5 11 rawEntry_7_05_11 rawEntry_7_05_11_data]
  rw [hh,rawEntry_7_05_11_physical]
  exact rawStandardPolynomial_symm 5 11
def rawEntry_7_05_12 : SparseEntry := [(26,162),(27,-54),(29,12)]
theorem rawEntry_7_05_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 12=sparseCoefficient rawEntry_7_05_12 r := by decide +kernel
theorem rawEntry_7_05_12_coordinates : sparsePolynomial 81 rawEntry_7_05_12=rawStandardCoordinates 5 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_12_physical : invariantSubst (rawCoordinate 7 5 12)=rawStandardPolynomial 5 12 := by
  rw [rawCoordinate_sparse 7 5 12 rawEntry_7_05_12 rawEntry_7_05_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_12)=_
  rw [rawEntry_7_05_12_coordinates]
  exact rawStandard_subst 5 12
theorem rawEntry_7_12_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 5=sparseCoefficient rawEntry_7_05_12 r := by decide +kernel
theorem rawEntry_7_12_05_physical : invariantSubst (rawCoordinate 7 12 5)=rawStandardPolynomial 12 5 := by
  have hh : rawCoordinate 7 12 5=rawCoordinate 7 5 12 := by
    rw [rawCoordinate_sparse 7 12 5 rawEntry_7_05_12 rawEntry_7_12_05_data,rawCoordinate_sparse 7 5 12 rawEntry_7_05_12 rawEntry_7_05_12_data]
  rw [hh,rawEntry_7_05_12_physical]
  exact rawStandardPolynomial_symm 5 12
def rawEntry_7_05_13 : SparseEntry := [(33,162),(35,-54),(37,12)]
theorem rawEntry_7_05_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 13=sparseCoefficient rawEntry_7_05_13 r := by decide +kernel
theorem rawEntry_7_05_13_coordinates : sparsePolynomial 81 rawEntry_7_05_13=rawStandardCoordinates 5 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_13_physical : invariantSubst (rawCoordinate 7 5 13)=rawStandardPolynomial 5 13 := by
  rw [rawCoordinate_sparse 7 5 13 rawEntry_7_05_13 rawEntry_7_05_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_13)=_
  rw [rawEntry_7_05_13_coordinates]
  exact rawStandard_subst 5 13
theorem rawEntry_7_13_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 5=sparseCoefficient rawEntry_7_05_13 r := by decide +kernel
theorem rawEntry_7_13_05_physical : invariantSubst (rawCoordinate 7 13 5)=rawStandardPolynomial 13 5 := by
  have hh : rawCoordinate 7 13 5=rawCoordinate 7 5 13 := by
    rw [rawCoordinate_sparse 7 13 5 rawEntry_7_05_13 rawEntry_7_13_05_data,rawCoordinate_sparse 7 5 13 rawEntry_7_05_13 rawEntry_7_05_13_data]
  rw [hh,rawEntry_7_05_13_physical]
  exact rawStandardPolynomial_symm 5 13
def rawEntry_7_05_14 : SparseEntry := [(36,162),(37,-54),(39,12)]
theorem rawEntry_7_05_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 14=sparseCoefficient rawEntry_7_05_14 r := by decide +kernel
theorem rawEntry_7_05_14_coordinates : sparsePolynomial 81 rawEntry_7_05_14=rawStandardCoordinates 5 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_14_physical : invariantSubst (rawCoordinate 7 5 14)=rawStandardPolynomial 5 14 := by
  rw [rawCoordinate_sparse 7 5 14 rawEntry_7_05_14 rawEntry_7_05_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_14)=_
  rw [rawEntry_7_05_14_coordinates]
  exact rawStandard_subst 5 14
theorem rawEntry_7_14_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 5=sparseCoefficient rawEntry_7_05_14 r := by decide +kernel
theorem rawEntry_7_14_05_physical : invariantSubst (rawCoordinate 7 14 5)=rawStandardPolynomial 14 5 := by
  have hh : rawCoordinate 7 14 5=rawCoordinate 7 5 14 := by
    rw [rawCoordinate_sparse 7 14 5 rawEntry_7_05_14 rawEntry_7_14_05_data,rawCoordinate_sparse 7 5 14 rawEntry_7_05_14 rawEntry_7_05_14_data]
  rw [hh,rawEntry_7_05_14_physical]
  exact rawStandardPolynomial_symm 5 14
def rawEntry_7_05_15 : SparseEntry := [(43,162),(45,-54),(48,12)]
theorem rawEntry_7_05_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 15=sparseCoefficient rawEntry_7_05_15 r := by decide +kernel
theorem rawEntry_7_05_15_coordinates : sparsePolynomial 81 rawEntry_7_05_15=rawStandardCoordinates 5 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_15_physical : invariantSubst (rawCoordinate 7 5 15)=rawStandardPolynomial 5 15 := by
  rw [rawCoordinate_sparse 7 5 15 rawEntry_7_05_15 rawEntry_7_05_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_15)=_
  rw [rawEntry_7_05_15_coordinates]
  exact rawStandard_subst 5 15
theorem rawEntry_7_15_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 5=sparseCoefficient rawEntry_7_05_15 r := by decide +kernel
theorem rawEntry_7_15_05_physical : invariantSubst (rawCoordinate 7 15 5)=rawStandardPolynomial 15 5 := by
  have hh : rawCoordinate 7 15 5=rawCoordinate 7 5 15 := by
    rw [rawCoordinate_sparse 7 15 5 rawEntry_7_05_15 rawEntry_7_15_05_data,rawCoordinate_sparse 7 5 15 rawEntry_7_05_15 rawEntry_7_05_15_data]
  rw [hh,rawEntry_7_05_15_physical]
  exact rawStandardPolynomial_symm 5 15
def rawEntry_7_05_16 : SparseEntry := [(45,162),(47,-54),(49,12)]
theorem rawEntry_7_05_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 16=sparseCoefficient rawEntry_7_05_16 r := by decide +kernel
theorem rawEntry_7_05_16_coordinates : sparsePolynomial 81 rawEntry_7_05_16=rawStandardCoordinates 5 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_16_physical : invariantSubst (rawCoordinate 7 5 16)=rawStandardPolynomial 5 16 := by
  rw [rawCoordinate_sparse 7 5 16 rawEntry_7_05_16 rawEntry_7_05_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_16)=_
  rw [rawEntry_7_05_16_coordinates]
  exact rawStandard_subst 5 16
theorem rawEntry_7_16_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 5=sparseCoefficient rawEntry_7_05_16 r := by decide +kernel
theorem rawEntry_7_16_05_physical : invariantSubst (rawCoordinate 7 16 5)=rawStandardPolynomial 16 5 := by
  have hh : rawCoordinate 7 16 5=rawCoordinate 7 5 16 := by
    rw [rawCoordinate_sparse 7 16 5 rawEntry_7_05_16 rawEntry_7_16_05_data,rawCoordinate_sparse 7 5 16 rawEntry_7_05_16 rawEntry_7_05_16_data]
  rw [hh,rawEntry_7_05_16_physical]
  exact rawStandardPolynomial_symm 5 16
def rawEntry_7_05_17 : SparseEntry := [(48,162),(49,-54),(51,12)]
theorem rawEntry_7_05_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 5 17=sparseCoefficient rawEntry_7_05_17 r := by decide +kernel
theorem rawEntry_7_05_17_coordinates : sparsePolynomial 81 rawEntry_7_05_17=rawStandardCoordinates 5 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_05_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_05_17_physical : invariantSubst (rawCoordinate 7 5 17)=rawStandardPolynomial 5 17 := by
  rw [rawCoordinate_sparse 7 5 17 rawEntry_7_05_17 rawEntry_7_05_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_05_17)=_
  rw [rawEntry_7_05_17_coordinates]
  exact rawStandard_subst 5 17
theorem rawEntry_7_17_05_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 5=sparseCoefficient rawEntry_7_05_17 r := by decide +kernel
theorem rawEntry_7_17_05_physical : invariantSubst (rawCoordinate 7 17 5)=rawStandardPolynomial 17 5 := by
  have hh : rawCoordinate 7 17 5=rawCoordinate 7 5 17 := by
    rw [rawCoordinate_sparse 7 17 5 rawEntry_7_05_17 rawEntry_7_17_05_data,rawCoordinate_sparse 7 5 17 rawEntry_7_05_17 rawEntry_7_05_17_data]
  rw [hh,rawEntry_7_05_17_physical]
  exact rawStandardPolynomial_symm 5 17
def rawEntry_7_06_06 : SparseEntry := [(39,-108),(40,36)]
theorem rawEntry_7_06_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 6=sparseCoefficient rawEntry_7_06_06 r := by decide +kernel
theorem rawEntry_7_06_06_coordinates : sparsePolynomial 81 rawEntry_7_06_06=rawStandardCoordinates 6 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_06,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_06_physical : invariantSubst (rawCoordinate 7 6 6)=rawStandardPolynomial 6 6 := by
  rw [rawCoordinate_sparse 7 6 6 rawEntry_7_06_06 rawEntry_7_06_06_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_06)=_
  rw [rawEntry_7_06_06_coordinates]
  exact rawStandard_subst 6 6
def rawEntry_7_06_07 : SparseEntry := [(47,-108),(49,36)]
theorem rawEntry_7_06_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 7=sparseCoefficient rawEntry_7_06_07 r := by decide +kernel
theorem rawEntry_7_06_07_coordinates : sparsePolynomial 81 rawEntry_7_06_07=rawStandardCoordinates 6 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_07_physical : invariantSubst (rawCoordinate 7 6 7)=rawStandardPolynomial 6 7 := by
  rw [rawCoordinate_sparse 7 6 7 rawEntry_7_06_07 rawEntry_7_06_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_07)=_
  rw [rawEntry_7_06_07_coordinates]
  exact rawStandard_subst 6 7
theorem rawEntry_7_07_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 6=sparseCoefficient rawEntry_7_06_07 r := by decide +kernel
theorem rawEntry_7_07_06_physical : invariantSubst (rawCoordinate 7 7 6)=rawStandardPolynomial 7 6 := by
  have hh : rawCoordinate 7 7 6=rawCoordinate 7 6 7 := by
    rw [rawCoordinate_sparse 7 7 6 rawEntry_7_06_07 rawEntry_7_07_06_data,rawCoordinate_sparse 7 6 7 rawEntry_7_06_07 rawEntry_7_06_07_data]
  rw [hh,rawEntry_7_06_07_physical]
  exact rawStandardPolynomial_symm 6 7
def rawEntry_7_06_08 : SparseEntry := [(48,-108),(50,36)]
theorem rawEntry_7_06_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 8=sparseCoefficient rawEntry_7_06_08 r := by decide +kernel
theorem rawEntry_7_06_08_coordinates : sparsePolynomial 81 rawEntry_7_06_08=rawStandardCoordinates 6 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_08_physical : invariantSubst (rawCoordinate 7 6 8)=rawStandardPolynomial 6 8 := by
  rw [rawCoordinate_sparse 7 6 8 rawEntry_7_06_08 rawEntry_7_06_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_08)=_
  rw [rawEntry_7_06_08_coordinates]
  exact rawStandard_subst 6 8
theorem rawEntry_7_08_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 6=sparseCoefficient rawEntry_7_06_08 r := by decide +kernel
theorem rawEntry_7_08_06_physical : invariantSubst (rawCoordinate 7 8 6)=rawStandardPolynomial 8 6 := by
  have hh : rawCoordinate 7 8 6=rawCoordinate 7 6 8 := by
    rw [rawCoordinate_sparse 7 8 6 rawEntry_7_06_08 rawEntry_7_08_06_data,rawCoordinate_sparse 7 6 8 rawEntry_7_06_08 rawEntry_7_06_08_data]
  rw [hh,rawEntry_7_06_08_physical]
  exact rawStandardPolynomial_symm 6 8
def rawEntry_7_06_09 : SparseEntry := [(49,-108),(51,36)]
theorem rawEntry_7_06_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 9=sparseCoefficient rawEntry_7_06_09 r := by decide +kernel
theorem rawEntry_7_06_09_coordinates : sparsePolynomial 81 rawEntry_7_06_09=rawStandardCoordinates 6 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_09_physical : invariantSubst (rawCoordinate 7 6 9)=rawStandardPolynomial 6 9 := by
  rw [rawCoordinate_sparse 7 6 9 rawEntry_7_06_09 rawEntry_7_06_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_09)=_
  rw [rawEntry_7_06_09_coordinates]
  exact rawStandard_subst 6 9
theorem rawEntry_7_09_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 6=sparseCoefficient rawEntry_7_06_09 r := by decide +kernel
theorem rawEntry_7_09_06_physical : invariantSubst (rawCoordinate 7 9 6)=rawStandardPolynomial 9 6 := by
  have hh : rawCoordinate 7 9 6=rawCoordinate 7 6 9 := by
    rw [rawCoordinate_sparse 7 9 6 rawEntry_7_06_09 rawEntry_7_09_06_data,rawCoordinate_sparse 7 6 9 rawEntry_7_06_09 rawEntry_7_06_09_data]
  rw [hh,rawEntry_7_06_09_physical]
  exact rawStandardPolynomial_symm 6 9
def rawEntry_7_06_10 : SparseEntry := [(51,-108),(52,36)]
theorem rawEntry_7_06_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 10=sparseCoefficient rawEntry_7_06_10 r := by decide +kernel
theorem rawEntry_7_06_10_coordinates : sparsePolynomial 81 rawEntry_7_06_10=rawStandardCoordinates 6 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_10_physical : invariantSubst (rawCoordinate 7 6 10)=rawStandardPolynomial 6 10 := by
  rw [rawCoordinate_sparse 7 6 10 rawEntry_7_06_10 rawEntry_7_06_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_10)=_
  rw [rawEntry_7_06_10_coordinates]
  exact rawStandard_subst 6 10
theorem rawEntry_7_10_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 6=sparseCoefficient rawEntry_7_06_10 r := by decide +kernel
theorem rawEntry_7_10_06_physical : invariantSubst (rawCoordinate 7 10 6)=rawStandardPolynomial 10 6 := by
  have hh : rawCoordinate 7 10 6=rawCoordinate 7 6 10 := by
    rw [rawCoordinate_sparse 7 10 6 rawEntry_7_06_10 rawEntry_7_10_06_data,rawCoordinate_sparse 7 6 10 rawEntry_7_06_10 rawEntry_7_06_10_data]
  rw [hh,rawEntry_7_06_10_physical]
  exact rawStandardPolynomial_symm 6 10
def rawEntry_7_06_11 : SparseEntry := [(20,162),(21,-54),(22,12)]
theorem rawEntry_7_06_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 11=sparseCoefficient rawEntry_7_06_11 r := by decide +kernel
theorem rawEntry_7_06_11_coordinates : sparsePolynomial 81 rawEntry_7_06_11=rawStandardCoordinates 6 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_11_physical : invariantSubst (rawCoordinate 7 6 11)=rawStandardPolynomial 6 11 := by
  rw [rawCoordinate_sparse 7 6 11 rawEntry_7_06_11 rawEntry_7_06_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_11)=_
  rw [rawEntry_7_06_11_coordinates]
  exact rawStandard_subst 6 11
theorem rawEntry_7_11_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 6=sparseCoefficient rawEntry_7_06_11 r := by decide +kernel
theorem rawEntry_7_11_06_physical : invariantSubst (rawCoordinate 7 11 6)=rawStandardPolynomial 11 6 := by
  have hh : rawCoordinate 7 11 6=rawCoordinate 7 6 11 := by
    rw [rawCoordinate_sparse 7 11 6 rawEntry_7_06_11 rawEntry_7_11_06_data,rawCoordinate_sparse 7 6 11 rawEntry_7_06_11 rawEntry_7_06_11_data]
  rw [hh,rawEntry_7_06_11_physical]
  exact rawStandardPolynomial_symm 6 11
def rawEntry_7_06_12 : SparseEntry := [(28,162),(29,-54),(30,12)]
theorem rawEntry_7_06_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 12=sparseCoefficient rawEntry_7_06_12 r := by decide +kernel
theorem rawEntry_7_06_12_coordinates : sparsePolynomial 81 rawEntry_7_06_12=rawStandardCoordinates 6 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_12_physical : invariantSubst (rawCoordinate 7 6 12)=rawStandardPolynomial 6 12 := by
  rw [rawCoordinate_sparse 7 6 12 rawEntry_7_06_12 rawEntry_7_06_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_12)=_
  rw [rawEntry_7_06_12_coordinates]
  exact rawStandard_subst 6 12
theorem rawEntry_7_12_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 6=sparseCoefficient rawEntry_7_06_12 r := by decide +kernel
theorem rawEntry_7_12_06_physical : invariantSubst (rawCoordinate 7 12 6)=rawStandardPolynomial 12 6 := by
  have hh : rawCoordinate 7 12 6=rawCoordinate 7 6 12 := by
    rw [rawCoordinate_sparse 7 12 6 rawEntry_7_06_12 rawEntry_7_12_06_data,rawCoordinate_sparse 7 6 12 rawEntry_7_06_12 rawEntry_7_06_12_data]
  rw [hh,rawEntry_7_06_12_physical]
  exact rawStandardPolynomial_symm 6 12
end ThomsonNegative.Certificate.Bridges
