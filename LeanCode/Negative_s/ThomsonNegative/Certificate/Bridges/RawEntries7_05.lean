import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_06_13 : SparseEntry := [(36,162),(37,-54),(39,12)]
theorem rawEntry_7_06_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 13=sparseCoefficient rawEntry_7_06_13 r := by decide +kernel
theorem rawEntry_7_06_13_coordinates : sparsePolynomial 81 rawEntry_7_06_13=rawStandardCoordinates 6 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_13_physical : invariantSubst (rawCoordinate 7 6 13)=rawStandardPolynomial 6 13 := by
  rw [rawCoordinate_sparse 7 6 13 rawEntry_7_06_13 rawEntry_7_06_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_13)=_
  rw [rawEntry_7_06_13_coordinates]
  exact rawStandard_subst 6 13
theorem rawEntry_7_13_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 6=sparseCoefficient rawEntry_7_06_13 r := by decide +kernel
theorem rawEntry_7_13_06_physical : invariantSubst (rawCoordinate 7 13 6)=rawStandardPolynomial 13 6 := by
  have hh : rawCoordinate 7 13 6=rawCoordinate 7 6 13 := by
    rw [rawCoordinate_sparse 7 13 6 rawEntry_7_06_13 rawEntry_7_13_06_data,rawCoordinate_sparse 7 6 13 rawEntry_7_06_13 rawEntry_7_06_13_data]
  rw [hh,rawEntry_7_06_13_physical]
  exact rawStandardPolynomial_symm 6 13
def rawEntry_7_06_14 : SparseEntry := [(38,162),(39,-54),(40,12)]
theorem rawEntry_7_06_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 14=sparseCoefficient rawEntry_7_06_14 r := by decide +kernel
theorem rawEntry_7_06_14_coordinates : sparsePolynomial 81 rawEntry_7_06_14=rawStandardCoordinates 6 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_14_physical : invariantSubst (rawCoordinate 7 6 14)=rawStandardPolynomial 6 14 := by
  rw [rawCoordinate_sparse 7 6 14 rawEntry_7_06_14 rawEntry_7_06_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_14)=_
  rw [rawEntry_7_06_14_coordinates]
  exact rawStandard_subst 6 14
theorem rawEntry_7_14_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 6=sparseCoefficient rawEntry_7_06_14 r := by decide +kernel
theorem rawEntry_7_14_06_physical : invariantSubst (rawCoordinate 7 14 6)=rawStandardPolynomial 14 6 := by
  have hh : rawCoordinate 7 14 6=rawCoordinate 7 6 14 := by
    rw [rawCoordinate_sparse 7 14 6 rawEntry_7_06_14 rawEntry_7_14_06_data,rawCoordinate_sparse 7 6 14 rawEntry_7_06_14 rawEntry_7_06_14_data]
  rw [hh,rawEntry_7_06_14_physical]
  exact rawStandardPolynomial_symm 6 14
def rawEntry_7_06_15 : SparseEntry := [(46,162),(48,-54),(50,12)]
theorem rawEntry_7_06_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 15=sparseCoefficient rawEntry_7_06_15 r := by decide +kernel
theorem rawEntry_7_06_15_coordinates : sparsePolynomial 81 rawEntry_7_06_15=rawStandardCoordinates 6 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_15_physical : invariantSubst (rawCoordinate 7 6 15)=rawStandardPolynomial 6 15 := by
  rw [rawCoordinate_sparse 7 6 15 rawEntry_7_06_15 rawEntry_7_06_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_15)=_
  rw [rawEntry_7_06_15_coordinates]
  exact rawStandard_subst 6 15
theorem rawEntry_7_15_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 6=sparseCoefficient rawEntry_7_06_15 r := by decide +kernel
theorem rawEntry_7_15_06_physical : invariantSubst (rawCoordinate 7 15 6)=rawStandardPolynomial 15 6 := by
  have hh : rawCoordinate 7 15 6=rawCoordinate 7 6 15 := by
    rw [rawCoordinate_sparse 7 15 6 rawEntry_7_06_15 rawEntry_7_15_06_data,rawCoordinate_sparse 7 6 15 rawEntry_7_06_15 rawEntry_7_06_15_data]
  rw [hh,rawEntry_7_06_15_physical]
  exact rawStandardPolynomial_symm 6 15
def rawEntry_7_06_16 : SparseEntry := [(48,162),(49,-54),(51,12)]
theorem rawEntry_7_06_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 16=sparseCoefficient rawEntry_7_06_16 r := by decide +kernel
theorem rawEntry_7_06_16_coordinates : sparsePolynomial 81 rawEntry_7_06_16=rawStandardCoordinates 6 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_16_physical : invariantSubst (rawCoordinate 7 6 16)=rawStandardPolynomial 6 16 := by
  rw [rawCoordinate_sparse 7 6 16 rawEntry_7_06_16 rawEntry_7_06_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_16)=_
  rw [rawEntry_7_06_16_coordinates]
  exact rawStandard_subst 6 16
theorem rawEntry_7_16_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 6=sparseCoefficient rawEntry_7_06_16 r := by decide +kernel
theorem rawEntry_7_16_06_physical : invariantSubst (rawCoordinate 7 16 6)=rawStandardPolynomial 16 6 := by
  have hh : rawCoordinate 7 16 6=rawCoordinate 7 6 16 := by
    rw [rawCoordinate_sparse 7 16 6 rawEntry_7_06_16 rawEntry_7_16_06_data,rawCoordinate_sparse 7 6 16 rawEntry_7_06_16 rawEntry_7_06_16_data]
  rw [hh,rawEntry_7_06_16_physical]
  exact rawStandardPolynomial_symm 6 16
def rawEntry_7_06_17 : SparseEntry := [(50,162),(51,-54),(52,12)]
theorem rawEntry_7_06_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 6 17=sparseCoefficient rawEntry_7_06_17 r := by decide +kernel
theorem rawEntry_7_06_17_coordinates : sparsePolynomial 81 rawEntry_7_06_17=rawStandardCoordinates 6 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_06_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_06_17_physical : invariantSubst (rawCoordinate 7 6 17)=rawStandardPolynomial 6 17 := by
  rw [rawCoordinate_sparse 7 6 17 rawEntry_7_06_17 rawEntry_7_06_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_06_17)=_
  rw [rawEntry_7_06_17_coordinates]
  exact rawStandard_subst 6 17
theorem rawEntry_7_17_06_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 6=sparseCoefficient rawEntry_7_06_17 r := by decide +kernel
theorem rawEntry_7_17_06_physical : invariantSubst (rawCoordinate 7 17 6)=rawStandardPolynomial 17 6 := by
  have hh : rawCoordinate 7 17 6=rawCoordinate 7 6 17 := by
    rw [rawCoordinate_sparse 7 17 6 rawEntry_7_06_17 rawEntry_7_17_06_data,rawCoordinate_sparse 7 6 17 rawEntry_7_06_17 rawEntry_7_06_17_data]
  rw [hh,rawEntry_7_06_17_physical]
  exact rawStandardPolynomial_symm 6 17
def rawEntry_7_07_07 : SparseEntry := [(54,-108),(58,36)]
theorem rawEntry_7_07_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 7=sparseCoefficient rawEntry_7_07_07 r := by decide +kernel
theorem rawEntry_7_07_07_coordinates : sparsePolynomial 81 rawEntry_7_07_07=rawStandardCoordinates 7 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_07,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_07_physical : invariantSubst (rawCoordinate 7 7 7)=rawStandardPolynomial 7 7 := by
  rw [rawCoordinate_sparse 7 7 7 rawEntry_7_07_07 rawEntry_7_07_07_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_07)=_
  rw [rawEntry_7_07_07_coordinates]
  exact rawStandard_subst 7 7
def rawEntry_7_07_08 : SparseEntry := [(56,-108),(59,36)]
theorem rawEntry_7_07_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 8=sparseCoefficient rawEntry_7_07_08 r := by decide +kernel
theorem rawEntry_7_07_08_coordinates : sparsePolynomial 81 rawEntry_7_07_08=rawStandardCoordinates 7 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_08_physical : invariantSubst (rawCoordinate 7 7 8)=rawStandardPolynomial 7 8 := by
  rw [rawCoordinate_sparse 7 7 8 rawEntry_7_07_08 rawEntry_7_07_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_08)=_
  rw [rawEntry_7_07_08_coordinates]
  exact rawStandard_subst 7 8
theorem rawEntry_7_08_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 7=sparseCoefficient rawEntry_7_07_08 r := by decide +kernel
theorem rawEntry_7_08_07_physical : invariantSubst (rawCoordinate 7 8 7)=rawStandardPolynomial 8 7 := by
  have hh : rawCoordinate 7 8 7=rawCoordinate 7 7 8 := by
    rw [rawCoordinate_sparse 7 8 7 rawEntry_7_07_08 rawEntry_7_08_07_data,rawCoordinate_sparse 7 7 8 rawEntry_7_07_08 rawEntry_7_07_08_data]
  rw [hh,rawEntry_7_07_08_physical]
  exact rawStandardPolynomial_symm 7 8
def rawEntry_7_07_09 : SparseEntry := [(58,-108),(61,36)]
theorem rawEntry_7_07_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 9=sparseCoefficient rawEntry_7_07_09 r := by decide +kernel
theorem rawEntry_7_07_09_coordinates : sparsePolynomial 81 rawEntry_7_07_09=rawStandardCoordinates 7 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_09_physical : invariantSubst (rawCoordinate 7 7 9)=rawStandardPolynomial 7 9 := by
  rw [rawCoordinate_sparse 7 7 9 rawEntry_7_07_09 rawEntry_7_07_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_09)=_
  rw [rawEntry_7_07_09_coordinates]
  exact rawStandard_subst 7 9
theorem rawEntry_7_09_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 7=sparseCoefficient rawEntry_7_07_09 r := by decide +kernel
theorem rawEntry_7_09_07_physical : invariantSubst (rawCoordinate 7 9 7)=rawStandardPolynomial 9 7 := by
  have hh : rawCoordinate 7 9 7=rawCoordinate 7 7 9 := by
    rw [rawCoordinate_sparse 7 9 7 rawEntry_7_07_09 rawEntry_7_09_07_data,rawCoordinate_sparse 7 7 9 rawEntry_7_07_09 rawEntry_7_07_09_data]
  rw [hh,rawEntry_7_07_09_physical]
  exact rawStandardPolynomial_symm 7 9
def rawEntry_7_07_10 : SparseEntry := [(61,-108),(63,36)]
theorem rawEntry_7_07_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 10=sparseCoefficient rawEntry_7_07_10 r := by decide +kernel
theorem rawEntry_7_07_10_coordinates : sparsePolynomial 81 rawEntry_7_07_10=rawStandardCoordinates 7 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_10_physical : invariantSubst (rawCoordinate 7 7 10)=rawStandardPolynomial 7 10 := by
  rw [rawCoordinate_sparse 7 7 10 rawEntry_7_07_10 rawEntry_7_07_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_10)=_
  rw [rawEntry_7_07_10_coordinates]
  exact rawStandard_subst 7 10
theorem rawEntry_7_10_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 7=sparseCoefficient rawEntry_7_07_10 r := by decide +kernel
theorem rawEntry_7_10_07_physical : invariantSubst (rawCoordinate 7 10 7)=rawStandardPolynomial 10 7 := by
  have hh : rawCoordinate 7 10 7=rawCoordinate 7 7 10 := by
    rw [rawCoordinate_sparse 7 10 7 rawEntry_7_07_10 rawEntry_7_10_07_data,rawCoordinate_sparse 7 7 10 rawEntry_7_07_10 rawEntry_7_07_10_data]
  rw [hh,rawEntry_7_07_10_physical]
  exact rawStandardPolynomial_symm 7 10
def rawEntry_7_07_11 : SparseEntry := [(23,162),(25,-54),(27,12)]
theorem rawEntry_7_07_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 11=sparseCoefficient rawEntry_7_07_11 r := by decide +kernel
theorem rawEntry_7_07_11_coordinates : sparsePolynomial 81 rawEntry_7_07_11=rawStandardCoordinates 7 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_11_physical : invariantSubst (rawCoordinate 7 7 11)=rawStandardPolynomial 7 11 := by
  rw [rawCoordinate_sparse 7 7 11 rawEntry_7_07_11 rawEntry_7_07_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_11)=_
  rw [rawEntry_7_07_11_coordinates]
  exact rawStandard_subst 7 11
theorem rawEntry_7_11_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 7=sparseCoefficient rawEntry_7_07_11 r := by decide +kernel
theorem rawEntry_7_11_07_physical : invariantSubst (rawCoordinate 7 11 7)=rawStandardPolynomial 11 7 := by
  have hh : rawCoordinate 7 11 7=rawCoordinate 7 7 11 := by
    rw [rawCoordinate_sparse 7 11 7 rawEntry_7_07_11 rawEntry_7_11_07_data,rawCoordinate_sparse 7 7 11 rawEntry_7_07_11 rawEntry_7_07_11_data]
  rw [hh,rawEntry_7_07_11_physical]
  exact rawStandardPolynomial_symm 7 11
def rawEntry_7_07_12 : SparseEntry := [(33,162),(35,-54),(37,12)]
theorem rawEntry_7_07_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 12=sparseCoefficient rawEntry_7_07_12 r := by decide +kernel
theorem rawEntry_7_07_12_coordinates : sparsePolynomial 81 rawEntry_7_07_12=rawStandardCoordinates 7 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_12_physical : invariantSubst (rawCoordinate 7 7 12)=rawStandardPolynomial 7 12 := by
  rw [rawCoordinate_sparse 7 7 12 rawEntry_7_07_12 rawEntry_7_07_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_12)=_
  rw [rawEntry_7_07_12_coordinates]
  exact rawStandard_subst 7 12
theorem rawEntry_7_12_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 7=sparseCoefficient rawEntry_7_07_12 r := by decide +kernel
theorem rawEntry_7_12_07_physical : invariantSubst (rawCoordinate 7 12 7)=rawStandardPolynomial 12 7 := by
  have hh : rawCoordinate 7 12 7=rawCoordinate 7 7 12 := by
    rw [rawCoordinate_sparse 7 12 7 rawEntry_7_07_12 rawEntry_7_12_07_data,rawCoordinate_sparse 7 7 12 rawEntry_7_07_12 rawEntry_7_07_12_data]
  rw [hh,rawEntry_7_07_12_physical]
  exact rawStandardPolynomial_symm 7 12
def rawEntry_7_07_13 : SparseEntry := [(42,162),(44,-54),(47,12)]
theorem rawEntry_7_07_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 13=sparseCoefficient rawEntry_7_07_13 r := by decide +kernel
theorem rawEntry_7_07_13_coordinates : sparsePolynomial 81 rawEntry_7_07_13=rawStandardCoordinates 7 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_13_physical : invariantSubst (rawCoordinate 7 7 13)=rawStandardPolynomial 7 13 := by
  rw [rawCoordinate_sparse 7 7 13 rawEntry_7_07_13 rawEntry_7_07_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_13)=_
  rw [rawEntry_7_07_13_coordinates]
  exact rawStandard_subst 7 13
theorem rawEntry_7_13_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 7=sparseCoefficient rawEntry_7_07_13 r := by decide +kernel
theorem rawEntry_7_13_07_physical : invariantSubst (rawCoordinate 7 13 7)=rawStandardPolynomial 13 7 := by
  have hh : rawCoordinate 7 13 7=rawCoordinate 7 7 13 := by
    rw [rawCoordinate_sparse 7 13 7 rawEntry_7_07_13 rawEntry_7_13_07_data,rawCoordinate_sparse 7 7 13 rawEntry_7_07_13 rawEntry_7_07_13_data]
  rw [hh,rawEntry_7_07_13_physical]
  exact rawStandardPolynomial_symm 7 13
def rawEntry_7_07_14 : SparseEntry := [(45,162),(47,-54),(49,12)]
theorem rawEntry_7_07_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 14=sparseCoefficient rawEntry_7_07_14 r := by decide +kernel
theorem rawEntry_7_07_14_coordinates : sparsePolynomial 81 rawEntry_7_07_14=rawStandardCoordinates 7 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_14_physical : invariantSubst (rawCoordinate 7 7 14)=rawStandardPolynomial 7 14 := by
  rw [rawCoordinate_sparse 7 7 14 rawEntry_7_07_14 rawEntry_7_07_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_14)=_
  rw [rawEntry_7_07_14_coordinates]
  exact rawStandard_subst 7 14
theorem rawEntry_7_14_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 7=sparseCoefficient rawEntry_7_07_14 r := by decide +kernel
theorem rawEntry_7_14_07_physical : invariantSubst (rawCoordinate 7 14 7)=rawStandardPolynomial 14 7 := by
  have hh : rawCoordinate 7 14 7=rawCoordinate 7 7 14 := by
    rw [rawCoordinate_sparse 7 14 7 rawEntry_7_07_14 rawEntry_7_14_07_data,rawCoordinate_sparse 7 7 14 rawEntry_7_07_14 rawEntry_7_07_14_data]
  rw [hh,rawEntry_7_07_14_physical]
  exact rawStandardPolynomial_symm 7 14
def rawEntry_7_07_15 : SparseEntry := [(53,162),(56,-54),(59,12)]
theorem rawEntry_7_07_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 15=sparseCoefficient rawEntry_7_07_15 r := by decide +kernel
theorem rawEntry_7_07_15_coordinates : sparsePolynomial 81 rawEntry_7_07_15=rawStandardCoordinates 7 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_15_physical : invariantSubst (rawCoordinate 7 7 15)=rawStandardPolynomial 7 15 := by
  rw [rawCoordinate_sparse 7 7 15 rawEntry_7_07_15 rawEntry_7_07_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_15)=_
  rw [rawEntry_7_07_15_coordinates]
  exact rawStandard_subst 7 15
theorem rawEntry_7_15_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 7=sparseCoefficient rawEntry_7_07_15 r := by decide +kernel
theorem rawEntry_7_15_07_physical : invariantSubst (rawCoordinate 7 15 7)=rawStandardPolynomial 15 7 := by
  have hh : rawCoordinate 7 15 7=rawCoordinate 7 7 15 := by
    rw [rawCoordinate_sparse 7 15 7 rawEntry_7_07_15 rawEntry_7_15_07_data,rawCoordinate_sparse 7 7 15 rawEntry_7_07_15 rawEntry_7_07_15_data]
  rw [hh,rawEntry_7_07_15_physical]
  exact rawStandardPolynomial_symm 7 15
def rawEntry_7_07_16 : SparseEntry := [(56,162),(58,-54),(61,12)]
theorem rawEntry_7_07_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 16=sparseCoefficient rawEntry_7_07_16 r := by decide +kernel
theorem rawEntry_7_07_16_coordinates : sparsePolynomial 81 rawEntry_7_07_16=rawStandardCoordinates 7 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_16_physical : invariantSubst (rawCoordinate 7 7 16)=rawStandardPolynomial 7 16 := by
  rw [rawCoordinate_sparse 7 7 16 rawEntry_7_07_16 rawEntry_7_07_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_16)=_
  rw [rawEntry_7_07_16_coordinates]
  exact rawStandard_subst 7 16
theorem rawEntry_7_16_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 7=sparseCoefficient rawEntry_7_07_16 r := by decide +kernel
theorem rawEntry_7_16_07_physical : invariantSubst (rawCoordinate 7 16 7)=rawStandardPolynomial 16 7 := by
  have hh : rawCoordinate 7 16 7=rawCoordinate 7 7 16 := by
    rw [rawCoordinate_sparse 7 16 7 rawEntry_7_07_16 rawEntry_7_16_07_data,rawCoordinate_sparse 7 7 16 rawEntry_7_07_16 rawEntry_7_07_16_data]
  rw [hh,rawEntry_7_07_16_physical]
  exact rawStandardPolynomial_symm 7 16
def rawEntry_7_07_17 : SparseEntry := [(59,162),(61,-54),(63,12)]
theorem rawEntry_7_07_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 7 17=sparseCoefficient rawEntry_7_07_17 r := by decide +kernel
theorem rawEntry_7_07_17_coordinates : sparsePolynomial 81 rawEntry_7_07_17=rawStandardCoordinates 7 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_07_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_07_17_physical : invariantSubst (rawCoordinate 7 7 17)=rawStandardPolynomial 7 17 := by
  rw [rawCoordinate_sparse 7 7 17 rawEntry_7_07_17 rawEntry_7_07_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_07_17)=_
  rw [rawEntry_7_07_17_coordinates]
  exact rawStandard_subst 7 17
theorem rawEntry_7_17_07_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 7=sparseCoefficient rawEntry_7_07_17 r := by decide +kernel
theorem rawEntry_7_17_07_physical : invariantSubst (rawCoordinate 7 17 7)=rawStandardPolynomial 17 7 := by
  have hh : rawCoordinate 7 17 7=rawCoordinate 7 7 17 := by
    rw [rawCoordinate_sparse 7 17 7 rawEntry_7_07_17 rawEntry_7_17_07_data,rawCoordinate_sparse 7 7 17 rawEntry_7_07_17 rawEntry_7_07_17_data]
  rw [hh,rawEntry_7_07_17_physical]
  exact rawStandardPolynomial_symm 7 17
def rawEntry_7_08_08 : SparseEntry := [(57,-108),(60,36)]
theorem rawEntry_7_08_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 8=sparseCoefficient rawEntry_7_08_08 r := by decide +kernel
theorem rawEntry_7_08_08_coordinates : sparsePolynomial 81 rawEntry_7_08_08=rawStandardCoordinates 8 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_08,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_08_physical : invariantSubst (rawCoordinate 7 8 8)=rawStandardPolynomial 8 8 := by
  rw [rawCoordinate_sparse 7 8 8 rawEntry_7_08_08 rawEntry_7_08_08_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_08)=_
  rw [rawEntry_7_08_08_coordinates]
  exact rawStandard_subst 8 8
def rawEntry_7_08_09 : SparseEntry := [(59,-108),(62,36)]
theorem rawEntry_7_08_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 9=sparseCoefficient rawEntry_7_08_09 r := by decide +kernel
theorem rawEntry_7_08_09_coordinates : sparsePolynomial 81 rawEntry_7_08_09=rawStandardCoordinates 8 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_09_physical : invariantSubst (rawCoordinate 7 8 9)=rawStandardPolynomial 8 9 := by
  rw [rawCoordinate_sparse 7 8 9 rawEntry_7_08_09 rawEntry_7_08_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_09)=_
  rw [rawEntry_7_08_09_coordinates]
  exact rawStandard_subst 8 9
theorem rawEntry_7_09_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 8=sparseCoefficient rawEntry_7_08_09 r := by decide +kernel
theorem rawEntry_7_09_08_physical : invariantSubst (rawCoordinate 7 9 8)=rawStandardPolynomial 9 8 := by
  have hh : rawCoordinate 7 9 8=rawCoordinate 7 8 9 := by
    rw [rawCoordinate_sparse 7 9 8 rawEntry_7_08_09 rawEntry_7_09_08_data,rawCoordinate_sparse 7 8 9 rawEntry_7_08_09 rawEntry_7_08_09_data]
  rw [hh,rawEntry_7_08_09_physical]
  exact rawStandardPolynomial_symm 8 9
def rawEntry_7_08_10 : SparseEntry := [(62,-108),(64,36)]
theorem rawEntry_7_08_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 10=sparseCoefficient rawEntry_7_08_10 r := by decide +kernel
theorem rawEntry_7_08_10_coordinates : sparsePolynomial 81 rawEntry_7_08_10=rawStandardCoordinates 8 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_10_physical : invariantSubst (rawCoordinate 7 8 10)=rawStandardPolynomial 8 10 := by
  rw [rawCoordinate_sparse 7 8 10 rawEntry_7_08_10 rawEntry_7_08_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_10)=_
  rw [rawEntry_7_08_10_coordinates]
  exact rawStandard_subst 8 10
theorem rawEntry_7_10_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 8=sparseCoefficient rawEntry_7_08_10 r := by decide +kernel
theorem rawEntry_7_10_08_physical : invariantSubst (rawCoordinate 7 10 8)=rawStandardPolynomial 10 8 := by
  have hh : rawCoordinate 7 10 8=rawCoordinate 7 8 10 := by
    rw [rawCoordinate_sparse 7 10 8 rawEntry_7_08_10 rawEntry_7_10_08_data,rawCoordinate_sparse 7 8 10 rawEntry_7_08_10 rawEntry_7_08_10_data]
  rw [hh,rawEntry_7_08_10_physical]
  exact rawStandardPolynomial_symm 8 10
def rawEntry_7_08_11 : SparseEntry := [(24,162),(26,-54),(28,12)]
theorem rawEntry_7_08_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 11=sparseCoefficient rawEntry_7_08_11 r := by decide +kernel
theorem rawEntry_7_08_11_coordinates : sparsePolynomial 81 rawEntry_7_08_11=rawStandardCoordinates 8 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_11_physical : invariantSubst (rawCoordinate 7 8 11)=rawStandardPolynomial 8 11 := by
  rw [rawCoordinate_sparse 7 8 11 rawEntry_7_08_11 rawEntry_7_08_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_11)=_
  rw [rawEntry_7_08_11_coordinates]
  exact rawStandard_subst 8 11
theorem rawEntry_7_11_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 8=sparseCoefficient rawEntry_7_08_11 r := by decide +kernel
theorem rawEntry_7_11_08_physical : invariantSubst (rawCoordinate 7 11 8)=rawStandardPolynomial 11 8 := by
  have hh : rawCoordinate 7 11 8=rawCoordinate 7 8 11 := by
    rw [rawCoordinate_sparse 7 11 8 rawEntry_7_08_11 rawEntry_7_11_08_data,rawCoordinate_sparse 7 8 11 rawEntry_7_08_11 rawEntry_7_08_11_data]
  rw [hh,rawEntry_7_08_11_physical]
  exact rawStandardPolynomial_symm 8 11
end ThomsonNegative.Certificate.Bridges
