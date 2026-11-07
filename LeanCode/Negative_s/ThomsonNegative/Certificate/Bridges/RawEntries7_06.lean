import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_08_12 : SparseEntry := [(34,162),(36,-54),(38,12)]
theorem rawEntry_7_08_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 12=sparseCoefficient rawEntry_7_08_12 r := by decide +kernel
theorem rawEntry_7_08_12_coordinates : sparsePolynomial 81 rawEntry_7_08_12=rawStandardCoordinates 8 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_12_physical : invariantSubst (rawCoordinate 7 8 12)=rawStandardPolynomial 8 12 := by
  rw [rawCoordinate_sparse 7 8 12 rawEntry_7_08_12 rawEntry_7_08_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_12)=_
  rw [rawEntry_7_08_12_coordinates]
  exact rawStandard_subst 8 12
theorem rawEntry_7_12_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 8=sparseCoefficient rawEntry_7_08_12 r := by decide +kernel
theorem rawEntry_7_12_08_physical : invariantSubst (rawCoordinate 7 12 8)=rawStandardPolynomial 12 8 := by
  have hh : rawCoordinate 7 12 8=rawCoordinate 7 8 12 := by
    rw [rawCoordinate_sparse 7 12 8 rawEntry_7_08_12 rawEntry_7_12_08_data,rawCoordinate_sparse 7 8 12 rawEntry_7_08_12 rawEntry_7_08_12_data]
  rw [hh,rawEntry_7_08_12_physical]
  exact rawStandardPolynomial_symm 8 12
def rawEntry_7_08_13 : SparseEntry := [(43,162),(45,-54),(48,12)]
theorem rawEntry_7_08_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 13=sparseCoefficient rawEntry_7_08_13 r := by decide +kernel
theorem rawEntry_7_08_13_coordinates : sparsePolynomial 81 rawEntry_7_08_13=rawStandardCoordinates 8 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_13_physical : invariantSubst (rawCoordinate 7 8 13)=rawStandardPolynomial 8 13 := by
  rw [rawCoordinate_sparse 7 8 13 rawEntry_7_08_13 rawEntry_7_08_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_13)=_
  rw [rawEntry_7_08_13_coordinates]
  exact rawStandard_subst 8 13
theorem rawEntry_7_13_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 8=sparseCoefficient rawEntry_7_08_13 r := by decide +kernel
theorem rawEntry_7_13_08_physical : invariantSubst (rawCoordinate 7 13 8)=rawStandardPolynomial 13 8 := by
  have hh : rawCoordinate 7 13 8=rawCoordinate 7 8 13 := by
    rw [rawCoordinate_sparse 7 13 8 rawEntry_7_08_13 rawEntry_7_13_08_data,rawCoordinate_sparse 7 8 13 rawEntry_7_08_13 rawEntry_7_08_13_data]
  rw [hh,rawEntry_7_08_13_physical]
  exact rawStandardPolynomial_symm 8 13
def rawEntry_7_08_14 : SparseEntry := [(46,162),(48,-54),(50,12)]
theorem rawEntry_7_08_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 14=sparseCoefficient rawEntry_7_08_14 r := by decide +kernel
theorem rawEntry_7_08_14_coordinates : sparsePolynomial 81 rawEntry_7_08_14=rawStandardCoordinates 8 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_14_physical : invariantSubst (rawCoordinate 7 8 14)=rawStandardPolynomial 8 14 := by
  rw [rawCoordinate_sparse 7 8 14 rawEntry_7_08_14 rawEntry_7_08_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_14)=_
  rw [rawEntry_7_08_14_coordinates]
  exact rawStandard_subst 8 14
theorem rawEntry_7_14_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 8=sparseCoefficient rawEntry_7_08_14 r := by decide +kernel
theorem rawEntry_7_14_08_physical : invariantSubst (rawCoordinate 7 14 8)=rawStandardPolynomial 14 8 := by
  have hh : rawCoordinate 7 14 8=rawCoordinate 7 8 14 := by
    rw [rawCoordinate_sparse 7 14 8 rawEntry_7_08_14 rawEntry_7_14_08_data,rawCoordinate_sparse 7 8 14 rawEntry_7_08_14 rawEntry_7_08_14_data]
  rw [hh,rawEntry_7_08_14_physical]
  exact rawStandardPolynomial_symm 8 14
def rawEntry_7_08_15 : SparseEntry := [(55,162),(57,-54),(60,12)]
theorem rawEntry_7_08_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 15=sparseCoefficient rawEntry_7_08_15 r := by decide +kernel
theorem rawEntry_7_08_15_coordinates : sparsePolynomial 81 rawEntry_7_08_15=rawStandardCoordinates 8 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_15_physical : invariantSubst (rawCoordinate 7 8 15)=rawStandardPolynomial 8 15 := by
  rw [rawCoordinate_sparse 7 8 15 rawEntry_7_08_15 rawEntry_7_08_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_15)=_
  rw [rawEntry_7_08_15_coordinates]
  exact rawStandard_subst 8 15
theorem rawEntry_7_15_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 8=sparseCoefficient rawEntry_7_08_15 r := by decide +kernel
theorem rawEntry_7_15_08_physical : invariantSubst (rawCoordinate 7 15 8)=rawStandardPolynomial 15 8 := by
  have hh : rawCoordinate 7 15 8=rawCoordinate 7 8 15 := by
    rw [rawCoordinate_sparse 7 15 8 rawEntry_7_08_15 rawEntry_7_15_08_data,rawCoordinate_sparse 7 8 15 rawEntry_7_08_15 rawEntry_7_08_15_data]
  rw [hh,rawEntry_7_08_15_physical]
  exact rawStandardPolynomial_symm 8 15
def rawEntry_7_08_16 : SparseEntry := [(57,162),(59,-54),(62,12)]
theorem rawEntry_7_08_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 16=sparseCoefficient rawEntry_7_08_16 r := by decide +kernel
theorem rawEntry_7_08_16_coordinates : sparsePolynomial 81 rawEntry_7_08_16=rawStandardCoordinates 8 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_16_physical : invariantSubst (rawCoordinate 7 8 16)=rawStandardPolynomial 8 16 := by
  rw [rawCoordinate_sparse 7 8 16 rawEntry_7_08_16 rawEntry_7_08_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_16)=_
  rw [rawEntry_7_08_16_coordinates]
  exact rawStandard_subst 8 16
theorem rawEntry_7_16_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 8=sparseCoefficient rawEntry_7_08_16 r := by decide +kernel
theorem rawEntry_7_16_08_physical : invariantSubst (rawCoordinate 7 16 8)=rawStandardPolynomial 16 8 := by
  have hh : rawCoordinate 7 16 8=rawCoordinate 7 8 16 := by
    rw [rawCoordinate_sparse 7 16 8 rawEntry_7_08_16 rawEntry_7_16_08_data,rawCoordinate_sparse 7 8 16 rawEntry_7_08_16 rawEntry_7_08_16_data]
  rw [hh,rawEntry_7_08_16_physical]
  exact rawStandardPolynomial_symm 8 16
def rawEntry_7_08_17 : SparseEntry := [(60,162),(62,-54),(64,12)]
theorem rawEntry_7_08_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 8 17=sparseCoefficient rawEntry_7_08_17 r := by decide +kernel
theorem rawEntry_7_08_17_coordinates : sparsePolynomial 81 rawEntry_7_08_17=rawStandardCoordinates 8 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_08_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_08_17_physical : invariantSubst (rawCoordinate 7 8 17)=rawStandardPolynomial 8 17 := by
  rw [rawCoordinate_sparse 7 8 17 rawEntry_7_08_17 rawEntry_7_08_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_08_17)=_
  rw [rawEntry_7_08_17_coordinates]
  exact rawStandard_subst 8 17
theorem rawEntry_7_17_08_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 8=sparseCoefficient rawEntry_7_08_17 r := by decide +kernel
theorem rawEntry_7_17_08_physical : invariantSubst (rawCoordinate 7 17 8)=rawStandardPolynomial 17 8 := by
  have hh : rawCoordinate 7 17 8=rawCoordinate 7 8 17 := by
    rw [rawCoordinate_sparse 7 17 8 rawEntry_7_08_17 rawEntry_7_17_08_data,rawCoordinate_sparse 7 8 17 rawEntry_7_08_17 rawEntry_7_08_17_data]
  rw [hh,rawEntry_7_08_17_physical]
  exact rawStandardPolynomial_symm 8 17
def rawEntry_7_09_09 : SparseEntry := [(61,-108),(63,36)]
theorem rawEntry_7_09_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 9=sparseCoefficient rawEntry_7_09_09 r := by decide +kernel
theorem rawEntry_7_09_09_coordinates : sparsePolynomial 81 rawEntry_7_09_09=rawStandardCoordinates 9 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_09,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_09_physical : invariantSubst (rawCoordinate 7 9 9)=rawStandardPolynomial 9 9 := by
  rw [rawCoordinate_sparse 7 9 9 rawEntry_7_09_09 rawEntry_7_09_09_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_09)=_
  rw [rawEntry_7_09_09_coordinates]
  exact rawStandard_subst 9 9
def rawEntry_7_09_10 : SparseEntry := [(63,-108),(65,36)]
theorem rawEntry_7_09_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 10=sparseCoefficient rawEntry_7_09_10 r := by decide +kernel
theorem rawEntry_7_09_10_coordinates : sparsePolynomial 81 rawEntry_7_09_10=rawStandardCoordinates 9 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_10_physical : invariantSubst (rawCoordinate 7 9 10)=rawStandardPolynomial 9 10 := by
  rw [rawCoordinate_sparse 7 9 10 rawEntry_7_09_10 rawEntry_7_09_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_10)=_
  rw [rawEntry_7_09_10_coordinates]
  exact rawStandard_subst 9 10
theorem rawEntry_7_10_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 9=sparseCoefficient rawEntry_7_09_10 r := by decide +kernel
theorem rawEntry_7_10_09_physical : invariantSubst (rawCoordinate 7 10 9)=rawStandardPolynomial 10 9 := by
  have hh : rawCoordinate 7 10 9=rawCoordinate 7 9 10 := by
    rw [rawCoordinate_sparse 7 10 9 rawEntry_7_09_10 rawEntry_7_10_09_data,rawCoordinate_sparse 7 9 10 rawEntry_7_09_10 rawEntry_7_09_10_data]
  rw [hh,rawEntry_7_09_10_physical]
  exact rawStandardPolynomial_symm 9 10
def rawEntry_7_09_11 : SparseEntry := [(26,162),(27,-54),(29,12)]
theorem rawEntry_7_09_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 11=sparseCoefficient rawEntry_7_09_11 r := by decide +kernel
theorem rawEntry_7_09_11_coordinates : sparsePolynomial 81 rawEntry_7_09_11=rawStandardCoordinates 9 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_11_physical : invariantSubst (rawCoordinate 7 9 11)=rawStandardPolynomial 9 11 := by
  rw [rawCoordinate_sparse 7 9 11 rawEntry_7_09_11 rawEntry_7_09_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_11)=_
  rw [rawEntry_7_09_11_coordinates]
  exact rawStandard_subst 9 11
theorem rawEntry_7_11_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 9=sparseCoefficient rawEntry_7_09_11 r := by decide +kernel
theorem rawEntry_7_11_09_physical : invariantSubst (rawCoordinate 7 11 9)=rawStandardPolynomial 11 9 := by
  have hh : rawCoordinate 7 11 9=rawCoordinate 7 9 11 := by
    rw [rawCoordinate_sparse 7 11 9 rawEntry_7_09_11 rawEntry_7_11_09_data,rawCoordinate_sparse 7 9 11 rawEntry_7_09_11 rawEntry_7_09_11_data]
  rw [hh,rawEntry_7_09_11_physical]
  exact rawStandardPolynomial_symm 9 11
def rawEntry_7_09_12 : SparseEntry := [(36,162),(37,-54),(39,12)]
theorem rawEntry_7_09_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 12=sparseCoefficient rawEntry_7_09_12 r := by decide +kernel
theorem rawEntry_7_09_12_coordinates : sparsePolynomial 81 rawEntry_7_09_12=rawStandardCoordinates 9 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_12_physical : invariantSubst (rawCoordinate 7 9 12)=rawStandardPolynomial 9 12 := by
  rw [rawCoordinate_sparse 7 9 12 rawEntry_7_09_12 rawEntry_7_09_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_12)=_
  rw [rawEntry_7_09_12_coordinates]
  exact rawStandard_subst 9 12
theorem rawEntry_7_12_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 9=sparseCoefficient rawEntry_7_09_12 r := by decide +kernel
theorem rawEntry_7_12_09_physical : invariantSubst (rawCoordinate 7 12 9)=rawStandardPolynomial 12 9 := by
  have hh : rawCoordinate 7 12 9=rawCoordinate 7 9 12 := by
    rw [rawCoordinate_sparse 7 12 9 rawEntry_7_09_12 rawEntry_7_12_09_data,rawCoordinate_sparse 7 9 12 rawEntry_7_09_12 rawEntry_7_09_12_data]
  rw [hh,rawEntry_7_09_12_physical]
  exact rawStandardPolynomial_symm 9 12
def rawEntry_7_09_13 : SparseEntry := [(45,162),(47,-54),(49,12)]
theorem rawEntry_7_09_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 13=sparseCoefficient rawEntry_7_09_13 r := by decide +kernel
theorem rawEntry_7_09_13_coordinates : sparsePolynomial 81 rawEntry_7_09_13=rawStandardCoordinates 9 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_13_physical : invariantSubst (rawCoordinate 7 9 13)=rawStandardPolynomial 9 13 := by
  rw [rawCoordinate_sparse 7 9 13 rawEntry_7_09_13 rawEntry_7_09_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_13)=_
  rw [rawEntry_7_09_13_coordinates]
  exact rawStandard_subst 9 13
theorem rawEntry_7_13_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 9=sparseCoefficient rawEntry_7_09_13 r := by decide +kernel
theorem rawEntry_7_13_09_physical : invariantSubst (rawCoordinate 7 13 9)=rawStandardPolynomial 13 9 := by
  have hh : rawCoordinate 7 13 9=rawCoordinate 7 9 13 := by
    rw [rawCoordinate_sparse 7 13 9 rawEntry_7_09_13 rawEntry_7_13_09_data,rawCoordinate_sparse 7 9 13 rawEntry_7_09_13 rawEntry_7_09_13_data]
  rw [hh,rawEntry_7_09_13_physical]
  exact rawStandardPolynomial_symm 9 13
def rawEntry_7_09_14 : SparseEntry := [(48,162),(49,-54),(51,12)]
theorem rawEntry_7_09_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 14=sparseCoefficient rawEntry_7_09_14 r := by decide +kernel
theorem rawEntry_7_09_14_coordinates : sparsePolynomial 81 rawEntry_7_09_14=rawStandardCoordinates 9 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_14_physical : invariantSubst (rawCoordinate 7 9 14)=rawStandardPolynomial 9 14 := by
  rw [rawCoordinate_sparse 7 9 14 rawEntry_7_09_14 rawEntry_7_09_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_14)=_
  rw [rawEntry_7_09_14_coordinates]
  exact rawStandard_subst 9 14
theorem rawEntry_7_14_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 9=sparseCoefficient rawEntry_7_09_14 r := by decide +kernel
theorem rawEntry_7_14_09_physical : invariantSubst (rawCoordinate 7 14 9)=rawStandardPolynomial 14 9 := by
  have hh : rawCoordinate 7 14 9=rawCoordinate 7 9 14 := by
    rw [rawCoordinate_sparse 7 14 9 rawEntry_7_09_14 rawEntry_7_14_09_data,rawCoordinate_sparse 7 9 14 rawEntry_7_09_14 rawEntry_7_09_14_data]
  rw [hh,rawEntry_7_09_14_physical]
  exact rawStandardPolynomial_symm 9 14
def rawEntry_7_09_15 : SparseEntry := [(57,162),(59,-54),(62,12)]
theorem rawEntry_7_09_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 15=sparseCoefficient rawEntry_7_09_15 r := by decide +kernel
theorem rawEntry_7_09_15_coordinates : sparsePolynomial 81 rawEntry_7_09_15=rawStandardCoordinates 9 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_15_physical : invariantSubst (rawCoordinate 7 9 15)=rawStandardPolynomial 9 15 := by
  rw [rawCoordinate_sparse 7 9 15 rawEntry_7_09_15 rawEntry_7_09_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_15)=_
  rw [rawEntry_7_09_15_coordinates]
  exact rawStandard_subst 9 15
theorem rawEntry_7_15_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 9=sparseCoefficient rawEntry_7_09_15 r := by decide +kernel
theorem rawEntry_7_15_09_physical : invariantSubst (rawCoordinate 7 15 9)=rawStandardPolynomial 15 9 := by
  have hh : rawCoordinate 7 15 9=rawCoordinate 7 9 15 := by
    rw [rawCoordinate_sparse 7 15 9 rawEntry_7_09_15 rawEntry_7_15_09_data,rawCoordinate_sparse 7 9 15 rawEntry_7_09_15 rawEntry_7_09_15_data]
  rw [hh,rawEntry_7_09_15_physical]
  exact rawStandardPolynomial_symm 9 15
def rawEntry_7_09_16 : SparseEntry := [(59,162),(61,-54),(63,12)]
theorem rawEntry_7_09_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 16=sparseCoefficient rawEntry_7_09_16 r := by decide +kernel
theorem rawEntry_7_09_16_coordinates : sparsePolynomial 81 rawEntry_7_09_16=rawStandardCoordinates 9 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_16_physical : invariantSubst (rawCoordinate 7 9 16)=rawStandardPolynomial 9 16 := by
  rw [rawCoordinate_sparse 7 9 16 rawEntry_7_09_16 rawEntry_7_09_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_16)=_
  rw [rawEntry_7_09_16_coordinates]
  exact rawStandard_subst 9 16
theorem rawEntry_7_16_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 9=sparseCoefficient rawEntry_7_09_16 r := by decide +kernel
theorem rawEntry_7_16_09_physical : invariantSubst (rawCoordinate 7 16 9)=rawStandardPolynomial 16 9 := by
  have hh : rawCoordinate 7 16 9=rawCoordinate 7 9 16 := by
    rw [rawCoordinate_sparse 7 16 9 rawEntry_7_09_16 rawEntry_7_16_09_data,rawCoordinate_sparse 7 9 16 rawEntry_7_09_16 rawEntry_7_09_16_data]
  rw [hh,rawEntry_7_09_16_physical]
  exact rawStandardPolynomial_symm 9 16
def rawEntry_7_09_17 : SparseEntry := [(62,162),(63,-54),(65,12)]
theorem rawEntry_7_09_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 9 17=sparseCoefficient rawEntry_7_09_17 r := by decide +kernel
theorem rawEntry_7_09_17_coordinates : sparsePolynomial 81 rawEntry_7_09_17=rawStandardCoordinates 9 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_09_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_09_17_physical : invariantSubst (rawCoordinate 7 9 17)=rawStandardPolynomial 9 17 := by
  rw [rawCoordinate_sparse 7 9 17 rawEntry_7_09_17 rawEntry_7_09_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_09_17)=_
  rw [rawEntry_7_09_17_coordinates]
  exact rawStandard_subst 9 17
theorem rawEntry_7_17_09_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 9=sparseCoefficient rawEntry_7_09_17 r := by decide +kernel
theorem rawEntry_7_17_09_physical : invariantSubst (rawCoordinate 7 17 9)=rawStandardPolynomial 17 9 := by
  have hh : rawCoordinate 7 17 9=rawCoordinate 7 9 17 := by
    rw [rawCoordinate_sparse 7 17 9 rawEntry_7_09_17 rawEntry_7_17_09_data,rawCoordinate_sparse 7 9 17 rawEntry_7_09_17 rawEntry_7_09_17_data]
  rw [hh,rawEntry_7_09_17_physical]
  exact rawStandardPolynomial_symm 9 17
def rawEntry_7_10_10 : SparseEntry := [(65,-108),(66,36)]
theorem rawEntry_7_10_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 10=sparseCoefficient rawEntry_7_10_10 r := by decide +kernel
theorem rawEntry_7_10_10_coordinates : sparsePolynomial 81 rawEntry_7_10_10=rawStandardCoordinates 10 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_10,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_10_physical : invariantSubst (rawCoordinate 7 10 10)=rawStandardPolynomial 10 10 := by
  rw [rawCoordinate_sparse 7 10 10 rawEntry_7_10_10 rawEntry_7_10_10_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_10)=_
  rw [rawEntry_7_10_10_coordinates]
  exact rawStandard_subst 10 10
def rawEntry_7_10_11 : SparseEntry := [(28,162),(29,-54),(30,12)]
theorem rawEntry_7_10_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 11=sparseCoefficient rawEntry_7_10_11 r := by decide +kernel
theorem rawEntry_7_10_11_coordinates : sparsePolynomial 81 rawEntry_7_10_11=rawStandardCoordinates 10 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_11_physical : invariantSubst (rawCoordinate 7 10 11)=rawStandardPolynomial 10 11 := by
  rw [rawCoordinate_sparse 7 10 11 rawEntry_7_10_11 rawEntry_7_10_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_11)=_
  rw [rawEntry_7_10_11_coordinates]
  exact rawStandard_subst 10 11
theorem rawEntry_7_11_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 10=sparseCoefficient rawEntry_7_10_11 r := by decide +kernel
theorem rawEntry_7_11_10_physical : invariantSubst (rawCoordinate 7 11 10)=rawStandardPolynomial 11 10 := by
  have hh : rawCoordinate 7 11 10=rawCoordinate 7 10 11 := by
    rw [rawCoordinate_sparse 7 11 10 rawEntry_7_10_11 rawEntry_7_11_10_data,rawCoordinate_sparse 7 10 11 rawEntry_7_10_11 rawEntry_7_10_11_data]
  rw [hh,rawEntry_7_10_11_physical]
  exact rawStandardPolynomial_symm 10 11
def rawEntry_7_10_12 : SparseEntry := [(38,162),(39,-54),(40,12)]
theorem rawEntry_7_10_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 12=sparseCoefficient rawEntry_7_10_12 r := by decide +kernel
theorem rawEntry_7_10_12_coordinates : sparsePolynomial 81 rawEntry_7_10_12=rawStandardCoordinates 10 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_12_physical : invariantSubst (rawCoordinate 7 10 12)=rawStandardPolynomial 10 12 := by
  rw [rawCoordinate_sparse 7 10 12 rawEntry_7_10_12 rawEntry_7_10_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_12)=_
  rw [rawEntry_7_10_12_coordinates]
  exact rawStandard_subst 10 12
theorem rawEntry_7_12_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 10=sparseCoefficient rawEntry_7_10_12 r := by decide +kernel
theorem rawEntry_7_12_10_physical : invariantSubst (rawCoordinate 7 12 10)=rawStandardPolynomial 12 10 := by
  have hh : rawCoordinate 7 12 10=rawCoordinate 7 10 12 := by
    rw [rawCoordinate_sparse 7 12 10 rawEntry_7_10_12 rawEntry_7_12_10_data,rawCoordinate_sparse 7 10 12 rawEntry_7_10_12 rawEntry_7_10_12_data]
  rw [hh,rawEntry_7_10_12_physical]
  exact rawStandardPolynomial_symm 10 12
def rawEntry_7_10_13 : SparseEntry := [(48,162),(49,-54),(51,12)]
theorem rawEntry_7_10_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 13=sparseCoefficient rawEntry_7_10_13 r := by decide +kernel
theorem rawEntry_7_10_13_coordinates : sparsePolynomial 81 rawEntry_7_10_13=rawStandardCoordinates 10 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_13_physical : invariantSubst (rawCoordinate 7 10 13)=rawStandardPolynomial 10 13 := by
  rw [rawCoordinate_sparse 7 10 13 rawEntry_7_10_13 rawEntry_7_10_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_13)=_
  rw [rawEntry_7_10_13_coordinates]
  exact rawStandard_subst 10 13
theorem rawEntry_7_13_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 10=sparseCoefficient rawEntry_7_10_13 r := by decide +kernel
theorem rawEntry_7_13_10_physical : invariantSubst (rawCoordinate 7 13 10)=rawStandardPolynomial 13 10 := by
  have hh : rawCoordinate 7 13 10=rawCoordinate 7 10 13 := by
    rw [rawCoordinate_sparse 7 13 10 rawEntry_7_10_13 rawEntry_7_13_10_data,rawCoordinate_sparse 7 10 13 rawEntry_7_10_13 rawEntry_7_10_13_data]
  rw [hh,rawEntry_7_10_13_physical]
  exact rawStandardPolynomial_symm 10 13
def rawEntry_7_10_14 : SparseEntry := [(50,162),(51,-54),(52,12)]
theorem rawEntry_7_10_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 14=sparseCoefficient rawEntry_7_10_14 r := by decide +kernel
theorem rawEntry_7_10_14_coordinates : sparsePolynomial 81 rawEntry_7_10_14=rawStandardCoordinates 10 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_14_physical : invariantSubst (rawCoordinate 7 10 14)=rawStandardPolynomial 10 14 := by
  rw [rawCoordinate_sparse 7 10 14 rawEntry_7_10_14 rawEntry_7_10_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_14)=_
  rw [rawEntry_7_10_14_coordinates]
  exact rawStandard_subst 10 14
theorem rawEntry_7_14_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 10=sparseCoefficient rawEntry_7_10_14 r := by decide +kernel
theorem rawEntry_7_14_10_physical : invariantSubst (rawCoordinate 7 14 10)=rawStandardPolynomial 14 10 := by
  have hh : rawCoordinate 7 14 10=rawCoordinate 7 10 14 := by
    rw [rawCoordinate_sparse 7 14 10 rawEntry_7_10_14 rawEntry_7_14_10_data,rawCoordinate_sparse 7 10 14 rawEntry_7_10_14 rawEntry_7_10_14_data]
  rw [hh,rawEntry_7_10_14_physical]
  exact rawStandardPolynomial_symm 10 14
end ThomsonNegative.Certificate.Bridges
