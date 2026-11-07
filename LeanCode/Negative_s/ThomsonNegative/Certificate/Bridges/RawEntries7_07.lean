import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_10_15 : SparseEntry := [(60,162),(62,-54),(64,12)]
theorem rawEntry_7_10_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 15=sparseCoefficient rawEntry_7_10_15 r := by decide +kernel
theorem rawEntry_7_10_15_coordinates : sparsePolynomial 81 rawEntry_7_10_15=rawStandardCoordinates 10 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_15_physical : invariantSubst (rawCoordinate 7 10 15)=rawStandardPolynomial 10 15 := by
  rw [rawCoordinate_sparse 7 10 15 rawEntry_7_10_15 rawEntry_7_10_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_15)=_
  rw [rawEntry_7_10_15_coordinates]
  exact rawStandard_subst 10 15
theorem rawEntry_7_15_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 10=sparseCoefficient rawEntry_7_10_15 r := by decide +kernel
theorem rawEntry_7_15_10_physical : invariantSubst (rawCoordinate 7 15 10)=rawStandardPolynomial 15 10 := by
  have hh : rawCoordinate 7 15 10=rawCoordinate 7 10 15 := by
    rw [rawCoordinate_sparse 7 15 10 rawEntry_7_10_15 rawEntry_7_15_10_data,rawCoordinate_sparse 7 10 15 rawEntry_7_10_15 rawEntry_7_10_15_data]
  rw [hh,rawEntry_7_10_15_physical]
  exact rawStandardPolynomial_symm 10 15
def rawEntry_7_10_16 : SparseEntry := [(62,162),(63,-54),(65,12)]
theorem rawEntry_7_10_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 16=sparseCoefficient rawEntry_7_10_16 r := by decide +kernel
theorem rawEntry_7_10_16_coordinates : sparsePolynomial 81 rawEntry_7_10_16=rawStandardCoordinates 10 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_16_physical : invariantSubst (rawCoordinate 7 10 16)=rawStandardPolynomial 10 16 := by
  rw [rawCoordinate_sparse 7 10 16 rawEntry_7_10_16 rawEntry_7_10_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_16)=_
  rw [rawEntry_7_10_16_coordinates]
  exact rawStandard_subst 10 16
theorem rawEntry_7_16_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 10=sparseCoefficient rawEntry_7_10_16 r := by decide +kernel
theorem rawEntry_7_16_10_physical : invariantSubst (rawCoordinate 7 16 10)=rawStandardPolynomial 16 10 := by
  have hh : rawCoordinate 7 16 10=rawCoordinate 7 10 16 := by
    rw [rawCoordinate_sparse 7 16 10 rawEntry_7_10_16 rawEntry_7_16_10_data,rawCoordinate_sparse 7 10 16 rawEntry_7_10_16 rawEntry_7_10_16_data]
  rw [hh,rawEntry_7_10_16_physical]
  exact rawStandardPolynomial_symm 10 16
def rawEntry_7_10_17 : SparseEntry := [(64,162),(65,-54),(66,12)]
theorem rawEntry_7_10_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 10 17=sparseCoefficient rawEntry_7_10_17 r := by decide +kernel
theorem rawEntry_7_10_17_coordinates : sparsePolynomial 81 rawEntry_7_10_17=rawStandardCoordinates 10 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_10_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_10_17_physical : invariantSubst (rawCoordinate 7 10 17)=rawStandardPolynomial 10 17 := by
  rw [rawCoordinate_sparse 7 10 17 rawEntry_7_10_17 rawEntry_7_10_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_10_17)=_
  rw [rawEntry_7_10_17_coordinates]
  exact rawStandard_subst 10 17
theorem rawEntry_7_17_10_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 10=sparseCoefficient rawEntry_7_10_17 r := by decide +kernel
theorem rawEntry_7_17_10_physical : invariantSubst (rawCoordinate 7 17 10)=rawStandardPolynomial 17 10 := by
  have hh : rawCoordinate 7 17 10=rawCoordinate 7 10 17 := by
    rw [rawCoordinate_sparse 7 17 10 rawEntry_7_10_17 rawEntry_7_17_10_data,rawCoordinate_sparse 7 10 17 rawEntry_7_10_17 rawEntry_7_10_17_data]
  rw [hh,rawEntry_7_10_17_physical]
  exact rawStandardPolynomial_symm 10 17
def rawEntry_7_11_11 : SparseEntry := [(7,36),(9,-24),(10,4)]
theorem rawEntry_7_11_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 11=sparseCoefficient rawEntry_7_11_11 r := by decide +kernel
theorem rawEntry_7_11_11_coordinates : sparsePolynomial 81 rawEntry_7_11_11=rawStandardCoordinates 11 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_11,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_11_physical : invariantSubst (rawCoordinate 7 11 11)=rawStandardPolynomial 11 11 := by
  rw [rawCoordinate_sparse 7 11 11 rawEntry_7_11_11 rawEntry_7_11_11_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_11)=_
  rw [rawEntry_7_11_11_coordinates]
  exact rawStandard_subst 11 11
def rawEntry_7_11_12 : SparseEntry := [(12,36),(14,-24),(15,4)]
theorem rawEntry_7_11_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 12=sparseCoefficient rawEntry_7_11_12 r := by decide +kernel
theorem rawEntry_7_11_12_coordinates : sparsePolynomial 81 rawEntry_7_11_12=rawStandardCoordinates 11 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_12_physical : invariantSubst (rawCoordinate 7 11 12)=rawStandardPolynomial 11 12 := by
  rw [rawCoordinate_sparse 7 11 12 rawEntry_7_11_12 rawEntry_7_11_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_12)=_
  rw [rawEntry_7_11_12_coordinates]
  exact rawStandard_subst 11 12
theorem rawEntry_7_12_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 11=sparseCoefficient rawEntry_7_11_12 r := by decide +kernel
theorem rawEntry_7_12_11_physical : invariantSubst (rawCoordinate 7 12 11)=rawStandardPolynomial 12 11 := by
  have hh : rawCoordinate 7 12 11=rawCoordinate 7 11 12 := by
    rw [rawCoordinate_sparse 7 12 11 rawEntry_7_11_12 rawEntry_7_12_11_data,rawCoordinate_sparse 7 11 12 rawEntry_7_11_12 rawEntry_7_11_12_data]
  rw [hh,rawEntry_7_11_12_physical]
  exact rawStandardPolynomial_symm 11 12
def rawEntry_7_11_13 : SparseEntry := [(17,36),(19,-24),(21,4)]
theorem rawEntry_7_11_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 13=sparseCoefficient rawEntry_7_11_13 r := by decide +kernel
theorem rawEntry_7_11_13_coordinates : sparsePolynomial 81 rawEntry_7_11_13=rawStandardCoordinates 11 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_13_physical : invariantSubst (rawCoordinate 7 11 13)=rawStandardPolynomial 11 13 := by
  rw [rawCoordinate_sparse 7 11 13 rawEntry_7_11_13 rawEntry_7_11_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_13)=_
  rw [rawEntry_7_11_13_coordinates]
  exact rawStandard_subst 11 13
theorem rawEntry_7_13_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 11=sparseCoefficient rawEntry_7_11_13 r := by decide +kernel
theorem rawEntry_7_13_11_physical : invariantSubst (rawCoordinate 7 13 11)=rawStandardPolynomial 13 11 := by
  have hh : rawCoordinate 7 13 11=rawCoordinate 7 11 13 := by
    rw [rawCoordinate_sparse 7 13 11 rawEntry_7_11_13 rawEntry_7_13_11_data,rawCoordinate_sparse 7 11 13 rawEntry_7_11_13 rawEntry_7_11_13_data]
  rw [hh,rawEntry_7_11_13_physical]
  exact rawStandardPolynomial_symm 11 13
def rawEntry_7_11_14 : SparseEntry := [(19,36),(21,-24),(22,4)]
theorem rawEntry_7_11_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 14=sparseCoefficient rawEntry_7_11_14 r := by decide +kernel
theorem rawEntry_7_11_14_coordinates : sparsePolynomial 81 rawEntry_7_11_14=rawStandardCoordinates 11 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_14_physical : invariantSubst (rawCoordinate 7 11 14)=rawStandardPolynomial 11 14 := by
  rw [rawCoordinate_sparse 7 11 14 rawEntry_7_11_14 rawEntry_7_11_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_14)=_
  rw [rawEntry_7_11_14_coordinates]
  exact rawStandard_subst 11 14
theorem rawEntry_7_14_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 11=sparseCoefficient rawEntry_7_11_14 r := by decide +kernel
theorem rawEntry_7_14_11_physical : invariantSubst (rawCoordinate 7 14 11)=rawStandardPolynomial 14 11 := by
  have hh : rawCoordinate 7 14 11=rawCoordinate 7 11 14 := by
    rw [rawCoordinate_sparse 7 14 11 rawEntry_7_11_14 rawEntry_7_14_11_data,rawCoordinate_sparse 7 11 14 rawEntry_7_11_14 rawEntry_7_11_14_data]
  rw [hh,rawEntry_7_11_14_physical]
  exact rawStandardPolynomial_symm 11 14
def rawEntry_7_11_15 : SparseEntry := [(23,36),(26,-24),(28,4)]
theorem rawEntry_7_11_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 15=sparseCoefficient rawEntry_7_11_15 r := by decide +kernel
theorem rawEntry_7_11_15_coordinates : sparsePolynomial 81 rawEntry_7_11_15=rawStandardCoordinates 11 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_15_physical : invariantSubst (rawCoordinate 7 11 15)=rawStandardPolynomial 11 15 := by
  rw [rawCoordinate_sparse 7 11 15 rawEntry_7_11_15 rawEntry_7_11_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_15)=_
  rw [rawEntry_7_11_15_coordinates]
  exact rawStandard_subst 11 15
theorem rawEntry_7_15_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 11=sparseCoefficient rawEntry_7_11_15 r := by decide +kernel
theorem rawEntry_7_15_11_physical : invariantSubst (rawCoordinate 7 15 11)=rawStandardPolynomial 15 11 := by
  have hh : rawCoordinate 7 15 11=rawCoordinate 7 11 15 := by
    rw [rawCoordinate_sparse 7 15 11 rawEntry_7_11_15 rawEntry_7_15_11_data,rawCoordinate_sparse 7 11 15 rawEntry_7_11_15 rawEntry_7_11_15_data]
  rw [hh,rawEntry_7_11_15_physical]
  exact rawStandardPolynomial_symm 11 15
def rawEntry_7_11_16 : SparseEntry := [(25,36),(27,-24),(29,4)]
theorem rawEntry_7_11_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 16=sparseCoefficient rawEntry_7_11_16 r := by decide +kernel
theorem rawEntry_7_11_16_coordinates : sparsePolynomial 81 rawEntry_7_11_16=rawStandardCoordinates 11 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_16_physical : invariantSubst (rawCoordinate 7 11 16)=rawStandardPolynomial 11 16 := by
  rw [rawCoordinate_sparse 7 11 16 rawEntry_7_11_16 rawEntry_7_11_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_16)=_
  rw [rawEntry_7_11_16_coordinates]
  exact rawStandard_subst 11 16
theorem rawEntry_7_16_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 11=sparseCoefficient rawEntry_7_11_16 r := by decide +kernel
theorem rawEntry_7_16_11_physical : invariantSubst (rawCoordinate 7 16 11)=rawStandardPolynomial 16 11 := by
  have hh : rawCoordinate 7 16 11=rawCoordinate 7 11 16 := by
    rw [rawCoordinate_sparse 7 16 11 rawEntry_7_11_16 rawEntry_7_16_11_data,rawCoordinate_sparse 7 11 16 rawEntry_7_11_16 rawEntry_7_11_16_data]
  rw [hh,rawEntry_7_11_16_physical]
  exact rawStandardPolynomial_symm 11 16
def rawEntry_7_11_17 : SparseEntry := [(27,36),(29,-24),(30,4)]
theorem rawEntry_7_11_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 11 17=sparseCoefficient rawEntry_7_11_17 r := by decide +kernel
theorem rawEntry_7_11_17_coordinates : sparsePolynomial 81 rawEntry_7_11_17=rawStandardCoordinates 11 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_11_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_11_17_physical : invariantSubst (rawCoordinate 7 11 17)=rawStandardPolynomial 11 17 := by
  rw [rawCoordinate_sparse 7 11 17 rawEntry_7_11_17 rawEntry_7_11_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_11_17)=_
  rw [rawEntry_7_11_17_coordinates]
  exact rawStandard_subst 11 17
theorem rawEntry_7_17_11_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 11=sparseCoefficient rawEntry_7_11_17 r := by decide +kernel
theorem rawEntry_7_17_11_physical : invariantSubst (rawCoordinate 7 17 11)=rawStandardPolynomial 17 11 := by
  have hh : rawCoordinate 7 17 11=rawCoordinate 7 11 17 := by
    rw [rawCoordinate_sparse 7 17 11 rawEntry_7_11_17 rawEntry_7_17_11_data,rawCoordinate_sparse 7 11 17 rawEntry_7_11_17 rawEntry_7_11_17_data]
  rw [hh,rawEntry_7_11_17_physical]
  exact rawStandardPolynomial_symm 11 17
def rawEntry_7_12_12 : SparseEntry := [(19,36),(21,-24),(22,4)]
theorem rawEntry_7_12_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 12=sparseCoefficient rawEntry_7_12_12 r := by decide +kernel
theorem rawEntry_7_12_12_coordinates : sparsePolynomial 81 rawEntry_7_12_12=rawStandardCoordinates 12 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_12,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_12_physical : invariantSubst (rawCoordinate 7 12 12)=rawStandardPolynomial 12 12 := by
  rw [rawCoordinate_sparse 7 12 12 rawEntry_7_12_12 rawEntry_7_12_12_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_12)=_
  rw [rawEntry_7_12_12_coordinates]
  exact rawStandard_subst 12 12
def rawEntry_7_12_13 : SparseEntry := [(25,36),(27,-24),(29,4)]
theorem rawEntry_7_12_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 13=sparseCoefficient rawEntry_7_12_13 r := by decide +kernel
theorem rawEntry_7_12_13_coordinates : sparsePolynomial 81 rawEntry_7_12_13=rawStandardCoordinates 12 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_13_physical : invariantSubst (rawCoordinate 7 12 13)=rawStandardPolynomial 12 13 := by
  rw [rawCoordinate_sparse 7 12 13 rawEntry_7_12_13 rawEntry_7_12_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_13)=_
  rw [rawEntry_7_12_13_coordinates]
  exact rawStandard_subst 12 13
theorem rawEntry_7_13_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 12=sparseCoefficient rawEntry_7_12_13 r := by decide +kernel
theorem rawEntry_7_13_12_physical : invariantSubst (rawCoordinate 7 13 12)=rawStandardPolynomial 13 12 := by
  have hh : rawCoordinate 7 13 12=rawCoordinate 7 12 13 := by
    rw [rawCoordinate_sparse 7 13 12 rawEntry_7_12_13 rawEntry_7_13_12_data,rawCoordinate_sparse 7 12 13 rawEntry_7_12_13 rawEntry_7_12_13_data]
  rw [hh,rawEntry_7_12_13_physical]
  exact rawStandardPolynomial_symm 12 13
def rawEntry_7_12_14 : SparseEntry := [(27,36),(29,-24),(30,4)]
theorem rawEntry_7_12_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 14=sparseCoefficient rawEntry_7_12_14 r := by decide +kernel
theorem rawEntry_7_12_14_coordinates : sparsePolynomial 81 rawEntry_7_12_14=rawStandardCoordinates 12 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_14_physical : invariantSubst (rawCoordinate 7 12 14)=rawStandardPolynomial 12 14 := by
  rw [rawCoordinate_sparse 7 12 14 rawEntry_7_12_14 rawEntry_7_12_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_14)=_
  rw [rawEntry_7_12_14_coordinates]
  exact rawStandard_subst 12 14
theorem rawEntry_7_14_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 12=sparseCoefficient rawEntry_7_12_14 r := by decide +kernel
theorem rawEntry_7_14_12_physical : invariantSubst (rawCoordinate 7 14 12)=rawStandardPolynomial 14 12 := by
  have hh : rawCoordinate 7 14 12=rawCoordinate 7 12 14 := by
    rw [rawCoordinate_sparse 7 14 12 rawEntry_7_12_14 rawEntry_7_14_12_data,rawCoordinate_sparse 7 12 14 rawEntry_7_12_14 rawEntry_7_12_14_data]
  rw [hh,rawEntry_7_12_14_physical]
  exact rawStandardPolynomial_symm 12 14
def rawEntry_7_12_15 : SparseEntry := [(33,36),(36,-24),(38,4)]
theorem rawEntry_7_12_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 15=sparseCoefficient rawEntry_7_12_15 r := by decide +kernel
theorem rawEntry_7_12_15_coordinates : sparsePolynomial 81 rawEntry_7_12_15=rawStandardCoordinates 12 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_15_physical : invariantSubst (rawCoordinate 7 12 15)=rawStandardPolynomial 12 15 := by
  rw [rawCoordinate_sparse 7 12 15 rawEntry_7_12_15 rawEntry_7_12_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_15)=_
  rw [rawEntry_7_12_15_coordinates]
  exact rawStandard_subst 12 15
theorem rawEntry_7_15_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 12=sparseCoefficient rawEntry_7_12_15 r := by decide +kernel
theorem rawEntry_7_15_12_physical : invariantSubst (rawCoordinate 7 15 12)=rawStandardPolynomial 15 12 := by
  have hh : rawCoordinate 7 15 12=rawCoordinate 7 12 15 := by
    rw [rawCoordinate_sparse 7 15 12 rawEntry_7_12_15 rawEntry_7_15_12_data,rawCoordinate_sparse 7 12 15 rawEntry_7_12_15 rawEntry_7_12_15_data]
  rw [hh,rawEntry_7_12_15_physical]
  exact rawStandardPolynomial_symm 12 15
def rawEntry_7_12_16 : SparseEntry := [(35,36),(37,-24),(39,4)]
theorem rawEntry_7_12_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 16=sparseCoefficient rawEntry_7_12_16 r := by decide +kernel
theorem rawEntry_7_12_16_coordinates : sparsePolynomial 81 rawEntry_7_12_16=rawStandardCoordinates 12 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_16_physical : invariantSubst (rawCoordinate 7 12 16)=rawStandardPolynomial 12 16 := by
  rw [rawCoordinate_sparse 7 12 16 rawEntry_7_12_16 rawEntry_7_12_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_16)=_
  rw [rawEntry_7_12_16_coordinates]
  exact rawStandard_subst 12 16
theorem rawEntry_7_16_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 12=sparseCoefficient rawEntry_7_12_16 r := by decide +kernel
theorem rawEntry_7_16_12_physical : invariantSubst (rawCoordinate 7 16 12)=rawStandardPolynomial 16 12 := by
  have hh : rawCoordinate 7 16 12=rawCoordinate 7 12 16 := by
    rw [rawCoordinate_sparse 7 16 12 rawEntry_7_12_16 rawEntry_7_16_12_data,rawCoordinate_sparse 7 12 16 rawEntry_7_12_16 rawEntry_7_12_16_data]
  rw [hh,rawEntry_7_12_16_physical]
  exact rawStandardPolynomial_symm 12 16
def rawEntry_7_12_17 : SparseEntry := [(37,36),(39,-24),(40,4)]
theorem rawEntry_7_12_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 12 17=sparseCoefficient rawEntry_7_12_17 r := by decide +kernel
theorem rawEntry_7_12_17_coordinates : sparsePolynomial 81 rawEntry_7_12_17=rawStandardCoordinates 12 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_12_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_12_17_physical : invariantSubst (rawCoordinate 7 12 17)=rawStandardPolynomial 12 17 := by
  rw [rawCoordinate_sparse 7 12 17 rawEntry_7_12_17 rawEntry_7_12_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_12_17)=_
  rw [rawEntry_7_12_17_coordinates]
  exact rawStandard_subst 12 17
theorem rawEntry_7_17_12_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 12=sparseCoefficient rawEntry_7_12_17 r := by decide +kernel
theorem rawEntry_7_17_12_physical : invariantSubst (rawCoordinate 7 17 12)=rawStandardPolynomial 17 12 := by
  have hh : rawCoordinate 7 17 12=rawCoordinate 7 12 17 := by
    rw [rawCoordinate_sparse 7 17 12 rawEntry_7_12_17 rawEntry_7_17_12_data,rawCoordinate_sparse 7 12 17 rawEntry_7_12_17 rawEntry_7_12_17_data]
  rw [hh,rawEntry_7_12_17_physical]
  exact rawStandardPolynomial_symm 12 17
def rawEntry_7_13_13 : SparseEntry := [(32,36),(35,-24),(37,4)]
theorem rawEntry_7_13_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 13=sparseCoefficient rawEntry_7_13_13 r := by decide +kernel
theorem rawEntry_7_13_13_coordinates : sparsePolynomial 81 rawEntry_7_13_13=rawStandardCoordinates 13 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_13_13,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_13_13_physical : invariantSubst (rawCoordinate 7 13 13)=rawStandardPolynomial 13 13 := by
  rw [rawCoordinate_sparse 7 13 13 rawEntry_7_13_13 rawEntry_7_13_13_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_13_13)=_
  rw [rawEntry_7_13_13_coordinates]
  exact rawStandard_subst 13 13
def rawEntry_7_13_14 : SparseEntry := [(35,36),(37,-24),(39,4)]
theorem rawEntry_7_13_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 14=sparseCoefficient rawEntry_7_13_14 r := by decide +kernel
theorem rawEntry_7_13_14_coordinates : sparsePolynomial 81 rawEntry_7_13_14=rawStandardCoordinates 13 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_13_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_13_14_physical : invariantSubst (rawCoordinate 7 13 14)=rawStandardPolynomial 13 14 := by
  rw [rawCoordinate_sparse 7 13 14 rawEntry_7_13_14 rawEntry_7_13_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_13_14)=_
  rw [rawEntry_7_13_14_coordinates]
  exact rawStandard_subst 13 14
theorem rawEntry_7_14_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 13=sparseCoefficient rawEntry_7_13_14 r := by decide +kernel
theorem rawEntry_7_14_13_physical : invariantSubst (rawCoordinate 7 14 13)=rawStandardPolynomial 14 13 := by
  have hh : rawCoordinate 7 14 13=rawCoordinate 7 13 14 := by
    rw [rawCoordinate_sparse 7 14 13 rawEntry_7_13_14 rawEntry_7_14_13_data,rawCoordinate_sparse 7 13 14 rawEntry_7_13_14 rawEntry_7_13_14_data]
  rw [hh,rawEntry_7_13_14_physical]
  exact rawStandardPolynomial_symm 13 14
def rawEntry_7_13_15 : SparseEntry := [(42,36),(45,-24),(48,4)]
theorem rawEntry_7_13_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 15=sparseCoefficient rawEntry_7_13_15 r := by decide +kernel
theorem rawEntry_7_13_15_coordinates : sparsePolynomial 81 rawEntry_7_13_15=rawStandardCoordinates 13 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_13_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_13_15_physical : invariantSubst (rawCoordinate 7 13 15)=rawStandardPolynomial 13 15 := by
  rw [rawCoordinate_sparse 7 13 15 rawEntry_7_13_15 rawEntry_7_13_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_13_15)=_
  rw [rawEntry_7_13_15_coordinates]
  exact rawStandard_subst 13 15
theorem rawEntry_7_15_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 13=sparseCoefficient rawEntry_7_13_15 r := by decide +kernel
theorem rawEntry_7_15_13_physical : invariantSubst (rawCoordinate 7 15 13)=rawStandardPolynomial 15 13 := by
  have hh : rawCoordinate 7 15 13=rawCoordinate 7 13 15 := by
    rw [rawCoordinate_sparse 7 15 13 rawEntry_7_13_15 rawEntry_7_15_13_data,rawCoordinate_sparse 7 13 15 rawEntry_7_13_15 rawEntry_7_13_15_data]
  rw [hh,rawEntry_7_13_15_physical]
  exact rawStandardPolynomial_symm 13 15
def rawEntry_7_13_16 : SparseEntry := [(44,36),(47,-24),(49,4)]
theorem rawEntry_7_13_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 16=sparseCoefficient rawEntry_7_13_16 r := by decide +kernel
theorem rawEntry_7_13_16_coordinates : sparsePolynomial 81 rawEntry_7_13_16=rawStandardCoordinates 13 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_13_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_13_16_physical : invariantSubst (rawCoordinate 7 13 16)=rawStandardPolynomial 13 16 := by
  rw [rawCoordinate_sparse 7 13 16 rawEntry_7_13_16 rawEntry_7_13_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_13_16)=_
  rw [rawEntry_7_13_16_coordinates]
  exact rawStandard_subst 13 16
theorem rawEntry_7_16_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 13=sparseCoefficient rawEntry_7_13_16 r := by decide +kernel
theorem rawEntry_7_16_13_physical : invariantSubst (rawCoordinate 7 16 13)=rawStandardPolynomial 16 13 := by
  have hh : rawCoordinate 7 16 13=rawCoordinate 7 13 16 := by
    rw [rawCoordinate_sparse 7 16 13 rawEntry_7_13_16 rawEntry_7_16_13_data,rawCoordinate_sparse 7 13 16 rawEntry_7_13_16 rawEntry_7_13_16_data]
  rw [hh,rawEntry_7_13_16_physical]
  exact rawStandardPolynomial_symm 13 16
end ThomsonNegative.Certificate.Bridges
