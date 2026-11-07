import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_7_13_17 : SparseEntry := [(47,36),(49,-24),(51,4)]
theorem rawEntry_7_13_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 13 17=sparseCoefficient rawEntry_7_13_17 r := by decide +kernel
theorem rawEntry_7_13_17_coordinates : sparsePolynomial 81 rawEntry_7_13_17=rawStandardCoordinates 13 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_13_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_13_17_physical : invariantSubst (rawCoordinate 7 13 17)=rawStandardPolynomial 13 17 := by
  rw [rawCoordinate_sparse 7 13 17 rawEntry_7_13_17 rawEntry_7_13_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_13_17)=_
  rw [rawEntry_7_13_17_coordinates]
  exact rawStandard_subst 13 17
theorem rawEntry_7_17_13_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 13=sparseCoefficient rawEntry_7_13_17 r := by decide +kernel
theorem rawEntry_7_17_13_physical : invariantSubst (rawCoordinate 7 17 13)=rawStandardPolynomial 17 13 := by
  have hh : rawCoordinate 7 17 13=rawCoordinate 7 13 17 := by
    rw [rawCoordinate_sparse 7 17 13 rawEntry_7_13_17 rawEntry_7_17_13_data,rawCoordinate_sparse 7 13 17 rawEntry_7_13_17 rawEntry_7_13_17_data]
  rw [hh,rawEntry_7_13_17_physical]
  exact rawStandardPolynomial_symm 13 17
def rawEntry_7_14_14 : SparseEntry := [(37,36),(39,-24),(40,4)]
theorem rawEntry_7_14_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 14=sparseCoefficient rawEntry_7_14_14 r := by decide +kernel
theorem rawEntry_7_14_14_coordinates : sparsePolynomial 81 rawEntry_7_14_14=rawStandardCoordinates 14 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_14_14,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_14_14_physical : invariantSubst (rawCoordinate 7 14 14)=rawStandardPolynomial 14 14 := by
  rw [rawCoordinate_sparse 7 14 14 rawEntry_7_14_14 rawEntry_7_14_14_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_14_14)=_
  rw [rawEntry_7_14_14_coordinates]
  exact rawStandard_subst 14 14
def rawEntry_7_14_15 : SparseEntry := [(45,36),(48,-24),(50,4)]
theorem rawEntry_7_14_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 15=sparseCoefficient rawEntry_7_14_15 r := by decide +kernel
theorem rawEntry_7_14_15_coordinates : sparsePolynomial 81 rawEntry_7_14_15=rawStandardCoordinates 14 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_14_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_14_15_physical : invariantSubst (rawCoordinate 7 14 15)=rawStandardPolynomial 14 15 := by
  rw [rawCoordinate_sparse 7 14 15 rawEntry_7_14_15 rawEntry_7_14_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_14_15)=_
  rw [rawEntry_7_14_15_coordinates]
  exact rawStandard_subst 14 15
theorem rawEntry_7_15_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 14=sparseCoefficient rawEntry_7_14_15 r := by decide +kernel
theorem rawEntry_7_15_14_physical : invariantSubst (rawCoordinate 7 15 14)=rawStandardPolynomial 15 14 := by
  have hh : rawCoordinate 7 15 14=rawCoordinate 7 14 15 := by
    rw [rawCoordinate_sparse 7 15 14 rawEntry_7_14_15 rawEntry_7_15_14_data,rawCoordinate_sparse 7 14 15 rawEntry_7_14_15 rawEntry_7_14_15_data]
  rw [hh,rawEntry_7_14_15_physical]
  exact rawStandardPolynomial_symm 14 15
def rawEntry_7_14_16 : SparseEntry := [(47,36),(49,-24),(51,4)]
theorem rawEntry_7_14_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 16=sparseCoefficient rawEntry_7_14_16 r := by decide +kernel
theorem rawEntry_7_14_16_coordinates : sparsePolynomial 81 rawEntry_7_14_16=rawStandardCoordinates 14 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_14_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_14_16_physical : invariantSubst (rawCoordinate 7 14 16)=rawStandardPolynomial 14 16 := by
  rw [rawCoordinate_sparse 7 14 16 rawEntry_7_14_16 rawEntry_7_14_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_14_16)=_
  rw [rawEntry_7_14_16_coordinates]
  exact rawStandard_subst 14 16
theorem rawEntry_7_16_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 14=sparseCoefficient rawEntry_7_14_16 r := by decide +kernel
theorem rawEntry_7_16_14_physical : invariantSubst (rawCoordinate 7 16 14)=rawStandardPolynomial 16 14 := by
  have hh : rawCoordinate 7 16 14=rawCoordinate 7 14 16 := by
    rw [rawCoordinate_sparse 7 16 14 rawEntry_7_14_16 rawEntry_7_16_14_data,rawCoordinate_sparse 7 14 16 rawEntry_7_14_16 rawEntry_7_14_16_data]
  rw [hh,rawEntry_7_14_16_physical]
  exact rawStandardPolynomial_symm 14 16
def rawEntry_7_14_17 : SparseEntry := [(49,36),(51,-24),(52,4)]
theorem rawEntry_7_14_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 14 17=sparseCoefficient rawEntry_7_14_17 r := by decide +kernel
theorem rawEntry_7_14_17_coordinates : sparsePolynomial 81 rawEntry_7_14_17=rawStandardCoordinates 14 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_14_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_14_17_physical : invariantSubst (rawCoordinate 7 14 17)=rawStandardPolynomial 14 17 := by
  rw [rawCoordinate_sparse 7 14 17 rawEntry_7_14_17 rawEntry_7_14_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_14_17)=_
  rw [rawEntry_7_14_17_coordinates]
  exact rawStandard_subst 14 17
theorem rawEntry_7_17_14_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 14=sparseCoefficient rawEntry_7_14_17 r := by decide +kernel
theorem rawEntry_7_17_14_physical : invariantSubst (rawCoordinate 7 17 14)=rawStandardPolynomial 17 14 := by
  have hh : rawCoordinate 7 17 14=rawCoordinate 7 14 17 := by
    rw [rawCoordinate_sparse 7 17 14 rawEntry_7_14_17 rawEntry_7_17_14_data,rawCoordinate_sparse 7 14 17 rawEntry_7_14_17 rawEntry_7_14_17_data]
  rw [hh,rawEntry_7_14_17_physical]
  exact rawStandardPolynomial_symm 14 17
def rawEntry_7_15_15 : SparseEntry := [(53,36),(57,-24),(60,4)]
theorem rawEntry_7_15_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 15=sparseCoefficient rawEntry_7_15_15 r := by decide +kernel
theorem rawEntry_7_15_15_coordinates : sparsePolynomial 81 rawEntry_7_15_15=rawStandardCoordinates 15 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_15_15,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_15_15_physical : invariantSubst (rawCoordinate 7 15 15)=rawStandardPolynomial 15 15 := by
  rw [rawCoordinate_sparse 7 15 15 rawEntry_7_15_15 rawEntry_7_15_15_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_15_15)=_
  rw [rawEntry_7_15_15_coordinates]
  exact rawStandard_subst 15 15
def rawEntry_7_15_16 : SparseEntry := [(56,36),(59,-24),(62,4)]
theorem rawEntry_7_15_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 16=sparseCoefficient rawEntry_7_15_16 r := by decide +kernel
theorem rawEntry_7_15_16_coordinates : sparsePolynomial 81 rawEntry_7_15_16=rawStandardCoordinates 15 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_15_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_15_16_physical : invariantSubst (rawCoordinate 7 15 16)=rawStandardPolynomial 15 16 := by
  rw [rawCoordinate_sparse 7 15 16 rawEntry_7_15_16 rawEntry_7_15_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_15_16)=_
  rw [rawEntry_7_15_16_coordinates]
  exact rawStandard_subst 15 16
theorem rawEntry_7_16_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 15=sparseCoefficient rawEntry_7_15_16 r := by decide +kernel
theorem rawEntry_7_16_15_physical : invariantSubst (rawCoordinate 7 16 15)=rawStandardPolynomial 16 15 := by
  have hh : rawCoordinate 7 16 15=rawCoordinate 7 15 16 := by
    rw [rawCoordinate_sparse 7 16 15 rawEntry_7_15_16 rawEntry_7_16_15_data,rawCoordinate_sparse 7 15 16 rawEntry_7_15_16 rawEntry_7_15_16_data]
  rw [hh,rawEntry_7_15_16_physical]
  exact rawStandardPolynomial_symm 15 16
def rawEntry_7_15_17 : SparseEntry := [(59,36),(62,-24),(64,4)]
theorem rawEntry_7_15_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 15 17=sparseCoefficient rawEntry_7_15_17 r := by decide +kernel
theorem rawEntry_7_15_17_coordinates : sparsePolynomial 81 rawEntry_7_15_17=rawStandardCoordinates 15 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_15_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_15_17_physical : invariantSubst (rawCoordinate 7 15 17)=rawStandardPolynomial 15 17 := by
  rw [rawCoordinate_sparse 7 15 17 rawEntry_7_15_17 rawEntry_7_15_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_15_17)=_
  rw [rawEntry_7_15_17_coordinates]
  exact rawStandard_subst 15 17
theorem rawEntry_7_17_15_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 15=sparseCoefficient rawEntry_7_15_17 r := by decide +kernel
theorem rawEntry_7_17_15_physical : invariantSubst (rawCoordinate 7 17 15)=rawStandardPolynomial 17 15 := by
  have hh : rawCoordinate 7 17 15=rawCoordinate 7 15 17 := by
    rw [rawCoordinate_sparse 7 17 15 rawEntry_7_15_17 rawEntry_7_17_15_data,rawCoordinate_sparse 7 15 17 rawEntry_7_15_17 rawEntry_7_15_17_data]
  rw [hh,rawEntry_7_15_17_physical]
  exact rawStandardPolynomial_symm 15 17
def rawEntry_7_16_16 : SparseEntry := [(58,36),(61,-24),(63,4)]
theorem rawEntry_7_16_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 16=sparseCoefficient rawEntry_7_16_16 r := by decide +kernel
theorem rawEntry_7_16_16_coordinates : sparsePolynomial 81 rawEntry_7_16_16=rawStandardCoordinates 16 16 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_16_16,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_16_16_physical : invariantSubst (rawCoordinate 7 16 16)=rawStandardPolynomial 16 16 := by
  rw [rawCoordinate_sparse 7 16 16 rawEntry_7_16_16 rawEntry_7_16_16_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_16_16)=_
  rw [rawEntry_7_16_16_coordinates]
  exact rawStandard_subst 16 16
def rawEntry_7_16_17 : SparseEntry := [(61,36),(63,-24),(65,4)]
theorem rawEntry_7_16_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 16 17=sparseCoefficient rawEntry_7_16_17 r := by decide +kernel
theorem rawEntry_7_16_17_coordinates : sparsePolynomial 81 rawEntry_7_16_17=rawStandardCoordinates 16 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_16_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_16_17_physical : invariantSubst (rawCoordinate 7 16 17)=rawStandardPolynomial 16 17 := by
  rw [rawCoordinate_sparse 7 16 17 rawEntry_7_16_17 rawEntry_7_16_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_16_17)=_
  rw [rawEntry_7_16_17_coordinates]
  exact rawStandard_subst 16 17
theorem rawEntry_7_17_16_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 16=sparseCoefficient rawEntry_7_16_17 r := by decide +kernel
theorem rawEntry_7_17_16_physical : invariantSubst (rawCoordinate 7 17 16)=rawStandardPolynomial 17 16 := by
  have hh : rawCoordinate 7 17 16=rawCoordinate 7 16 17 := by
    rw [rawCoordinate_sparse 7 17 16 rawEntry_7_16_17 rawEntry_7_17_16_data,rawCoordinate_sparse 7 16 17 rawEntry_7_16_17 rawEntry_7_16_17_data]
  rw [hh,rawEntry_7_16_17_physical]
  exact rawStandardPolynomial_symm 16 17
def rawEntry_7_17_17 : SparseEntry := [(63,36),(65,-24),(66,4)]
theorem rawEntry_7_17_17_data : ∀r : Fin 102, RawData.coefficient 7 r.val 17 17=sparseCoefficient rawEntry_7_17_17 r := by decide +kernel
theorem rawEntry_7_17_17_coordinates : sparsePolynomial 81 rawEntry_7_17_17=rawStandardCoordinates 17 17 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_7_17_17,coordinateMonomial,rawStandardCoordinates,standardPairCoordinates,addTag,standardTag] <;> ring
theorem rawEntry_7_17_17_physical : invariantSubst (rawCoordinate 7 17 17)=rawStandardPolynomial 17 17 := by
  rw [rawCoordinate_sparse 7 17 17 rawEntry_7_17_17 rawEntry_7_17_17_data]
  change invariantSubst (sparsePolynomial 81 rawEntry_7_17_17)=_
  rw [rawEntry_7_17_17_coordinates]
  exact rawStandard_subst 17 17
end ThomsonNegative.Certificate.Bridges
