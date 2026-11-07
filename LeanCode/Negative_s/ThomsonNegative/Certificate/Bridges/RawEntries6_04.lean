import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_05_15 : SparseEntry := [(39,1)]
theorem rawEntry_6_05_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 15=sparseCoefficient rawEntry_6_05_15 r := by decide +kernel
theorem rawEntry_6_05_15_coordinates : sparsePolynomial 1 rawEntry_6_05_15=rawPlusCoordinates 5 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_15_physical : invariantSubst (rawCoordinate 6 5 15)=rawPlusPolynomial 5 15 := by
  rw [rawCoordinate_sparse 6 5 15 rawEntry_6_05_15 rawEntry_6_05_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_15)=_
  rw [rawEntry_6_05_15_coordinates]
  exact rawPlus_subst 5 15
theorem rawEntry_6_15_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 5=sparseCoefficient rawEntry_6_05_15 r := by decide +kernel
theorem rawEntry_6_15_05_physical : invariantSubst (rawCoordinate 6 15 5)=rawPlusPolynomial 15 5 := by
  have hh : rawCoordinate 6 15 5=rawCoordinate 6 5 15 := by
    rw [rawCoordinate_sparse 6 15 5 rawEntry_6_05_15 rawEntry_6_15_05_data,rawCoordinate_sparse 6 5 15 rawEntry_6_05_15 rawEntry_6_05_15_data]
  rw [hh,rawEntry_6_05_15_physical]
  exact rawPlusPolynomial_symm 5 15
def rawEntry_6_06_06 : SparseEntry := [(22,1)]
theorem rawEntry_6_06_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 6=sparseCoefficient rawEntry_6_06_06 r := by decide +kernel
theorem rawEntry_6_06_06_coordinates : sparsePolynomial 1 rawEntry_6_06_06=rawPlusCoordinates 6 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_06_physical : invariantSubst (rawCoordinate 6 6 6)=rawPlusPolynomial 6 6 := by
  rw [rawCoordinate_sparse 6 6 6 rawEntry_6_06_06 rawEntry_6_06_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_06)=_
  rw [rawEntry_6_06_06_coordinates]
  exact rawPlus_subst 6 6
def rawEntry_6_06_07 : SparseEntry := [(27,1)]
theorem rawEntry_6_06_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 7=sparseCoefficient rawEntry_6_06_07 r := by decide +kernel
theorem rawEntry_6_06_07_coordinates : sparsePolynomial 1 rawEntry_6_06_07=rawPlusCoordinates 6 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_07_physical : invariantSubst (rawCoordinate 6 6 7)=rawPlusPolynomial 6 7 := by
  rw [rawCoordinate_sparse 6 6 7 rawEntry_6_06_07 rawEntry_6_06_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_07)=_
  rw [rawEntry_6_06_07_coordinates]
  exact rawPlus_subst 6 7
theorem rawEntry_6_07_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 6=sparseCoefficient rawEntry_6_06_07 r := by decide +kernel
theorem rawEntry_6_07_06_physical : invariantSubst (rawCoordinate 6 7 6)=rawPlusPolynomial 7 6 := by
  have hh : rawCoordinate 6 7 6=rawCoordinate 6 6 7 := by
    rw [rawCoordinate_sparse 6 7 6 rawEntry_6_06_07 rawEntry_6_07_06_data,rawCoordinate_sparse 6 6 7 rawEntry_6_06_07 rawEntry_6_06_07_data]
  rw [hh,rawEntry_6_06_07_physical]
  exact rawPlusPolynomial_symm 6 7
def rawEntry_6_06_08 : SparseEntry := [(28,1)]
theorem rawEntry_6_06_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 8=sparseCoefficient rawEntry_6_06_08 r := by decide +kernel
theorem rawEntry_6_06_08_coordinates : sparsePolynomial 1 rawEntry_6_06_08=rawPlusCoordinates 6 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_08_physical : invariantSubst (rawCoordinate 6 6 8)=rawPlusPolynomial 6 8 := by
  rw [rawCoordinate_sparse 6 6 8 rawEntry_6_06_08 rawEntry_6_06_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_08)=_
  rw [rawEntry_6_06_08_coordinates]
  exact rawPlus_subst 6 8
theorem rawEntry_6_08_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 6=sparseCoefficient rawEntry_6_06_08 r := by decide +kernel
theorem rawEntry_6_08_06_physical : invariantSubst (rawCoordinate 6 8 6)=rawPlusPolynomial 8 6 := by
  have hh : rawCoordinate 6 8 6=rawCoordinate 6 6 8 := by
    rw [rawCoordinate_sparse 6 8 6 rawEntry_6_06_08 rawEntry_6_08_06_data,rawCoordinate_sparse 6 6 8 rawEntry_6_06_08 rawEntry_6_06_08_data]
  rw [hh,rawEntry_6_06_08_physical]
  exact rawPlusPolynomial_symm 6 8
def rawEntry_6_06_09 : SparseEntry := [(29,1)]
theorem rawEntry_6_06_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 9=sparseCoefficient rawEntry_6_06_09 r := by decide +kernel
theorem rawEntry_6_06_09_coordinates : sparsePolynomial 1 rawEntry_6_06_09=rawPlusCoordinates 6 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_09_physical : invariantSubst (rawCoordinate 6 6 9)=rawPlusPolynomial 6 9 := by
  rw [rawCoordinate_sparse 6 6 9 rawEntry_6_06_09 rawEntry_6_06_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_09)=_
  rw [rawEntry_6_06_09_coordinates]
  exact rawPlus_subst 6 9
theorem rawEntry_6_09_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 6=sparseCoefficient rawEntry_6_06_09 r := by decide +kernel
theorem rawEntry_6_09_06_physical : invariantSubst (rawCoordinate 6 9 6)=rawPlusPolynomial 9 6 := by
  have hh : rawCoordinate 6 9 6=rawCoordinate 6 6 9 := by
    rw [rawCoordinate_sparse 6 9 6 rawEntry_6_06_09 rawEntry_6_09_06_data,rawCoordinate_sparse 6 6 9 rawEntry_6_06_09 rawEntry_6_06_09_data]
  rw [hh,rawEntry_6_06_09_physical]
  exact rawPlusPolynomial_symm 6 9
def rawEntry_6_06_10 : SparseEntry := [(30,1)]
theorem rawEntry_6_06_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 10=sparseCoefficient rawEntry_6_06_10 r := by decide +kernel
theorem rawEntry_6_06_10_coordinates : sparsePolynomial 1 rawEntry_6_06_10=rawPlusCoordinates 6 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_10_physical : invariantSubst (rawCoordinate 6 6 10)=rawPlusPolynomial 6 10 := by
  rw [rawCoordinate_sparse 6 6 10 rawEntry_6_06_10 rawEntry_6_06_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_10)=_
  rw [rawEntry_6_06_10_coordinates]
  exact rawPlus_subst 6 10
theorem rawEntry_6_10_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 6=sparseCoefficient rawEntry_6_06_10 r := by decide +kernel
theorem rawEntry_6_10_06_physical : invariantSubst (rawCoordinate 6 10 6)=rawPlusPolynomial 10 6 := by
  have hh : rawCoordinate 6 10 6=rawCoordinate 6 6 10 := by
    rw [rawCoordinate_sparse 6 10 6 rawEntry_6_06_10 rawEntry_6_10_06_data,rawCoordinate_sparse 6 6 10 rawEntry_6_06_10 rawEntry_6_06_10_data]
  rw [hh,rawEntry_6_06_10_physical]
  exact rawPlusPolynomial_symm 6 10
def rawEntry_6_06_11 : SparseEntry := [(36,1)]
theorem rawEntry_6_06_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 11=sparseCoefficient rawEntry_6_06_11 r := by decide +kernel
theorem rawEntry_6_06_11_coordinates : sparsePolynomial 1 rawEntry_6_06_11=rawPlusCoordinates 6 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_11_physical : invariantSubst (rawCoordinate 6 6 11)=rawPlusPolynomial 6 11 := by
  rw [rawCoordinate_sparse 6 6 11 rawEntry_6_06_11 rawEntry_6_06_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_11)=_
  rw [rawEntry_6_06_11_coordinates]
  exact rawPlus_subst 6 11
theorem rawEntry_6_11_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 6=sparseCoefficient rawEntry_6_06_11 r := by decide +kernel
theorem rawEntry_6_11_06_physical : invariantSubst (rawCoordinate 6 11 6)=rawPlusPolynomial 11 6 := by
  have hh : rawCoordinate 6 11 6=rawCoordinate 6 6 11 := by
    rw [rawCoordinate_sparse 6 11 6 rawEntry_6_06_11 rawEntry_6_11_06_data,rawCoordinate_sparse 6 6 11 rawEntry_6_06_11 rawEntry_6_06_11_data]
  rw [hh,rawEntry_6_06_11_physical]
  exact rawPlusPolynomial_symm 6 11
def rawEntry_6_06_12 : SparseEntry := [(37,1)]
theorem rawEntry_6_06_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 12=sparseCoefficient rawEntry_6_06_12 r := by decide +kernel
theorem rawEntry_6_06_12_coordinates : sparsePolynomial 1 rawEntry_6_06_12=rawPlusCoordinates 6 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_12_physical : invariantSubst (rawCoordinate 6 6 12)=rawPlusPolynomial 6 12 := by
  rw [rawCoordinate_sparse 6 6 12 rawEntry_6_06_12 rawEntry_6_06_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_12)=_
  rw [rawEntry_6_06_12_coordinates]
  exact rawPlus_subst 6 12
theorem rawEntry_6_12_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 6=sparseCoefficient rawEntry_6_06_12 r := by decide +kernel
theorem rawEntry_6_12_06_physical : invariantSubst (rawCoordinate 6 12 6)=rawPlusPolynomial 12 6 := by
  have hh : rawCoordinate 6 12 6=rawCoordinate 6 6 12 := by
    rw [rawCoordinate_sparse 6 12 6 rawEntry_6_06_12 rawEntry_6_12_06_data,rawCoordinate_sparse 6 6 12 rawEntry_6_06_12 rawEntry_6_06_12_data]
  rw [hh,rawEntry_6_06_12_physical]
  exact rawPlusPolynomial_symm 6 12
def rawEntry_6_06_13 : SparseEntry := [(38,1)]
theorem rawEntry_6_06_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 13=sparseCoefficient rawEntry_6_06_13 r := by decide +kernel
theorem rawEntry_6_06_13_coordinates : sparsePolynomial 1 rawEntry_6_06_13=rawPlusCoordinates 6 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_13_physical : invariantSubst (rawCoordinate 6 6 13)=rawPlusPolynomial 6 13 := by
  rw [rawCoordinate_sparse 6 6 13 rawEntry_6_06_13 rawEntry_6_06_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_13)=_
  rw [rawEntry_6_06_13_coordinates]
  exact rawPlus_subst 6 13
theorem rawEntry_6_13_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 6=sparseCoefficient rawEntry_6_06_13 r := by decide +kernel
theorem rawEntry_6_13_06_physical : invariantSubst (rawCoordinate 6 13 6)=rawPlusPolynomial 13 6 := by
  have hh : rawCoordinate 6 13 6=rawCoordinate 6 6 13 := by
    rw [rawCoordinate_sparse 6 13 6 rawEntry_6_06_13 rawEntry_6_13_06_data,rawCoordinate_sparse 6 6 13 rawEntry_6_06_13 rawEntry_6_06_13_data]
  rw [hh,rawEntry_6_06_13_physical]
  exact rawPlusPolynomial_symm 6 13
def rawEntry_6_06_14 : SparseEntry := [(39,1)]
theorem rawEntry_6_06_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 14=sparseCoefficient rawEntry_6_06_14 r := by decide +kernel
theorem rawEntry_6_06_14_coordinates : sparsePolynomial 1 rawEntry_6_06_14=rawPlusCoordinates 6 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_14_physical : invariantSubst (rawCoordinate 6 6 14)=rawPlusPolynomial 6 14 := by
  rw [rawCoordinate_sparse 6 6 14 rawEntry_6_06_14 rawEntry_6_06_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_14)=_
  rw [rawEntry_6_06_14_coordinates]
  exact rawPlus_subst 6 14
theorem rawEntry_6_14_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 6=sparseCoefficient rawEntry_6_06_14 r := by decide +kernel
theorem rawEntry_6_14_06_physical : invariantSubst (rawCoordinate 6 14 6)=rawPlusPolynomial 14 6 := by
  have hh : rawCoordinate 6 14 6=rawCoordinate 6 6 14 := by
    rw [rawCoordinate_sparse 6 14 6 rawEntry_6_06_14 rawEntry_6_14_06_data,rawCoordinate_sparse 6 6 14 rawEntry_6_06_14 rawEntry_6_06_14_data]
  rw [hh,rawEntry_6_06_14_physical]
  exact rawPlusPolynomial_symm 6 14
def rawEntry_6_06_15 : SparseEntry := [(40,1)]
theorem rawEntry_6_06_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 15=sparseCoefficient rawEntry_6_06_15 r := by decide +kernel
theorem rawEntry_6_06_15_coordinates : sparsePolynomial 1 rawEntry_6_06_15=rawPlusCoordinates 6 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_06_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_06_15_physical : invariantSubst (rawCoordinate 6 6 15)=rawPlusPolynomial 6 15 := by
  rw [rawCoordinate_sparse 6 6 15 rawEntry_6_06_15 rawEntry_6_06_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_06_15)=_
  rw [rawEntry_6_06_15_coordinates]
  exact rawPlus_subst 6 15
theorem rawEntry_6_15_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 6=sparseCoefficient rawEntry_6_06_15 r := by decide +kernel
theorem rawEntry_6_15_06_physical : invariantSubst (rawCoordinate 6 15 6)=rawPlusPolynomial 15 6 := by
  have hh : rawCoordinate 6 15 6=rawCoordinate 6 6 15 := by
    rw [rawCoordinate_sparse 6 15 6 rawEntry_6_06_15 rawEntry_6_15_06_data,rawCoordinate_sparse 6 6 15 rawEntry_6_06_15 rawEntry_6_06_15_data]
  rw [hh,rawEntry_6_06_15_physical]
  exact rawPlusPolynomial_symm 6 15
def rawEntry_6_07_07 : SparseEntry := [(32,1)]
theorem rawEntry_6_07_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 7=sparseCoefficient rawEntry_6_07_07 r := by decide +kernel
theorem rawEntry_6_07_07_coordinates : sparsePolynomial 1 rawEntry_6_07_07=rawPlusCoordinates 7 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_07_physical : invariantSubst (rawCoordinate 6 7 7)=rawPlusPolynomial 7 7 := by
  rw [rawCoordinate_sparse 6 7 7 rawEntry_6_07_07 rawEntry_6_07_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_07)=_
  rw [rawEntry_6_07_07_coordinates]
  exact rawPlus_subst 7 7
def rawEntry_6_07_08 : SparseEntry := [(33,1)]
theorem rawEntry_6_07_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 8=sparseCoefficient rawEntry_6_07_08 r := by decide +kernel
theorem rawEntry_6_07_08_coordinates : sparsePolynomial 1 rawEntry_6_07_08=rawPlusCoordinates 7 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_08_physical : invariantSubst (rawCoordinate 6 7 8)=rawPlusPolynomial 7 8 := by
  rw [rawCoordinate_sparse 6 7 8 rawEntry_6_07_08 rawEntry_6_07_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_08)=_
  rw [rawEntry_6_07_08_coordinates]
  exact rawPlus_subst 7 8
theorem rawEntry_6_08_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 7=sparseCoefficient rawEntry_6_07_08 r := by decide +kernel
theorem rawEntry_6_08_07_physical : invariantSubst (rawCoordinate 6 8 7)=rawPlusPolynomial 8 7 := by
  have hh : rawCoordinate 6 8 7=rawCoordinate 6 7 8 := by
    rw [rawCoordinate_sparse 6 8 7 rawEntry_6_07_08 rawEntry_6_08_07_data,rawCoordinate_sparse 6 7 8 rawEntry_6_07_08 rawEntry_6_07_08_data]
  rw [hh,rawEntry_6_07_08_physical]
  exact rawPlusPolynomial_symm 7 8
def rawEntry_6_07_09 : SparseEntry := [(35,1)]
theorem rawEntry_6_07_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 9=sparseCoefficient rawEntry_6_07_09 r := by decide +kernel
theorem rawEntry_6_07_09_coordinates : sparsePolynomial 1 rawEntry_6_07_09=rawPlusCoordinates 7 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_09_physical : invariantSubst (rawCoordinate 6 7 9)=rawPlusPolynomial 7 9 := by
  rw [rawCoordinate_sparse 6 7 9 rawEntry_6_07_09 rawEntry_6_07_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_09)=_
  rw [rawEntry_6_07_09_coordinates]
  exact rawPlus_subst 7 9
theorem rawEntry_6_09_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 7=sparseCoefficient rawEntry_6_07_09 r := by decide +kernel
theorem rawEntry_6_09_07_physical : invariantSubst (rawCoordinate 6 9 7)=rawPlusPolynomial 9 7 := by
  have hh : rawCoordinate 6 9 7=rawCoordinate 6 7 9 := by
    rw [rawCoordinate_sparse 6 9 7 rawEntry_6_07_09 rawEntry_6_09_07_data,rawCoordinate_sparse 6 7 9 rawEntry_6_07_09 rawEntry_6_07_09_data]
  rw [hh,rawEntry_6_07_09_physical]
  exact rawPlusPolynomial_symm 7 9
def rawEntry_6_07_10 : SparseEntry := [(37,1)]
theorem rawEntry_6_07_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 10=sparseCoefficient rawEntry_6_07_10 r := by decide +kernel
theorem rawEntry_6_07_10_coordinates : sparsePolynomial 1 rawEntry_6_07_10=rawPlusCoordinates 7 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_10_physical : invariantSubst (rawCoordinate 6 7 10)=rawPlusPolynomial 7 10 := by
  rw [rawCoordinate_sparse 6 7 10 rawEntry_6_07_10 rawEntry_6_07_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_10)=_
  rw [rawEntry_6_07_10_coordinates]
  exact rawPlus_subst 7 10
theorem rawEntry_6_10_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 7=sparseCoefficient rawEntry_6_07_10 r := by decide +kernel
theorem rawEntry_6_10_07_physical : invariantSubst (rawCoordinate 6 10 7)=rawPlusPolynomial 10 7 := by
  have hh : rawCoordinate 6 10 7=rawCoordinate 6 7 10 := by
    rw [rawCoordinate_sparse 6 10 7 rawEntry_6_07_10 rawEntry_6_10_07_data,rawCoordinate_sparse 6 7 10 rawEntry_6_07_10 rawEntry_6_07_10_data]
  rw [hh,rawEntry_6_07_10_physical]
  exact rawPlusPolynomial_symm 7 10
def rawEntry_6_07_11 : SparseEntry := [(42,1)]
theorem rawEntry_6_07_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 11=sparseCoefficient rawEntry_6_07_11 r := by decide +kernel
theorem rawEntry_6_07_11_coordinates : sparsePolynomial 1 rawEntry_6_07_11=rawPlusCoordinates 7 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_11_physical : invariantSubst (rawCoordinate 6 7 11)=rawPlusPolynomial 7 11 := by
  rw [rawCoordinate_sparse 6 7 11 rawEntry_6_07_11 rawEntry_6_07_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_11)=_
  rw [rawEntry_6_07_11_coordinates]
  exact rawPlus_subst 7 11
theorem rawEntry_6_11_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 7=sparseCoefficient rawEntry_6_07_11 r := by decide +kernel
theorem rawEntry_6_11_07_physical : invariantSubst (rawCoordinate 6 11 7)=rawPlusPolynomial 11 7 := by
  have hh : rawCoordinate 6 11 7=rawCoordinate 6 7 11 := by
    rw [rawCoordinate_sparse 6 11 7 rawEntry_6_07_11 rawEntry_6_11_07_data,rawCoordinate_sparse 6 7 11 rawEntry_6_07_11 rawEntry_6_07_11_data]
  rw [hh,rawEntry_6_07_11_physical]
  exact rawPlusPolynomial_symm 7 11
def rawEntry_6_07_12 : SparseEntry := [(44,1)]
theorem rawEntry_6_07_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 12=sparseCoefficient rawEntry_6_07_12 r := by decide +kernel
theorem rawEntry_6_07_12_coordinates : sparsePolynomial 1 rawEntry_6_07_12=rawPlusCoordinates 7 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_12_physical : invariantSubst (rawCoordinate 6 7 12)=rawPlusPolynomial 7 12 := by
  rw [rawCoordinate_sparse 6 7 12 rawEntry_6_07_12 rawEntry_6_07_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_12)=_
  rw [rawEntry_6_07_12_coordinates]
  exact rawPlus_subst 7 12
theorem rawEntry_6_12_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 7=sparseCoefficient rawEntry_6_07_12 r := by decide +kernel
theorem rawEntry_6_12_07_physical : invariantSubst (rawCoordinate 6 12 7)=rawPlusPolynomial 12 7 := by
  have hh : rawCoordinate 6 12 7=rawCoordinate 6 7 12 := by
    rw [rawCoordinate_sparse 6 12 7 rawEntry_6_07_12 rawEntry_6_12_07_data,rawCoordinate_sparse 6 7 12 rawEntry_6_07_12 rawEntry_6_07_12_data]
  rw [hh,rawEntry_6_07_12_physical]
  exact rawPlusPolynomial_symm 7 12
def rawEntry_6_07_13 : SparseEntry := [(45,1)]
theorem rawEntry_6_07_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 13=sparseCoefficient rawEntry_6_07_13 r := by decide +kernel
theorem rawEntry_6_07_13_coordinates : sparsePolynomial 1 rawEntry_6_07_13=rawPlusCoordinates 7 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_13_physical : invariantSubst (rawCoordinate 6 7 13)=rawPlusPolynomial 7 13 := by
  rw [rawCoordinate_sparse 6 7 13 rawEntry_6_07_13 rawEntry_6_07_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_13)=_
  rw [rawEntry_6_07_13_coordinates]
  exact rawPlus_subst 7 13
theorem rawEntry_6_13_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 7=sparseCoefficient rawEntry_6_07_13 r := by decide +kernel
theorem rawEntry_6_13_07_physical : invariantSubst (rawCoordinate 6 13 7)=rawPlusPolynomial 13 7 := by
  have hh : rawCoordinate 6 13 7=rawCoordinate 6 7 13 := by
    rw [rawCoordinate_sparse 6 13 7 rawEntry_6_07_13 rawEntry_6_13_07_data,rawCoordinate_sparse 6 7 13 rawEntry_6_07_13 rawEntry_6_07_13_data]
  rw [hh,rawEntry_6_07_13_physical]
  exact rawPlusPolynomial_symm 7 13
def rawEntry_6_07_14 : SparseEntry := [(47,1)]
theorem rawEntry_6_07_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 14=sparseCoefficient rawEntry_6_07_14 r := by decide +kernel
theorem rawEntry_6_07_14_coordinates : sparsePolynomial 1 rawEntry_6_07_14=rawPlusCoordinates 7 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_14_physical : invariantSubst (rawCoordinate 6 7 14)=rawPlusPolynomial 7 14 := by
  rw [rawCoordinate_sparse 6 7 14 rawEntry_6_07_14 rawEntry_6_07_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_14)=_
  rw [rawEntry_6_07_14_coordinates]
  exact rawPlus_subst 7 14
theorem rawEntry_6_14_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 7=sparseCoefficient rawEntry_6_07_14 r := by decide +kernel
theorem rawEntry_6_14_07_physical : invariantSubst (rawCoordinate 6 14 7)=rawPlusPolynomial 14 7 := by
  have hh : rawCoordinate 6 14 7=rawCoordinate 6 7 14 := by
    rw [rawCoordinate_sparse 6 14 7 rawEntry_6_07_14 rawEntry_6_14_07_data,rawCoordinate_sparse 6 7 14 rawEntry_6_07_14 rawEntry_6_07_14_data]
  rw [hh,rawEntry_6_07_14_physical]
  exact rawPlusPolynomial_symm 7 14
def rawEntry_6_07_15 : SparseEntry := [(49,1)]
theorem rawEntry_6_07_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 15=sparseCoefficient rawEntry_6_07_15 r := by decide +kernel
theorem rawEntry_6_07_15_coordinates : sparsePolynomial 1 rawEntry_6_07_15=rawPlusCoordinates 7 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_07_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_07_15_physical : invariantSubst (rawCoordinate 6 7 15)=rawPlusPolynomial 7 15 := by
  rw [rawCoordinate_sparse 6 7 15 rawEntry_6_07_15 rawEntry_6_07_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_07_15)=_
  rw [rawEntry_6_07_15_coordinates]
  exact rawPlus_subst 7 15
theorem rawEntry_6_15_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 7=sparseCoefficient rawEntry_6_07_15 r := by decide +kernel
theorem rawEntry_6_15_07_physical : invariantSubst (rawCoordinate 6 15 7)=rawPlusPolynomial 15 7 := by
  have hh : rawCoordinate 6 15 7=rawCoordinate 6 7 15 := by
    rw [rawCoordinate_sparse 6 15 7 rawEntry_6_07_15 rawEntry_6_15_07_data,rawCoordinate_sparse 6 7 15 rawEntry_6_07_15 rawEntry_6_07_15_data]
  rw [hh,rawEntry_6_07_15_physical]
  exact rawPlusPolynomial_symm 7 15
end ThomsonNegative.Certificate.Bridges
