import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_04_06 : SparseEntry := [(20,1)]
theorem rawEntry_6_04_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 6=sparseCoefficient rawEntry_6_04_06 r := by decide +kernel
theorem rawEntry_6_04_06_coordinates : sparsePolynomial 1 rawEntry_6_04_06=rawPlusCoordinates 4 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_06_physical : invariantSubst (rawCoordinate 6 4 6)=rawPlusPolynomial 4 6 := by
  rw [rawCoordinate_sparse 6 4 6 rawEntry_6_04_06 rawEntry_6_04_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_06)=_
  rw [rawEntry_6_04_06_coordinates]
  exact rawPlus_subst 4 6
theorem rawEntry_6_06_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 4=sparseCoefficient rawEntry_6_04_06 r := by decide +kernel
theorem rawEntry_6_06_04_physical : invariantSubst (rawCoordinate 6 6 4)=rawPlusPolynomial 6 4 := by
  have hh : rawCoordinate 6 6 4=rawCoordinate 6 4 6 := by
    rw [rawCoordinate_sparse 6 6 4 rawEntry_6_04_06 rawEntry_6_06_04_data,rawCoordinate_sparse 6 4 6 rawEntry_6_04_06 rawEntry_6_04_06_data]
  rw [hh,rawEntry_6_04_06_physical]
  exact rawPlusPolynomial_symm 4 6
def rawEntry_6_04_07 : SparseEntry := [(23,1)]
theorem rawEntry_6_04_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 7=sparseCoefficient rawEntry_6_04_07 r := by decide +kernel
theorem rawEntry_6_04_07_coordinates : sparsePolynomial 1 rawEntry_6_04_07=rawPlusCoordinates 4 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_07_physical : invariantSubst (rawCoordinate 6 4 7)=rawPlusPolynomial 4 7 := by
  rw [rawCoordinate_sparse 6 4 7 rawEntry_6_04_07 rawEntry_6_04_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_07)=_
  rw [rawEntry_6_04_07_coordinates]
  exact rawPlus_subst 4 7
theorem rawEntry_6_07_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 4=sparseCoefficient rawEntry_6_04_07 r := by decide +kernel
theorem rawEntry_6_07_04_physical : invariantSubst (rawCoordinate 6 7 4)=rawPlusPolynomial 7 4 := by
  have hh : rawCoordinate 6 7 4=rawCoordinate 6 4 7 := by
    rw [rawCoordinate_sparse 6 7 4 rawEntry_6_04_07 rawEntry_6_07_04_data,rawCoordinate_sparse 6 4 7 rawEntry_6_04_07 rawEntry_6_04_07_data]
  rw [hh,rawEntry_6_04_07_physical]
  exact rawPlusPolynomial_symm 4 7
def rawEntry_6_04_08 : SparseEntry := [(24,1)]
theorem rawEntry_6_04_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 8=sparseCoefficient rawEntry_6_04_08 r := by decide +kernel
theorem rawEntry_6_04_08_coordinates : sparsePolynomial 1 rawEntry_6_04_08=rawPlusCoordinates 4 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_08_physical : invariantSubst (rawCoordinate 6 4 8)=rawPlusPolynomial 4 8 := by
  rw [rawCoordinate_sparse 6 4 8 rawEntry_6_04_08 rawEntry_6_04_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_08)=_
  rw [rawEntry_6_04_08_coordinates]
  exact rawPlus_subst 4 8
theorem rawEntry_6_08_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 4=sparseCoefficient rawEntry_6_04_08 r := by decide +kernel
theorem rawEntry_6_08_04_physical : invariantSubst (rawCoordinate 6 8 4)=rawPlusPolynomial 8 4 := by
  have hh : rawCoordinate 6 8 4=rawCoordinate 6 4 8 := by
    rw [rawCoordinate_sparse 6 8 4 rawEntry_6_04_08 rawEntry_6_08_04_data,rawCoordinate_sparse 6 4 8 rawEntry_6_04_08 rawEntry_6_04_08_data]
  rw [hh,rawEntry_6_04_08_physical]
  exact rawPlusPolynomial_symm 4 8
def rawEntry_6_04_09 : SparseEntry := [(26,1)]
theorem rawEntry_6_04_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 9=sparseCoefficient rawEntry_6_04_09 r := by decide +kernel
theorem rawEntry_6_04_09_coordinates : sparsePolynomial 1 rawEntry_6_04_09=rawPlusCoordinates 4 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_09_physical : invariantSubst (rawCoordinate 6 4 9)=rawPlusPolynomial 4 9 := by
  rw [rawCoordinate_sparse 6 4 9 rawEntry_6_04_09 rawEntry_6_04_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_09)=_
  rw [rawEntry_6_04_09_coordinates]
  exact rawPlus_subst 4 9
theorem rawEntry_6_09_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 4=sparseCoefficient rawEntry_6_04_09 r := by decide +kernel
theorem rawEntry_6_09_04_physical : invariantSubst (rawCoordinate 6 9 4)=rawPlusPolynomial 9 4 := by
  have hh : rawCoordinate 6 9 4=rawCoordinate 6 4 9 := by
    rw [rawCoordinate_sparse 6 9 4 rawEntry_6_04_09 rawEntry_6_09_04_data,rawCoordinate_sparse 6 4 9 rawEntry_6_04_09 rawEntry_6_04_09_data]
  rw [hh,rawEntry_6_04_09_physical]
  exact rawPlusPolynomial_symm 4 9
def rawEntry_6_04_10 : SparseEntry := [(28,1)]
theorem rawEntry_6_04_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 10=sparseCoefficient rawEntry_6_04_10 r := by decide +kernel
theorem rawEntry_6_04_10_coordinates : sparsePolynomial 1 rawEntry_6_04_10=rawPlusCoordinates 4 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_10_physical : invariantSubst (rawCoordinate 6 4 10)=rawPlusPolynomial 4 10 := by
  rw [rawCoordinate_sparse 6 4 10 rawEntry_6_04_10 rawEntry_6_04_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_10)=_
  rw [rawEntry_6_04_10_coordinates]
  exact rawPlus_subst 4 10
theorem rawEntry_6_10_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 4=sparseCoefficient rawEntry_6_04_10 r := by decide +kernel
theorem rawEntry_6_10_04_physical : invariantSubst (rawCoordinate 6 10 4)=rawPlusPolynomial 10 4 := by
  have hh : rawCoordinate 6 10 4=rawCoordinate 6 4 10 := by
    rw [rawCoordinate_sparse 6 10 4 rawEntry_6_04_10 rawEntry_6_10_04_data,rawCoordinate_sparse 6 4 10 rawEntry_6_04_10 rawEntry_6_04_10_data]
  rw [hh,rawEntry_6_04_10_physical]
  exact rawPlusPolynomial_symm 4 10
def rawEntry_6_04_11 : SparseEntry := [(31,1)]
theorem rawEntry_6_04_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 11=sparseCoefficient rawEntry_6_04_11 r := by decide +kernel
theorem rawEntry_6_04_11_coordinates : sparsePolynomial 1 rawEntry_6_04_11=rawPlusCoordinates 4 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_11_physical : invariantSubst (rawCoordinate 6 4 11)=rawPlusPolynomial 4 11 := by
  rw [rawCoordinate_sparse 6 4 11 rawEntry_6_04_11 rawEntry_6_04_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_11)=_
  rw [rawEntry_6_04_11_coordinates]
  exact rawPlus_subst 4 11
theorem rawEntry_6_11_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 4=sparseCoefficient rawEntry_6_04_11 r := by decide +kernel
theorem rawEntry_6_11_04_physical : invariantSubst (rawCoordinate 6 11 4)=rawPlusPolynomial 11 4 := by
  have hh : rawCoordinate 6 11 4=rawCoordinate 6 4 11 := by
    rw [rawCoordinate_sparse 6 11 4 rawEntry_6_04_11 rawEntry_6_11_04_data,rawCoordinate_sparse 6 4 11 rawEntry_6_04_11 rawEntry_6_04_11_data]
  rw [hh,rawEntry_6_04_11_physical]
  exact rawPlusPolynomial_symm 4 11
def rawEntry_6_04_12 : SparseEntry := [(33,1)]
theorem rawEntry_6_04_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 12=sparseCoefficient rawEntry_6_04_12 r := by decide +kernel
theorem rawEntry_6_04_12_coordinates : sparsePolynomial 1 rawEntry_6_04_12=rawPlusCoordinates 4 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_12_physical : invariantSubst (rawCoordinate 6 4 12)=rawPlusPolynomial 4 12 := by
  rw [rawCoordinate_sparse 6 4 12 rawEntry_6_04_12 rawEntry_6_04_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_12)=_
  rw [rawEntry_6_04_12_coordinates]
  exact rawPlus_subst 4 12
theorem rawEntry_6_12_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 4=sparseCoefficient rawEntry_6_04_12 r := by decide +kernel
theorem rawEntry_6_12_04_physical : invariantSubst (rawCoordinate 6 12 4)=rawPlusPolynomial 12 4 := by
  have hh : rawCoordinate 6 12 4=rawCoordinate 6 4 12 := by
    rw [rawCoordinate_sparse 6 12 4 rawEntry_6_04_12 rawEntry_6_12_04_data,rawCoordinate_sparse 6 4 12 rawEntry_6_04_12 rawEntry_6_04_12_data]
  rw [hh,rawEntry_6_04_12_physical]
  exact rawPlusPolynomial_symm 4 12
def rawEntry_6_04_13 : SparseEntry := [(34,1)]
theorem rawEntry_6_04_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 13=sparseCoefficient rawEntry_6_04_13 r := by decide +kernel
theorem rawEntry_6_04_13_coordinates : sparsePolynomial 1 rawEntry_6_04_13=rawPlusCoordinates 4 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_13_physical : invariantSubst (rawCoordinate 6 4 13)=rawPlusPolynomial 4 13 := by
  rw [rawCoordinate_sparse 6 4 13 rawEntry_6_04_13 rawEntry_6_04_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_13)=_
  rw [rawEntry_6_04_13_coordinates]
  exact rawPlus_subst 4 13
theorem rawEntry_6_13_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 4=sparseCoefficient rawEntry_6_04_13 r := by decide +kernel
theorem rawEntry_6_13_04_physical : invariantSubst (rawCoordinate 6 13 4)=rawPlusPolynomial 13 4 := by
  have hh : rawCoordinate 6 13 4=rawCoordinate 6 4 13 := by
    rw [rawCoordinate_sparse 6 13 4 rawEntry_6_04_13 rawEntry_6_13_04_data,rawCoordinate_sparse 6 4 13 rawEntry_6_04_13 rawEntry_6_04_13_data]
  rw [hh,rawEntry_6_04_13_physical]
  exact rawPlusPolynomial_symm 4 13
def rawEntry_6_04_14 : SparseEntry := [(36,1)]
theorem rawEntry_6_04_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 14=sparseCoefficient rawEntry_6_04_14 r := by decide +kernel
theorem rawEntry_6_04_14_coordinates : sparsePolynomial 1 rawEntry_6_04_14=rawPlusCoordinates 4 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_14_physical : invariantSubst (rawCoordinate 6 4 14)=rawPlusPolynomial 4 14 := by
  rw [rawCoordinate_sparse 6 4 14 rawEntry_6_04_14 rawEntry_6_04_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_14)=_
  rw [rawEntry_6_04_14_coordinates]
  exact rawPlus_subst 4 14
theorem rawEntry_6_14_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 4=sparseCoefficient rawEntry_6_04_14 r := by decide +kernel
theorem rawEntry_6_14_04_physical : invariantSubst (rawCoordinate 6 14 4)=rawPlusPolynomial 14 4 := by
  have hh : rawCoordinate 6 14 4=rawCoordinate 6 4 14 := by
    rw [rawCoordinate_sparse 6 14 4 rawEntry_6_04_14 rawEntry_6_14_04_data,rawCoordinate_sparse 6 4 14 rawEntry_6_04_14 rawEntry_6_04_14_data]
  rw [hh,rawEntry_6_04_14_physical]
  exact rawPlusPolynomial_symm 4 14
def rawEntry_6_04_15 : SparseEntry := [(38,1)]
theorem rawEntry_6_04_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 15=sparseCoefficient rawEntry_6_04_15 r := by decide +kernel
theorem rawEntry_6_04_15_coordinates : sparsePolynomial 1 rawEntry_6_04_15=rawPlusCoordinates 4 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_15_physical : invariantSubst (rawCoordinate 6 4 15)=rawPlusPolynomial 4 15 := by
  rw [rawCoordinate_sparse 6 4 15 rawEntry_6_04_15 rawEntry_6_04_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_15)=_
  rw [rawEntry_6_04_15_coordinates]
  exact rawPlus_subst 4 15
theorem rawEntry_6_15_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 4=sparseCoefficient rawEntry_6_04_15 r := by decide +kernel
theorem rawEntry_6_15_04_physical : invariantSubst (rawCoordinate 6 15 4)=rawPlusPolynomial 15 4 := by
  have hh : rawCoordinate 6 15 4=rawCoordinate 6 4 15 := by
    rw [rawCoordinate_sparse 6 15 4 rawEntry_6_04_15 rawEntry_6_15_04_data,rawCoordinate_sparse 6 4 15 rawEntry_6_04_15 rawEntry_6_04_15_data]
  rw [hh,rawEntry_6_04_15_physical]
  exact rawPlusPolynomial_symm 4 15
def rawEntry_6_05_05 : SparseEntry := [(19,1)]
theorem rawEntry_6_05_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 5=sparseCoefficient rawEntry_6_05_05 r := by decide +kernel
theorem rawEntry_6_05_05_coordinates : sparsePolynomial 1 rawEntry_6_05_05=rawPlusCoordinates 5 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_05_physical : invariantSubst (rawCoordinate 6 5 5)=rawPlusPolynomial 5 5 := by
  rw [rawCoordinate_sparse 6 5 5 rawEntry_6_05_05 rawEntry_6_05_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_05)=_
  rw [rawEntry_6_05_05_coordinates]
  exact rawPlus_subst 5 5
def rawEntry_6_05_06 : SparseEntry := [(21,1)]
theorem rawEntry_6_05_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 6=sparseCoefficient rawEntry_6_05_06 r := by decide +kernel
theorem rawEntry_6_05_06_coordinates : sparsePolynomial 1 rawEntry_6_05_06=rawPlusCoordinates 5 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_06_physical : invariantSubst (rawCoordinate 6 5 6)=rawPlusPolynomial 5 6 := by
  rw [rawCoordinate_sparse 6 5 6 rawEntry_6_05_06 rawEntry_6_05_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_06)=_
  rw [rawEntry_6_05_06_coordinates]
  exact rawPlus_subst 5 6
theorem rawEntry_6_06_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 5=sparseCoefficient rawEntry_6_05_06 r := by decide +kernel
theorem rawEntry_6_06_05_physical : invariantSubst (rawCoordinate 6 6 5)=rawPlusPolynomial 6 5 := by
  have hh : rawCoordinate 6 6 5=rawCoordinate 6 5 6 := by
    rw [rawCoordinate_sparse 6 6 5 rawEntry_6_05_06 rawEntry_6_06_05_data,rawCoordinate_sparse 6 5 6 rawEntry_6_05_06 rawEntry_6_05_06_data]
  rw [hh,rawEntry_6_05_06_physical]
  exact rawPlusPolynomial_symm 5 6
def rawEntry_6_05_07 : SparseEntry := [(25,1)]
theorem rawEntry_6_05_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 7=sparseCoefficient rawEntry_6_05_07 r := by decide +kernel
theorem rawEntry_6_05_07_coordinates : sparsePolynomial 1 rawEntry_6_05_07=rawPlusCoordinates 5 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_07_physical : invariantSubst (rawCoordinate 6 5 7)=rawPlusPolynomial 5 7 := by
  rw [rawCoordinate_sparse 6 5 7 rawEntry_6_05_07 rawEntry_6_05_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_07)=_
  rw [rawEntry_6_05_07_coordinates]
  exact rawPlus_subst 5 7
theorem rawEntry_6_07_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 5=sparseCoefficient rawEntry_6_05_07 r := by decide +kernel
theorem rawEntry_6_07_05_physical : invariantSubst (rawCoordinate 6 7 5)=rawPlusPolynomial 7 5 := by
  have hh : rawCoordinate 6 7 5=rawCoordinate 6 5 7 := by
    rw [rawCoordinate_sparse 6 7 5 rawEntry_6_05_07 rawEntry_6_07_05_data,rawCoordinate_sparse 6 5 7 rawEntry_6_05_07 rawEntry_6_05_07_data]
  rw [hh,rawEntry_6_05_07_physical]
  exact rawPlusPolynomial_symm 5 7
def rawEntry_6_05_08 : SparseEntry := [(26,1)]
theorem rawEntry_6_05_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 8=sparseCoefficient rawEntry_6_05_08 r := by decide +kernel
theorem rawEntry_6_05_08_coordinates : sparsePolynomial 1 rawEntry_6_05_08=rawPlusCoordinates 5 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_08_physical : invariantSubst (rawCoordinate 6 5 8)=rawPlusPolynomial 5 8 := by
  rw [rawCoordinate_sparse 6 5 8 rawEntry_6_05_08 rawEntry_6_05_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_08)=_
  rw [rawEntry_6_05_08_coordinates]
  exact rawPlus_subst 5 8
theorem rawEntry_6_08_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 5=sparseCoefficient rawEntry_6_05_08 r := by decide +kernel
theorem rawEntry_6_08_05_physical : invariantSubst (rawCoordinate 6 8 5)=rawPlusPolynomial 8 5 := by
  have hh : rawCoordinate 6 8 5=rawCoordinate 6 5 8 := by
    rw [rawCoordinate_sparse 6 8 5 rawEntry_6_05_08 rawEntry_6_08_05_data,rawCoordinate_sparse 6 5 8 rawEntry_6_05_08 rawEntry_6_05_08_data]
  rw [hh,rawEntry_6_05_08_physical]
  exact rawPlusPolynomial_symm 5 8
def rawEntry_6_05_09 : SparseEntry := [(27,1)]
theorem rawEntry_6_05_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 9=sparseCoefficient rawEntry_6_05_09 r := by decide +kernel
theorem rawEntry_6_05_09_coordinates : sparsePolynomial 1 rawEntry_6_05_09=rawPlusCoordinates 5 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_09_physical : invariantSubst (rawCoordinate 6 5 9)=rawPlusPolynomial 5 9 := by
  rw [rawCoordinate_sparse 6 5 9 rawEntry_6_05_09 rawEntry_6_05_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_09)=_
  rw [rawEntry_6_05_09_coordinates]
  exact rawPlus_subst 5 9
theorem rawEntry_6_09_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 5=sparseCoefficient rawEntry_6_05_09 r := by decide +kernel
theorem rawEntry_6_09_05_physical : invariantSubst (rawCoordinate 6 9 5)=rawPlusPolynomial 9 5 := by
  have hh : rawCoordinate 6 9 5=rawCoordinate 6 5 9 := by
    rw [rawCoordinate_sparse 6 9 5 rawEntry_6_05_09 rawEntry_6_09_05_data,rawCoordinate_sparse 6 5 9 rawEntry_6_05_09 rawEntry_6_05_09_data]
  rw [hh,rawEntry_6_05_09_physical]
  exact rawPlusPolynomial_symm 5 9
def rawEntry_6_05_10 : SparseEntry := [(29,1)]
theorem rawEntry_6_05_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 10=sparseCoefficient rawEntry_6_05_10 r := by decide +kernel
theorem rawEntry_6_05_10_coordinates : sparsePolynomial 1 rawEntry_6_05_10=rawPlusCoordinates 5 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_10_physical : invariantSubst (rawCoordinate 6 5 10)=rawPlusPolynomial 5 10 := by
  rw [rawCoordinate_sparse 6 5 10 rawEntry_6_05_10 rawEntry_6_05_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_10)=_
  rw [rawEntry_6_05_10_coordinates]
  exact rawPlus_subst 5 10
theorem rawEntry_6_10_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 5=sparseCoefficient rawEntry_6_05_10 r := by decide +kernel
theorem rawEntry_6_10_05_physical : invariantSubst (rawCoordinate 6 10 5)=rawPlusPolynomial 10 5 := by
  have hh : rawCoordinate 6 10 5=rawCoordinate 6 5 10 := by
    rw [rawCoordinate_sparse 6 10 5 rawEntry_6_05_10 rawEntry_6_10_05_data,rawCoordinate_sparse 6 5 10 rawEntry_6_05_10 rawEntry_6_05_10_data]
  rw [hh,rawEntry_6_05_10_physical]
  exact rawPlusPolynomial_symm 5 10
def rawEntry_6_05_11 : SparseEntry := [(33,1)]
theorem rawEntry_6_05_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 11=sparseCoefficient rawEntry_6_05_11 r := by decide +kernel
theorem rawEntry_6_05_11_coordinates : sparsePolynomial 1 rawEntry_6_05_11=rawPlusCoordinates 5 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_11_physical : invariantSubst (rawCoordinate 6 5 11)=rawPlusPolynomial 5 11 := by
  rw [rawCoordinate_sparse 6 5 11 rawEntry_6_05_11 rawEntry_6_05_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_11)=_
  rw [rawEntry_6_05_11_coordinates]
  exact rawPlus_subst 5 11
theorem rawEntry_6_11_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 5=sparseCoefficient rawEntry_6_05_11 r := by decide +kernel
theorem rawEntry_6_11_05_physical : invariantSubst (rawCoordinate 6 11 5)=rawPlusPolynomial 11 5 := by
  have hh : rawCoordinate 6 11 5=rawCoordinate 6 5 11 := by
    rw [rawCoordinate_sparse 6 11 5 rawEntry_6_05_11 rawEntry_6_11_05_data,rawCoordinate_sparse 6 5 11 rawEntry_6_05_11 rawEntry_6_05_11_data]
  rw [hh,rawEntry_6_05_11_physical]
  exact rawPlusPolynomial_symm 5 11
def rawEntry_6_05_12 : SparseEntry := [(35,1)]
theorem rawEntry_6_05_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 12=sparseCoefficient rawEntry_6_05_12 r := by decide +kernel
theorem rawEntry_6_05_12_coordinates : sparsePolynomial 1 rawEntry_6_05_12=rawPlusCoordinates 5 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_12_physical : invariantSubst (rawCoordinate 6 5 12)=rawPlusPolynomial 5 12 := by
  rw [rawCoordinate_sparse 6 5 12 rawEntry_6_05_12 rawEntry_6_05_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_12)=_
  rw [rawEntry_6_05_12_coordinates]
  exact rawPlus_subst 5 12
theorem rawEntry_6_12_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 5=sparseCoefficient rawEntry_6_05_12 r := by decide +kernel
theorem rawEntry_6_12_05_physical : invariantSubst (rawCoordinate 6 12 5)=rawPlusPolynomial 12 5 := by
  have hh : rawCoordinate 6 12 5=rawCoordinate 6 5 12 := by
    rw [rawCoordinate_sparse 6 12 5 rawEntry_6_05_12 rawEntry_6_12_05_data,rawCoordinate_sparse 6 5 12 rawEntry_6_05_12 rawEntry_6_05_12_data]
  rw [hh,rawEntry_6_05_12_physical]
  exact rawPlusPolynomial_symm 5 12
def rawEntry_6_05_13 : SparseEntry := [(36,1)]
theorem rawEntry_6_05_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 13=sparseCoefficient rawEntry_6_05_13 r := by decide +kernel
theorem rawEntry_6_05_13_coordinates : sparsePolynomial 1 rawEntry_6_05_13=rawPlusCoordinates 5 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_13_physical : invariantSubst (rawCoordinate 6 5 13)=rawPlusPolynomial 5 13 := by
  rw [rawCoordinate_sparse 6 5 13 rawEntry_6_05_13 rawEntry_6_05_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_13)=_
  rw [rawEntry_6_05_13_coordinates]
  exact rawPlus_subst 5 13
theorem rawEntry_6_13_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 5=sparseCoefficient rawEntry_6_05_13 r := by decide +kernel
theorem rawEntry_6_13_05_physical : invariantSubst (rawCoordinate 6 13 5)=rawPlusPolynomial 13 5 := by
  have hh : rawCoordinate 6 13 5=rawCoordinate 6 5 13 := by
    rw [rawCoordinate_sparse 6 13 5 rawEntry_6_05_13 rawEntry_6_13_05_data,rawCoordinate_sparse 6 5 13 rawEntry_6_05_13 rawEntry_6_05_13_data]
  rw [hh,rawEntry_6_05_13_physical]
  exact rawPlusPolynomial_symm 5 13
def rawEntry_6_05_14 : SparseEntry := [(37,1)]
theorem rawEntry_6_05_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 14=sparseCoefficient rawEntry_6_05_14 r := by decide +kernel
theorem rawEntry_6_05_14_coordinates : sparsePolynomial 1 rawEntry_6_05_14=rawPlusCoordinates 5 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_05_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_05_14_physical : invariantSubst (rawCoordinate 6 5 14)=rawPlusPolynomial 5 14 := by
  rw [rawCoordinate_sparse 6 5 14 rawEntry_6_05_14 rawEntry_6_05_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_05_14)=_
  rw [rawEntry_6_05_14_coordinates]
  exact rawPlus_subst 5 14
theorem rawEntry_6_14_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 5=sparseCoefficient rawEntry_6_05_14 r := by decide +kernel
theorem rawEntry_6_14_05_physical : invariantSubst (rawCoordinate 6 14 5)=rawPlusPolynomial 14 5 := by
  have hh : rawCoordinate 6 14 5=rawCoordinate 6 5 14 := by
    rw [rawCoordinate_sparse 6 14 5 rawEntry_6_05_14 rawEntry_6_14_05_data,rawCoordinate_sparse 6 5 14 rawEntry_6_05_14 rawEntry_6_05_14_data]
  rw [hh,rawEntry_6_05_14_physical]
  exact rawPlusPolynomial_symm 5 14
end ThomsonNegative.Certificate.Bridges
