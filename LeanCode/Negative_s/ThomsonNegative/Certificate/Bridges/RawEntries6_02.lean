import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_02_11 : SparseEntry := [(23,1)]
theorem rawEntry_6_02_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 11=sparseCoefficient rawEntry_6_02_11 r := by decide +kernel
theorem rawEntry_6_02_11_coordinates : sparsePolynomial 1 rawEntry_6_02_11=rawPlusCoordinates 2 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_11_physical : invariantSubst (rawCoordinate 6 2 11)=rawPlusPolynomial 2 11 := by
  rw [rawCoordinate_sparse 6 2 11 rawEntry_6_02_11 rawEntry_6_02_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_11)=_
  rw [rawEntry_6_02_11_coordinates]
  exact rawPlus_subst 2 11
theorem rawEntry_6_11_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 2=sparseCoefficient rawEntry_6_02_11 r := by decide +kernel
theorem rawEntry_6_11_02_physical : invariantSubst (rawCoordinate 6 11 2)=rawPlusPolynomial 11 2 := by
  have hh : rawCoordinate 6 11 2=rawCoordinate 6 2 11 := by
    rw [rawCoordinate_sparse 6 11 2 rawEntry_6_02_11 rawEntry_6_11_02_data,rawCoordinate_sparse 6 2 11 rawEntry_6_02_11 rawEntry_6_02_11_data]
  rw [hh,rawEntry_6_02_11_physical]
  exact rawPlusPolynomial_symm 2 11
def rawEntry_6_02_12 : SparseEntry := [(25,1)]
theorem rawEntry_6_02_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 12=sparseCoefficient rawEntry_6_02_12 r := by decide +kernel
theorem rawEntry_6_02_12_coordinates : sparsePolynomial 1 rawEntry_6_02_12=rawPlusCoordinates 2 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_12_physical : invariantSubst (rawCoordinate 6 2 12)=rawPlusPolynomial 2 12 := by
  rw [rawCoordinate_sparse 6 2 12 rawEntry_6_02_12 rawEntry_6_02_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_12)=_
  rw [rawEntry_6_02_12_coordinates]
  exact rawPlus_subst 2 12
theorem rawEntry_6_12_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 2=sparseCoefficient rawEntry_6_02_12 r := by decide +kernel
theorem rawEntry_6_12_02_physical : invariantSubst (rawCoordinate 6 12 2)=rawPlusPolynomial 12 2 := by
  have hh : rawCoordinate 6 12 2=rawCoordinate 6 2 12 := by
    rw [rawCoordinate_sparse 6 12 2 rawEntry_6_02_12 rawEntry_6_12_02_data,rawCoordinate_sparse 6 2 12 rawEntry_6_02_12 rawEntry_6_02_12_data]
  rw [hh,rawEntry_6_02_12_physical]
  exact rawPlusPolynomial_symm 2 12
def rawEntry_6_02_13 : SparseEntry := [(26,1)]
theorem rawEntry_6_02_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 13=sparseCoefficient rawEntry_6_02_13 r := by decide +kernel
theorem rawEntry_6_02_13_coordinates : sparsePolynomial 1 rawEntry_6_02_13=rawPlusCoordinates 2 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_13_physical : invariantSubst (rawCoordinate 6 2 13)=rawPlusPolynomial 2 13 := by
  rw [rawCoordinate_sparse 6 2 13 rawEntry_6_02_13 rawEntry_6_02_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_13)=_
  rw [rawEntry_6_02_13_coordinates]
  exact rawPlus_subst 2 13
theorem rawEntry_6_13_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 2=sparseCoefficient rawEntry_6_02_13 r := by decide +kernel
theorem rawEntry_6_13_02_physical : invariantSubst (rawCoordinate 6 13 2)=rawPlusPolynomial 13 2 := by
  have hh : rawCoordinate 6 13 2=rawCoordinate 6 2 13 := by
    rw [rawCoordinate_sparse 6 13 2 rawEntry_6_02_13 rawEntry_6_13_02_data,rawCoordinate_sparse 6 2 13 rawEntry_6_02_13 rawEntry_6_02_13_data]
  rw [hh,rawEntry_6_02_13_physical]
  exact rawPlusPolynomial_symm 2 13
def rawEntry_6_02_14 : SparseEntry := [(27,1)]
theorem rawEntry_6_02_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 14=sparseCoefficient rawEntry_6_02_14 r := by decide +kernel
theorem rawEntry_6_02_14_coordinates : sparsePolynomial 1 rawEntry_6_02_14=rawPlusCoordinates 2 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_14_physical : invariantSubst (rawCoordinate 6 2 14)=rawPlusPolynomial 2 14 := by
  rw [rawCoordinate_sparse 6 2 14 rawEntry_6_02_14 rawEntry_6_02_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_14)=_
  rw [rawEntry_6_02_14_coordinates]
  exact rawPlus_subst 2 14
theorem rawEntry_6_14_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 2=sparseCoefficient rawEntry_6_02_14 r := by decide +kernel
theorem rawEntry_6_14_02_physical : invariantSubst (rawCoordinate 6 14 2)=rawPlusPolynomial 14 2 := by
  have hh : rawCoordinate 6 14 2=rawCoordinate 6 2 14 := by
    rw [rawCoordinate_sparse 6 14 2 rawEntry_6_02_14 rawEntry_6_14_02_data,rawCoordinate_sparse 6 2 14 rawEntry_6_02_14 rawEntry_6_02_14_data]
  rw [hh,rawEntry_6_02_14_physical]
  exact rawPlusPolynomial_symm 2 14
def rawEntry_6_02_15 : SparseEntry := [(29,1)]
theorem rawEntry_6_02_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 15=sparseCoefficient rawEntry_6_02_15 r := by decide +kernel
theorem rawEntry_6_02_15_coordinates : sparsePolynomial 1 rawEntry_6_02_15=rawPlusCoordinates 2 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_15_physical : invariantSubst (rawCoordinate 6 2 15)=rawPlusPolynomial 2 15 := by
  rw [rawCoordinate_sparse 6 2 15 rawEntry_6_02_15 rawEntry_6_02_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_15)=_
  rw [rawEntry_6_02_15_coordinates]
  exact rawPlus_subst 2 15
theorem rawEntry_6_15_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 2=sparseCoefficient rawEntry_6_02_15 r := by decide +kernel
theorem rawEntry_6_15_02_physical : invariantSubst (rawCoordinate 6 15 2)=rawPlusPolynomial 15 2 := by
  have hh : rawCoordinate 6 15 2=rawCoordinate 6 2 15 := by
    rw [rawCoordinate_sparse 6 15 2 rawEntry_6_02_15 rawEntry_6_15_02_data,rawCoordinate_sparse 6 2 15 rawEntry_6_02_15 rawEntry_6_02_15_data]
  rw [hh,rawEntry_6_02_15_physical]
  exact rawPlusPolynomial_symm 2 15
def rawEntry_6_03_03 : SparseEntry := [(10,1)]
theorem rawEntry_6_03_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 3=sparseCoefficient rawEntry_6_03_03 r := by decide +kernel
theorem rawEntry_6_03_03_coordinates : sparsePolynomial 1 rawEntry_6_03_03=rawPlusCoordinates 3 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_03,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_03_physical : invariantSubst (rawCoordinate 6 3 3)=rawPlusPolynomial 3 3 := by
  rw [rawCoordinate_sparse 6 3 3 rawEntry_6_03_03 rawEntry_6_03_03_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_03)=_
  rw [rawEntry_6_03_03_coordinates]
  exact rawPlus_subst 3 3
def rawEntry_6_03_04 : SparseEntry := [(13,1)]
theorem rawEntry_6_03_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 4=sparseCoefficient rawEntry_6_03_04 r := by decide +kernel
theorem rawEntry_6_03_04_coordinates : sparsePolynomial 1 rawEntry_6_03_04=rawPlusCoordinates 3 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_04,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_04_physical : invariantSubst (rawCoordinate 6 3 4)=rawPlusPolynomial 3 4 := by
  rw [rawCoordinate_sparse 6 3 4 rawEntry_6_03_04 rawEntry_6_03_04_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_04)=_
  rw [rawEntry_6_03_04_coordinates]
  exact rawPlus_subst 3 4
theorem rawEntry_6_04_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 3=sparseCoefficient rawEntry_6_03_04 r := by decide +kernel
theorem rawEntry_6_04_03_physical : invariantSubst (rawCoordinate 6 4 3)=rawPlusPolynomial 4 3 := by
  have hh : rawCoordinate 6 4 3=rawCoordinate 6 3 4 := by
    rw [rawCoordinate_sparse 6 4 3 rawEntry_6_03_04 rawEntry_6_04_03_data,rawCoordinate_sparse 6 3 4 rawEntry_6_03_04 rawEntry_6_03_04_data]
  rw [hh,rawEntry_6_03_04_physical]
  exact rawPlusPolynomial_symm 3 4
def rawEntry_6_03_05 : SparseEntry := [(14,1)]
theorem rawEntry_6_03_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 5=sparseCoefficient rawEntry_6_03_05 r := by decide +kernel
theorem rawEntry_6_03_05_coordinates : sparsePolynomial 1 rawEntry_6_03_05=rawPlusCoordinates 3 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_05_physical : invariantSubst (rawCoordinate 6 3 5)=rawPlusPolynomial 3 5 := by
  rw [rawCoordinate_sparse 6 3 5 rawEntry_6_03_05 rawEntry_6_03_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_05)=_
  rw [rawEntry_6_03_05_coordinates]
  exact rawPlus_subst 3 5
theorem rawEntry_6_05_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 3=sparseCoefficient rawEntry_6_03_05 r := by decide +kernel
theorem rawEntry_6_05_03_physical : invariantSubst (rawCoordinate 6 5 3)=rawPlusPolynomial 5 3 := by
  have hh : rawCoordinate 6 5 3=rawCoordinate 6 3 5 := by
    rw [rawCoordinate_sparse 6 5 3 rawEntry_6_03_05 rawEntry_6_05_03_data,rawCoordinate_sparse 6 3 5 rawEntry_6_03_05 rawEntry_6_03_05_data]
  rw [hh,rawEntry_6_03_05_physical]
  exact rawPlusPolynomial_symm 3 5
def rawEntry_6_03_06 : SparseEntry := [(15,1)]
theorem rawEntry_6_03_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 6=sparseCoefficient rawEntry_6_03_06 r := by decide +kernel
theorem rawEntry_6_03_06_coordinates : sparsePolynomial 1 rawEntry_6_03_06=rawPlusCoordinates 3 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_06_physical : invariantSubst (rawCoordinate 6 3 6)=rawPlusPolynomial 3 6 := by
  rw [rawCoordinate_sparse 6 3 6 rawEntry_6_03_06 rawEntry_6_03_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_06)=_
  rw [rawEntry_6_03_06_coordinates]
  exact rawPlus_subst 3 6
theorem rawEntry_6_06_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 3=sparseCoefficient rawEntry_6_03_06 r := by decide +kernel
theorem rawEntry_6_06_03_physical : invariantSubst (rawCoordinate 6 6 3)=rawPlusPolynomial 6 3 := by
  have hh : rawCoordinate 6 6 3=rawCoordinate 6 3 6 := by
    rw [rawCoordinate_sparse 6 6 3 rawEntry_6_03_06 rawEntry_6_06_03_data,rawCoordinate_sparse 6 3 6 rawEntry_6_03_06 rawEntry_6_03_06_data]
  rw [hh,rawEntry_6_03_06_physical]
  exact rawPlusPolynomial_symm 3 6
def rawEntry_6_03_07 : SparseEntry := [(19,1)]
theorem rawEntry_6_03_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 7=sparseCoefficient rawEntry_6_03_07 r := by decide +kernel
theorem rawEntry_6_03_07_coordinates : sparsePolynomial 1 rawEntry_6_03_07=rawPlusCoordinates 3 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_07_physical : invariantSubst (rawCoordinate 6 3 7)=rawPlusPolynomial 3 7 := by
  rw [rawCoordinate_sparse 6 3 7 rawEntry_6_03_07 rawEntry_6_03_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_07)=_
  rw [rawEntry_6_03_07_coordinates]
  exact rawPlus_subst 3 7
theorem rawEntry_6_07_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 3=sparseCoefficient rawEntry_6_03_07 r := by decide +kernel
theorem rawEntry_6_07_03_physical : invariantSubst (rawCoordinate 6 7 3)=rawPlusPolynomial 7 3 := by
  have hh : rawCoordinate 6 7 3=rawCoordinate 6 3 7 := by
    rw [rawCoordinate_sparse 6 7 3 rawEntry_6_03_07 rawEntry_6_07_03_data,rawCoordinate_sparse 6 3 7 rawEntry_6_03_07 rawEntry_6_03_07_data]
  rw [hh,rawEntry_6_03_07_physical]
  exact rawPlusPolynomial_symm 3 7
def rawEntry_6_03_08 : SparseEntry := [(20,1)]
theorem rawEntry_6_03_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 8=sparseCoefficient rawEntry_6_03_08 r := by decide +kernel
theorem rawEntry_6_03_08_coordinates : sparsePolynomial 1 rawEntry_6_03_08=rawPlusCoordinates 3 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_08_physical : invariantSubst (rawCoordinate 6 3 8)=rawPlusPolynomial 3 8 := by
  rw [rawCoordinate_sparse 6 3 8 rawEntry_6_03_08 rawEntry_6_03_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_08)=_
  rw [rawEntry_6_03_08_coordinates]
  exact rawPlus_subst 3 8
theorem rawEntry_6_08_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 3=sparseCoefficient rawEntry_6_03_08 r := by decide +kernel
theorem rawEntry_6_08_03_physical : invariantSubst (rawCoordinate 6 8 3)=rawPlusPolynomial 8 3 := by
  have hh : rawCoordinate 6 8 3=rawCoordinate 6 3 8 := by
    rw [rawCoordinate_sparse 6 8 3 rawEntry_6_03_08 rawEntry_6_08_03_data,rawCoordinate_sparse 6 3 8 rawEntry_6_03_08 rawEntry_6_03_08_data]
  rw [hh,rawEntry_6_03_08_physical]
  exact rawPlusPolynomial_symm 3 8
def rawEntry_6_03_09 : SparseEntry := [(21,1)]
theorem rawEntry_6_03_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 9=sparseCoefficient rawEntry_6_03_09 r := by decide +kernel
theorem rawEntry_6_03_09_coordinates : sparsePolynomial 1 rawEntry_6_03_09=rawPlusCoordinates 3 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_09_physical : invariantSubst (rawCoordinate 6 3 9)=rawPlusPolynomial 3 9 := by
  rw [rawCoordinate_sparse 6 3 9 rawEntry_6_03_09 rawEntry_6_03_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_09)=_
  rw [rawEntry_6_03_09_coordinates]
  exact rawPlus_subst 3 9
theorem rawEntry_6_09_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 3=sparseCoefficient rawEntry_6_03_09 r := by decide +kernel
theorem rawEntry_6_09_03_physical : invariantSubst (rawCoordinate 6 9 3)=rawPlusPolynomial 9 3 := by
  have hh : rawCoordinate 6 9 3=rawCoordinate 6 3 9 := by
    rw [rawCoordinate_sparse 6 9 3 rawEntry_6_03_09 rawEntry_6_09_03_data,rawCoordinate_sparse 6 3 9 rawEntry_6_03_09 rawEntry_6_03_09_data]
  rw [hh,rawEntry_6_03_09_physical]
  exact rawPlusPolynomial_symm 3 9
def rawEntry_6_03_10 : SparseEntry := [(22,1)]
theorem rawEntry_6_03_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 10=sparseCoefficient rawEntry_6_03_10 r := by decide +kernel
theorem rawEntry_6_03_10_coordinates : sparsePolynomial 1 rawEntry_6_03_10=rawPlusCoordinates 3 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_10_physical : invariantSubst (rawCoordinate 6 3 10)=rawPlusPolynomial 3 10 := by
  rw [rawCoordinate_sparse 6 3 10 rawEntry_6_03_10 rawEntry_6_03_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_10)=_
  rw [rawEntry_6_03_10_coordinates]
  exact rawPlus_subst 3 10
theorem rawEntry_6_10_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 3=sparseCoefficient rawEntry_6_03_10 r := by decide +kernel
theorem rawEntry_6_10_03_physical : invariantSubst (rawCoordinate 6 10 3)=rawPlusPolynomial 10 3 := by
  have hh : rawCoordinate 6 10 3=rawCoordinate 6 3 10 := by
    rw [rawCoordinate_sparse 6 10 3 rawEntry_6_03_10 rawEntry_6_10_03_data,rawCoordinate_sparse 6 3 10 rawEntry_6_03_10 rawEntry_6_03_10_data]
  rw [hh,rawEntry_6_03_10_physical]
  exact rawPlusPolynomial_symm 3 10
def rawEntry_6_03_11 : SparseEntry := [(26,1)]
theorem rawEntry_6_03_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 11=sparseCoefficient rawEntry_6_03_11 r := by decide +kernel
theorem rawEntry_6_03_11_coordinates : sparsePolynomial 1 rawEntry_6_03_11=rawPlusCoordinates 3 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_11_physical : invariantSubst (rawCoordinate 6 3 11)=rawPlusPolynomial 3 11 := by
  rw [rawCoordinate_sparse 6 3 11 rawEntry_6_03_11 rawEntry_6_03_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_11)=_
  rw [rawEntry_6_03_11_coordinates]
  exact rawPlus_subst 3 11
theorem rawEntry_6_11_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 3=sparseCoefficient rawEntry_6_03_11 r := by decide +kernel
theorem rawEntry_6_11_03_physical : invariantSubst (rawCoordinate 6 11 3)=rawPlusPolynomial 11 3 := by
  have hh : rawCoordinate 6 11 3=rawCoordinate 6 3 11 := by
    rw [rawCoordinate_sparse 6 11 3 rawEntry_6_03_11 rawEntry_6_11_03_data,rawCoordinate_sparse 6 3 11 rawEntry_6_03_11 rawEntry_6_03_11_data]
  rw [hh,rawEntry_6_03_11_physical]
  exact rawPlusPolynomial_symm 3 11
def rawEntry_6_03_12 : SparseEntry := [(27,1)]
theorem rawEntry_6_03_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 12=sparseCoefficient rawEntry_6_03_12 r := by decide +kernel
theorem rawEntry_6_03_12_coordinates : sparsePolynomial 1 rawEntry_6_03_12=rawPlusCoordinates 3 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_12_physical : invariantSubst (rawCoordinate 6 3 12)=rawPlusPolynomial 3 12 := by
  rw [rawCoordinate_sparse 6 3 12 rawEntry_6_03_12 rawEntry_6_03_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_12)=_
  rw [rawEntry_6_03_12_coordinates]
  exact rawPlus_subst 3 12
theorem rawEntry_6_12_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 3=sparseCoefficient rawEntry_6_03_12 r := by decide +kernel
theorem rawEntry_6_12_03_physical : invariantSubst (rawCoordinate 6 12 3)=rawPlusPolynomial 12 3 := by
  have hh : rawCoordinate 6 12 3=rawCoordinate 6 3 12 := by
    rw [rawCoordinate_sparse 6 12 3 rawEntry_6_03_12 rawEntry_6_12_03_data,rawCoordinate_sparse 6 3 12 rawEntry_6_03_12 rawEntry_6_03_12_data]
  rw [hh,rawEntry_6_03_12_physical]
  exact rawPlusPolynomial_symm 3 12
def rawEntry_6_03_13 : SparseEntry := [(28,1)]
theorem rawEntry_6_03_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 13=sparseCoefficient rawEntry_6_03_13 r := by decide +kernel
theorem rawEntry_6_03_13_coordinates : sparsePolynomial 1 rawEntry_6_03_13=rawPlusCoordinates 3 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_13_physical : invariantSubst (rawCoordinate 6 3 13)=rawPlusPolynomial 3 13 := by
  rw [rawCoordinate_sparse 6 3 13 rawEntry_6_03_13 rawEntry_6_03_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_13)=_
  rw [rawEntry_6_03_13_coordinates]
  exact rawPlus_subst 3 13
theorem rawEntry_6_13_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 3=sparseCoefficient rawEntry_6_03_13 r := by decide +kernel
theorem rawEntry_6_13_03_physical : invariantSubst (rawCoordinate 6 13 3)=rawPlusPolynomial 13 3 := by
  have hh : rawCoordinate 6 13 3=rawCoordinate 6 3 13 := by
    rw [rawCoordinate_sparse 6 13 3 rawEntry_6_03_13 rawEntry_6_13_03_data,rawCoordinate_sparse 6 3 13 rawEntry_6_03_13 rawEntry_6_03_13_data]
  rw [hh,rawEntry_6_03_13_physical]
  exact rawPlusPolynomial_symm 3 13
def rawEntry_6_03_14 : SparseEntry := [(29,1)]
theorem rawEntry_6_03_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 14=sparseCoefficient rawEntry_6_03_14 r := by decide +kernel
theorem rawEntry_6_03_14_coordinates : sparsePolynomial 1 rawEntry_6_03_14=rawPlusCoordinates 3 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_14_physical : invariantSubst (rawCoordinate 6 3 14)=rawPlusPolynomial 3 14 := by
  rw [rawCoordinate_sparse 6 3 14 rawEntry_6_03_14 rawEntry_6_03_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_14)=_
  rw [rawEntry_6_03_14_coordinates]
  exact rawPlus_subst 3 14
theorem rawEntry_6_14_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 3=sparseCoefficient rawEntry_6_03_14 r := by decide +kernel
theorem rawEntry_6_14_03_physical : invariantSubst (rawCoordinate 6 14 3)=rawPlusPolynomial 14 3 := by
  have hh : rawCoordinate 6 14 3=rawCoordinate 6 3 14 := by
    rw [rawCoordinate_sparse 6 14 3 rawEntry_6_03_14 rawEntry_6_14_03_data,rawCoordinate_sparse 6 3 14 rawEntry_6_03_14 rawEntry_6_03_14_data]
  rw [hh,rawEntry_6_03_14_physical]
  exact rawPlusPolynomial_symm 3 14
def rawEntry_6_03_15 : SparseEntry := [(30,1)]
theorem rawEntry_6_03_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 15=sparseCoefficient rawEntry_6_03_15 r := by decide +kernel
theorem rawEntry_6_03_15_coordinates : sparsePolynomial 1 rawEntry_6_03_15=rawPlusCoordinates 3 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_03_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_03_15_physical : invariantSubst (rawCoordinate 6 3 15)=rawPlusPolynomial 3 15 := by
  rw [rawCoordinate_sparse 6 3 15 rawEntry_6_03_15 rawEntry_6_03_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_03_15)=_
  rw [rawEntry_6_03_15_coordinates]
  exact rawPlus_subst 3 15
theorem rawEntry_6_15_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 3=sparseCoefficient rawEntry_6_03_15 r := by decide +kernel
theorem rawEntry_6_15_03_physical : invariantSubst (rawCoordinate 6 15 3)=rawPlusPolynomial 15 3 := by
  have hh : rawCoordinate 6 15 3=rawCoordinate 6 3 15 := by
    rw [rawCoordinate_sparse 6 15 3 rawEntry_6_03_15 rawEntry_6_15_03_data,rawCoordinate_sparse 6 3 15 rawEntry_6_03_15 rawEntry_6_03_15_data]
  rw [hh,rawEntry_6_03_15_physical]
  exact rawPlusPolynomial_symm 3 15
def rawEntry_6_04_04 : SparseEntry := [(16,1)]
theorem rawEntry_6_04_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 4=sparseCoefficient rawEntry_6_04_04 r := by decide +kernel
theorem rawEntry_6_04_04_coordinates : sparsePolynomial 1 rawEntry_6_04_04=rawPlusCoordinates 4 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_04,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_04_physical : invariantSubst (rawCoordinate 6 4 4)=rawPlusPolynomial 4 4 := by
  rw [rawCoordinate_sparse 6 4 4 rawEntry_6_04_04 rawEntry_6_04_04_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_04)=_
  rw [rawEntry_6_04_04_coordinates]
  exact rawPlus_subst 4 4
def rawEntry_6_04_05 : SparseEntry := [(18,1)]
theorem rawEntry_6_04_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 5=sparseCoefficient rawEntry_6_04_05 r := by decide +kernel
theorem rawEntry_6_04_05_coordinates : sparsePolynomial 1 rawEntry_6_04_05=rawPlusCoordinates 4 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_04_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_04_05_physical : invariantSubst (rawCoordinate 6 4 5)=rawPlusPolynomial 4 5 := by
  rw [rawCoordinate_sparse 6 4 5 rawEntry_6_04_05 rawEntry_6_04_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_04_05)=_
  rw [rawEntry_6_04_05_coordinates]
  exact rawPlus_subst 4 5
theorem rawEntry_6_05_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 4=sparseCoefficient rawEntry_6_04_05 r := by decide +kernel
theorem rawEntry_6_05_04_physical : invariantSubst (rawCoordinate 6 5 4)=rawPlusPolynomial 5 4 := by
  have hh : rawCoordinate 6 5 4=rawCoordinate 6 4 5 := by
    rw [rawCoordinate_sparse 6 5 4 rawEntry_6_04_05 rawEntry_6_05_04_data,rawCoordinate_sparse 6 4 5 rawEntry_6_04_05 rawEntry_6_04_05_data]
  rw [hh,rawEntry_6_04_05_physical]
  exact rawPlusPolynomial_symm 4 5
end ThomsonNegative.Certificate.Bridges
