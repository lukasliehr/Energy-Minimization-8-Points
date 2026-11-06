import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_01_05 : SparseEntry := [(9,1)]
theorem rawEntry_6_01_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 5=sparseCoefficient rawEntry_6_01_05 r := by decide +kernel
theorem rawEntry_6_01_05_coordinates : sparsePolynomial 1 rawEntry_6_01_05=rawPlusCoordinates 1 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_05_physical : invariantSubst (rawCoordinate 6 1 5)=rawPlusPolynomial 1 5 := by
  rw [rawCoordinate_sparse 6 1 5 rawEntry_6_01_05 rawEntry_6_01_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_05)=_
  rw [rawEntry_6_01_05_coordinates]
  exact rawPlus_subst 1 5
theorem rawEntry_6_05_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 1=sparseCoefficient rawEntry_6_01_05 r := by decide +kernel
theorem rawEntry_6_05_01_physical : invariantSubst (rawCoordinate 6 5 1)=rawPlusPolynomial 5 1 := by
  have hh : rawCoordinate 6 5 1=rawCoordinate 6 1 5 := by
    rw [rawCoordinate_sparse 6 5 1 rawEntry_6_01_05 rawEntry_6_05_01_data,rawCoordinate_sparse 6 1 5 rawEntry_6_01_05 rawEntry_6_01_05_data]
  rw [hh,rawEntry_6_01_05_physical]
  exact rawPlusPolynomial_symm 1 5
def rawEntry_6_01_06 : SparseEntry := [(10,1)]
theorem rawEntry_6_01_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 6=sparseCoefficient rawEntry_6_01_06 r := by decide +kernel
theorem rawEntry_6_01_06_coordinates : sparsePolynomial 1 rawEntry_6_01_06=rawPlusCoordinates 1 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_06_physical : invariantSubst (rawCoordinate 6 1 6)=rawPlusPolynomial 1 6 := by
  rw [rawCoordinate_sparse 6 1 6 rawEntry_6_01_06 rawEntry_6_01_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_06)=_
  rw [rawEntry_6_01_06_coordinates]
  exact rawPlus_subst 1 6
theorem rawEntry_6_06_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 1=sparseCoefficient rawEntry_6_01_06 r := by decide +kernel
theorem rawEntry_6_06_01_physical : invariantSubst (rawCoordinate 6 6 1)=rawPlusPolynomial 6 1 := by
  have hh : rawCoordinate 6 6 1=rawCoordinate 6 1 6 := by
    rw [rawCoordinate_sparse 6 6 1 rawEntry_6_01_06 rawEntry_6_06_01_data,rawCoordinate_sparse 6 1 6 rawEntry_6_01_06 rawEntry_6_01_06_data]
  rw [hh,rawEntry_6_01_06_physical]
  exact rawPlusPolynomial_symm 1 6
def rawEntry_6_01_07 : SparseEntry := [(12,1)]
theorem rawEntry_6_01_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 7=sparseCoefficient rawEntry_6_01_07 r := by decide +kernel
theorem rawEntry_6_01_07_coordinates : sparsePolynomial 1 rawEntry_6_01_07=rawPlusCoordinates 1 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_07_physical : invariantSubst (rawCoordinate 6 1 7)=rawPlusPolynomial 1 7 := by
  rw [rawCoordinate_sparse 6 1 7 rawEntry_6_01_07 rawEntry_6_01_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_07)=_
  rw [rawEntry_6_01_07_coordinates]
  exact rawPlus_subst 1 7
theorem rawEntry_6_07_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 1=sparseCoefficient rawEntry_6_01_07 r := by decide +kernel
theorem rawEntry_6_07_01_physical : invariantSubst (rawCoordinate 6 7 1)=rawPlusPolynomial 7 1 := by
  have hh : rawCoordinate 6 7 1=rawCoordinate 6 1 7 := by
    rw [rawCoordinate_sparse 6 7 1 rawEntry_6_01_07 rawEntry_6_07_01_data,rawCoordinate_sparse 6 1 7 rawEntry_6_01_07 rawEntry_6_01_07_data]
  rw [hh,rawEntry_6_01_07_physical]
  exact rawPlusPolynomial_symm 1 7
def rawEntry_6_01_08 : SparseEntry := [(13,1)]
theorem rawEntry_6_01_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 8=sparseCoefficient rawEntry_6_01_08 r := by decide +kernel
theorem rawEntry_6_01_08_coordinates : sparsePolynomial 1 rawEntry_6_01_08=rawPlusCoordinates 1 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_08_physical : invariantSubst (rawCoordinate 6 1 8)=rawPlusPolynomial 1 8 := by
  rw [rawCoordinate_sparse 6 1 8 rawEntry_6_01_08 rawEntry_6_01_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_08)=_
  rw [rawEntry_6_01_08_coordinates]
  exact rawPlus_subst 1 8
theorem rawEntry_6_08_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 1=sparseCoefficient rawEntry_6_01_08 r := by decide +kernel
theorem rawEntry_6_08_01_physical : invariantSubst (rawCoordinate 6 8 1)=rawPlusPolynomial 8 1 := by
  have hh : rawCoordinate 6 8 1=rawCoordinate 6 1 8 := by
    rw [rawCoordinate_sparse 6 8 1 rawEntry_6_01_08 rawEntry_6_08_01_data,rawCoordinate_sparse 6 1 8 rawEntry_6_01_08 rawEntry_6_01_08_data]
  rw [hh,rawEntry_6_01_08_physical]
  exact rawPlusPolynomial_symm 1 8
def rawEntry_6_01_09 : SparseEntry := [(14,1)]
theorem rawEntry_6_01_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 9=sparseCoefficient rawEntry_6_01_09 r := by decide +kernel
theorem rawEntry_6_01_09_coordinates : sparsePolynomial 1 rawEntry_6_01_09=rawPlusCoordinates 1 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_09_physical : invariantSubst (rawCoordinate 6 1 9)=rawPlusPolynomial 1 9 := by
  rw [rawCoordinate_sparse 6 1 9 rawEntry_6_01_09 rawEntry_6_01_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_09)=_
  rw [rawEntry_6_01_09_coordinates]
  exact rawPlus_subst 1 9
theorem rawEntry_6_09_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 1=sparseCoefficient rawEntry_6_01_09 r := by decide +kernel
theorem rawEntry_6_09_01_physical : invariantSubst (rawCoordinate 6 9 1)=rawPlusPolynomial 9 1 := by
  have hh : rawCoordinate 6 9 1=rawCoordinate 6 1 9 := by
    rw [rawCoordinate_sparse 6 9 1 rawEntry_6_01_09 rawEntry_6_09_01_data,rawCoordinate_sparse 6 1 9 rawEntry_6_01_09 rawEntry_6_01_09_data]
  rw [hh,rawEntry_6_01_09_physical]
  exact rawPlusPolynomial_symm 1 9
def rawEntry_6_01_10 : SparseEntry := [(15,1)]
theorem rawEntry_6_01_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 10=sparseCoefficient rawEntry_6_01_10 r := by decide +kernel
theorem rawEntry_6_01_10_coordinates : sparsePolynomial 1 rawEntry_6_01_10=rawPlusCoordinates 1 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_10_physical : invariantSubst (rawCoordinate 6 1 10)=rawPlusPolynomial 1 10 := by
  rw [rawCoordinate_sparse 6 1 10 rawEntry_6_01_10 rawEntry_6_01_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_10)=_
  rw [rawEntry_6_01_10_coordinates]
  exact rawPlus_subst 1 10
theorem rawEntry_6_10_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 1=sparseCoefficient rawEntry_6_01_10 r := by decide +kernel
theorem rawEntry_6_10_01_physical : invariantSubst (rawCoordinate 6 10 1)=rawPlusPolynomial 10 1 := by
  have hh : rawCoordinate 6 10 1=rawCoordinate 6 1 10 := by
    rw [rawCoordinate_sparse 6 10 1 rawEntry_6_01_10 rawEntry_6_10_01_data,rawCoordinate_sparse 6 1 10 rawEntry_6_01_10 rawEntry_6_01_10_data]
  rw [hh,rawEntry_6_01_10_physical]
  exact rawPlusPolynomial_symm 1 10
def rawEntry_6_01_11 : SparseEntry := [(18,1)]
theorem rawEntry_6_01_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 11=sparseCoefficient rawEntry_6_01_11 r := by decide +kernel
theorem rawEntry_6_01_11_coordinates : sparsePolynomial 1 rawEntry_6_01_11=rawPlusCoordinates 1 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_11_physical : invariantSubst (rawCoordinate 6 1 11)=rawPlusPolynomial 1 11 := by
  rw [rawCoordinate_sparse 6 1 11 rawEntry_6_01_11 rawEntry_6_01_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_11)=_
  rw [rawEntry_6_01_11_coordinates]
  exact rawPlus_subst 1 11
theorem rawEntry_6_11_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 1=sparseCoefficient rawEntry_6_01_11 r := by decide +kernel
theorem rawEntry_6_11_01_physical : invariantSubst (rawCoordinate 6 11 1)=rawPlusPolynomial 11 1 := by
  have hh : rawCoordinate 6 11 1=rawCoordinate 6 1 11 := by
    rw [rawCoordinate_sparse 6 11 1 rawEntry_6_01_11 rawEntry_6_11_01_data,rawCoordinate_sparse 6 1 11 rawEntry_6_01_11 rawEntry_6_01_11_data]
  rw [hh,rawEntry_6_01_11_physical]
  exact rawPlusPolynomial_symm 1 11
def rawEntry_6_01_12 : SparseEntry := [(19,1)]
theorem rawEntry_6_01_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 12=sparseCoefficient rawEntry_6_01_12 r := by decide +kernel
theorem rawEntry_6_01_12_coordinates : sparsePolynomial 1 rawEntry_6_01_12=rawPlusCoordinates 1 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_12_physical : invariantSubst (rawCoordinate 6 1 12)=rawPlusPolynomial 1 12 := by
  rw [rawCoordinate_sparse 6 1 12 rawEntry_6_01_12 rawEntry_6_01_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_12)=_
  rw [rawEntry_6_01_12_coordinates]
  exact rawPlus_subst 1 12
theorem rawEntry_6_12_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 1=sparseCoefficient rawEntry_6_01_12 r := by decide +kernel
theorem rawEntry_6_12_01_physical : invariantSubst (rawCoordinate 6 12 1)=rawPlusPolynomial 12 1 := by
  have hh : rawCoordinate 6 12 1=rawCoordinate 6 1 12 := by
    rw [rawCoordinate_sparse 6 12 1 rawEntry_6_01_12 rawEntry_6_12_01_data,rawCoordinate_sparse 6 1 12 rawEntry_6_01_12 rawEntry_6_01_12_data]
  rw [hh,rawEntry_6_01_12_physical]
  exact rawPlusPolynomial_symm 1 12
def rawEntry_6_01_13 : SparseEntry := [(20,1)]
theorem rawEntry_6_01_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 13=sparseCoefficient rawEntry_6_01_13 r := by decide +kernel
theorem rawEntry_6_01_13_coordinates : sparsePolynomial 1 rawEntry_6_01_13=rawPlusCoordinates 1 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_13_physical : invariantSubst (rawCoordinate 6 1 13)=rawPlusPolynomial 1 13 := by
  rw [rawCoordinate_sparse 6 1 13 rawEntry_6_01_13 rawEntry_6_01_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_13)=_
  rw [rawEntry_6_01_13_coordinates]
  exact rawPlus_subst 1 13
theorem rawEntry_6_13_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 1=sparseCoefficient rawEntry_6_01_13 r := by decide +kernel
theorem rawEntry_6_13_01_physical : invariantSubst (rawCoordinate 6 13 1)=rawPlusPolynomial 13 1 := by
  have hh : rawCoordinate 6 13 1=rawCoordinate 6 1 13 := by
    rw [rawCoordinate_sparse 6 13 1 rawEntry_6_01_13 rawEntry_6_13_01_data,rawCoordinate_sparse 6 1 13 rawEntry_6_01_13 rawEntry_6_01_13_data]
  rw [hh,rawEntry_6_01_13_physical]
  exact rawPlusPolynomial_symm 1 13
def rawEntry_6_01_14 : SparseEntry := [(21,1)]
theorem rawEntry_6_01_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 14=sparseCoefficient rawEntry_6_01_14 r := by decide +kernel
theorem rawEntry_6_01_14_coordinates : sparsePolynomial 1 rawEntry_6_01_14=rawPlusCoordinates 1 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_14_physical : invariantSubst (rawCoordinate 6 1 14)=rawPlusPolynomial 1 14 := by
  rw [rawCoordinate_sparse 6 1 14 rawEntry_6_01_14 rawEntry_6_01_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_14)=_
  rw [rawEntry_6_01_14_coordinates]
  exact rawPlus_subst 1 14
theorem rawEntry_6_14_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 1=sparseCoefficient rawEntry_6_01_14 r := by decide +kernel
theorem rawEntry_6_14_01_physical : invariantSubst (rawCoordinate 6 14 1)=rawPlusPolynomial 14 1 := by
  have hh : rawCoordinate 6 14 1=rawCoordinate 6 1 14 := by
    rw [rawCoordinate_sparse 6 14 1 rawEntry_6_01_14 rawEntry_6_14_01_data,rawCoordinate_sparse 6 1 14 rawEntry_6_01_14 rawEntry_6_01_14_data]
  rw [hh,rawEntry_6_01_14_physical]
  exact rawPlusPolynomial_symm 1 14
def rawEntry_6_01_15 : SparseEntry := [(22,1)]
theorem rawEntry_6_01_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 15=sparseCoefficient rawEntry_6_01_15 r := by decide +kernel
theorem rawEntry_6_01_15_coordinates : sparsePolynomial 1 rawEntry_6_01_15=rawPlusCoordinates 1 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_15_physical : invariantSubst (rawCoordinate 6 1 15)=rawPlusPolynomial 1 15 := by
  rw [rawCoordinate_sparse 6 1 15 rawEntry_6_01_15 rawEntry_6_01_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_15)=_
  rw [rawEntry_6_01_15_coordinates]
  exact rawPlus_subst 1 15
theorem rawEntry_6_15_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 1=sparseCoefficient rawEntry_6_01_15 r := by decide +kernel
theorem rawEntry_6_15_01_physical : invariantSubst (rawCoordinate 6 15 1)=rawPlusPolynomial 15 1 := by
  have hh : rawCoordinate 6 15 1=rawCoordinate 6 1 15 := by
    rw [rawCoordinate_sparse 6 15 1 rawEntry_6_01_15 rawEntry_6_15_01_data,rawCoordinate_sparse 6 1 15 rawEntry_6_01_15 rawEntry_6_01_15_data]
  rw [hh,rawEntry_6_01_15_physical]
  exact rawPlusPolynomial_symm 1 15
def rawEntry_6_02_02 : SparseEntry := [(7,1)]
theorem rawEntry_6_02_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 2=sparseCoefficient rawEntry_6_02_02 r := by decide +kernel
theorem rawEntry_6_02_02_coordinates : sparsePolynomial 1 rawEntry_6_02_02=rawPlusCoordinates 2 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_02,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_02_physical : invariantSubst (rawCoordinate 6 2 2)=rawPlusPolynomial 2 2 := by
  rw [rawCoordinate_sparse 6 2 2 rawEntry_6_02_02 rawEntry_6_02_02_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_02)=_
  rw [rawEntry_6_02_02_coordinates]
  exact rawPlus_subst 2 2
def rawEntry_6_02_03 : SparseEntry := [(9,1)]
theorem rawEntry_6_02_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 3=sparseCoefficient rawEntry_6_02_03 r := by decide +kernel
theorem rawEntry_6_02_03_coordinates : sparsePolynomial 1 rawEntry_6_02_03=rawPlusCoordinates 2 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_03,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_03_physical : invariantSubst (rawCoordinate 6 2 3)=rawPlusPolynomial 2 3 := by
  rw [rawCoordinate_sparse 6 2 3 rawEntry_6_02_03 rawEntry_6_02_03_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_03)=_
  rw [rawEntry_6_02_03_coordinates]
  exact rawPlus_subst 2 3
theorem rawEntry_6_03_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 2=sparseCoefficient rawEntry_6_02_03 r := by decide +kernel
theorem rawEntry_6_03_02_physical : invariantSubst (rawCoordinate 6 3 2)=rawPlusPolynomial 3 2 := by
  have hh : rawCoordinate 6 3 2=rawCoordinate 6 2 3 := by
    rw [rawCoordinate_sparse 6 3 2 rawEntry_6_02_03 rawEntry_6_03_02_data,rawCoordinate_sparse 6 2 3 rawEntry_6_02_03 rawEntry_6_02_03_data]
  rw [hh,rawEntry_6_02_03_physical]
  exact rawPlusPolynomial_symm 2 3
def rawEntry_6_02_04 : SparseEntry := [(11,1)]
theorem rawEntry_6_02_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 4=sparseCoefficient rawEntry_6_02_04 r := by decide +kernel
theorem rawEntry_6_02_04_coordinates : sparsePolynomial 1 rawEntry_6_02_04=rawPlusCoordinates 2 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_04,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_04_physical : invariantSubst (rawCoordinate 6 2 4)=rawPlusPolynomial 2 4 := by
  rw [rawCoordinate_sparse 6 2 4 rawEntry_6_02_04 rawEntry_6_02_04_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_04)=_
  rw [rawEntry_6_02_04_coordinates]
  exact rawPlus_subst 2 4
theorem rawEntry_6_04_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 2=sparseCoefficient rawEntry_6_02_04 r := by decide +kernel
theorem rawEntry_6_04_02_physical : invariantSubst (rawCoordinate 6 4 2)=rawPlusPolynomial 4 2 := by
  have hh : rawCoordinate 6 4 2=rawCoordinate 6 2 4 := by
    rw [rawCoordinate_sparse 6 4 2 rawEntry_6_02_04 rawEntry_6_04_02_data,rawCoordinate_sparse 6 2 4 rawEntry_6_02_04 rawEntry_6_02_04_data]
  rw [hh,rawEntry_6_02_04_physical]
  exact rawPlusPolynomial_symm 2 4
def rawEntry_6_02_05 : SparseEntry := [(12,1)]
theorem rawEntry_6_02_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 5=sparseCoefficient rawEntry_6_02_05 r := by decide +kernel
theorem rawEntry_6_02_05_coordinates : sparsePolynomial 1 rawEntry_6_02_05=rawPlusCoordinates 2 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_05_physical : invariantSubst (rawCoordinate 6 2 5)=rawPlusPolynomial 2 5 := by
  rw [rawCoordinate_sparse 6 2 5 rawEntry_6_02_05 rawEntry_6_02_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_05)=_
  rw [rawEntry_6_02_05_coordinates]
  exact rawPlus_subst 2 5
theorem rawEntry_6_05_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 2=sparseCoefficient rawEntry_6_02_05 r := by decide +kernel
theorem rawEntry_6_05_02_physical : invariantSubst (rawCoordinate 6 5 2)=rawPlusPolynomial 5 2 := by
  have hh : rawCoordinate 6 5 2=rawCoordinate 6 2 5 := by
    rw [rawCoordinate_sparse 6 5 2 rawEntry_6_02_05 rawEntry_6_05_02_data,rawCoordinate_sparse 6 2 5 rawEntry_6_02_05 rawEntry_6_02_05_data]
  rw [hh,rawEntry_6_02_05_physical]
  exact rawPlusPolynomial_symm 2 5
def rawEntry_6_02_06 : SparseEntry := [(14,1)]
theorem rawEntry_6_02_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 6=sparseCoefficient rawEntry_6_02_06 r := by decide +kernel
theorem rawEntry_6_02_06_coordinates : sparsePolynomial 1 rawEntry_6_02_06=rawPlusCoordinates 2 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_06_physical : invariantSubst (rawCoordinate 6 2 6)=rawPlusPolynomial 2 6 := by
  rw [rawCoordinate_sparse 6 2 6 rawEntry_6_02_06 rawEntry_6_02_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_06)=_
  rw [rawEntry_6_02_06_coordinates]
  exact rawPlus_subst 2 6
theorem rawEntry_6_06_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 2=sparseCoefficient rawEntry_6_02_06 r := by decide +kernel
theorem rawEntry_6_06_02_physical : invariantSubst (rawCoordinate 6 6 2)=rawPlusPolynomial 6 2 := by
  have hh : rawCoordinate 6 6 2=rawCoordinate 6 2 6 := by
    rw [rawCoordinate_sparse 6 6 2 rawEntry_6_02_06 rawEntry_6_06_02_data,rawCoordinate_sparse 6 2 6 rawEntry_6_02_06 rawEntry_6_02_06_data]
  rw [hh,rawEntry_6_02_06_physical]
  exact rawPlusPolynomial_symm 2 6
def rawEntry_6_02_07 : SparseEntry := [(17,1)]
theorem rawEntry_6_02_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 7=sparseCoefficient rawEntry_6_02_07 r := by decide +kernel
theorem rawEntry_6_02_07_coordinates : sparsePolynomial 1 rawEntry_6_02_07=rawPlusCoordinates 2 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_07_physical : invariantSubst (rawCoordinate 6 2 7)=rawPlusPolynomial 2 7 := by
  rw [rawCoordinate_sparse 6 2 7 rawEntry_6_02_07 rawEntry_6_02_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_07)=_
  rw [rawEntry_6_02_07_coordinates]
  exact rawPlus_subst 2 7
theorem rawEntry_6_07_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 2=sparseCoefficient rawEntry_6_02_07 r := by decide +kernel
theorem rawEntry_6_07_02_physical : invariantSubst (rawCoordinate 6 7 2)=rawPlusPolynomial 7 2 := by
  have hh : rawCoordinate 6 7 2=rawCoordinate 6 2 7 := by
    rw [rawCoordinate_sparse 6 7 2 rawEntry_6_02_07 rawEntry_6_07_02_data,rawCoordinate_sparse 6 2 7 rawEntry_6_02_07 rawEntry_6_02_07_data]
  rw [hh,rawEntry_6_02_07_physical]
  exact rawPlusPolynomial_symm 2 7
def rawEntry_6_02_08 : SparseEntry := [(18,1)]
theorem rawEntry_6_02_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 8=sparseCoefficient rawEntry_6_02_08 r := by decide +kernel
theorem rawEntry_6_02_08_coordinates : sparsePolynomial 1 rawEntry_6_02_08=rawPlusCoordinates 2 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_08_physical : invariantSubst (rawCoordinate 6 2 8)=rawPlusPolynomial 2 8 := by
  rw [rawCoordinate_sparse 6 2 8 rawEntry_6_02_08 rawEntry_6_02_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_08)=_
  rw [rawEntry_6_02_08_coordinates]
  exact rawPlus_subst 2 8
theorem rawEntry_6_08_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 2=sparseCoefficient rawEntry_6_02_08 r := by decide +kernel
theorem rawEntry_6_08_02_physical : invariantSubst (rawCoordinate 6 8 2)=rawPlusPolynomial 8 2 := by
  have hh : rawCoordinate 6 8 2=rawCoordinate 6 2 8 := by
    rw [rawCoordinate_sparse 6 8 2 rawEntry_6_02_08 rawEntry_6_08_02_data,rawCoordinate_sparse 6 2 8 rawEntry_6_02_08 rawEntry_6_02_08_data]
  rw [hh,rawEntry_6_02_08_physical]
  exact rawPlusPolynomial_symm 2 8
def rawEntry_6_02_09 : SparseEntry := [(19,1)]
theorem rawEntry_6_02_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 9=sparseCoefficient rawEntry_6_02_09 r := by decide +kernel
theorem rawEntry_6_02_09_coordinates : sparsePolynomial 1 rawEntry_6_02_09=rawPlusCoordinates 2 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_09_physical : invariantSubst (rawCoordinate 6 2 9)=rawPlusPolynomial 2 9 := by
  rw [rawCoordinate_sparse 6 2 9 rawEntry_6_02_09 rawEntry_6_02_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_09)=_
  rw [rawEntry_6_02_09_coordinates]
  exact rawPlus_subst 2 9
theorem rawEntry_6_09_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 2=sparseCoefficient rawEntry_6_02_09 r := by decide +kernel
theorem rawEntry_6_09_02_physical : invariantSubst (rawCoordinate 6 9 2)=rawPlusPolynomial 9 2 := by
  have hh : rawCoordinate 6 9 2=rawCoordinate 6 2 9 := by
    rw [rawCoordinate_sparse 6 9 2 rawEntry_6_02_09 rawEntry_6_09_02_data,rawCoordinate_sparse 6 2 9 rawEntry_6_02_09 rawEntry_6_02_09_data]
  rw [hh,rawEntry_6_02_09_physical]
  exact rawPlusPolynomial_symm 2 9
def rawEntry_6_02_10 : SparseEntry := [(21,1)]
theorem rawEntry_6_02_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 10=sparseCoefficient rawEntry_6_02_10 r := by decide +kernel
theorem rawEntry_6_02_10_coordinates : sparsePolynomial 1 rawEntry_6_02_10=rawPlusCoordinates 2 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_02_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_02_10_physical : invariantSubst (rawCoordinate 6 2 10)=rawPlusPolynomial 2 10 := by
  rw [rawCoordinate_sparse 6 2 10 rawEntry_6_02_10 rawEntry_6_02_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_02_10)=_
  rw [rawEntry_6_02_10_coordinates]
  exact rawPlus_subst 2 10
theorem rawEntry_6_10_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 2=sparseCoefficient rawEntry_6_02_10 r := by decide +kernel
theorem rawEntry_6_10_02_physical : invariantSubst (rawCoordinate 6 10 2)=rawPlusPolynomial 10 2 := by
  have hh : rawCoordinate 6 10 2=rawCoordinate 6 2 10 := by
    rw [rawCoordinate_sparse 6 10 2 rawEntry_6_02_10 rawEntry_6_10_02_data,rawCoordinate_sparse 6 2 10 rawEntry_6_02_10 rawEntry_6_02_10_data]
  rw [hh,rawEntry_6_02_10_physical]
  exact rawPlusPolynomial_symm 2 10
end ThomsonNegative.Certificate.Bridges
