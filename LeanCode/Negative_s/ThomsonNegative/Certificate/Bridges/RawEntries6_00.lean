import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_00_00 : SparseEntry := [(0,1)]
theorem rawEntry_6_00_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 0=sparseCoefficient rawEntry_6_00_00 r := by decide +kernel
theorem rawEntry_6_00_00_coordinates : sparsePolynomial 1 rawEntry_6_00_00=rawPlusCoordinates 0 0 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_00,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_00_physical : invariantSubst (rawCoordinate 6 0 0)=rawPlusPolynomial 0 0 := by
  rw [rawCoordinate_sparse 6 0 0 rawEntry_6_00_00 rawEntry_6_00_00_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_00)=_
  rw [rawEntry_6_00_00_coordinates]
  exact rawPlus_subst 0 0
def rawEntry_6_00_01 : SparseEntry := [(1,1)]
theorem rawEntry_6_00_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 1=sparseCoefficient rawEntry_6_00_01 r := by decide +kernel
theorem rawEntry_6_00_01_coordinates : sparsePolynomial 1 rawEntry_6_00_01=rawPlusCoordinates 0 1 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_01,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_01_physical : invariantSubst (rawCoordinate 6 0 1)=rawPlusPolynomial 0 1 := by
  rw [rawCoordinate_sparse 6 0 1 rawEntry_6_00_01 rawEntry_6_00_01_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_01)=_
  rw [rawEntry_6_00_01_coordinates]
  exact rawPlus_subst 0 1
theorem rawEntry_6_01_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 0=sparseCoefficient rawEntry_6_00_01 r := by decide +kernel
theorem rawEntry_6_01_00_physical : invariantSubst (rawCoordinate 6 1 0)=rawPlusPolynomial 1 0 := by
  have hh : rawCoordinate 6 1 0=rawCoordinate 6 0 1 := by
    rw [rawCoordinate_sparse 6 1 0 rawEntry_6_00_01 rawEntry_6_01_00_data,rawCoordinate_sparse 6 0 1 rawEntry_6_00_01 rawEntry_6_00_01_data]
  rw [hh,rawEntry_6_00_01_physical]
  exact rawPlusPolynomial_symm 0 1
def rawEntry_6_00_02 : SparseEntry := [(2,1)]
theorem rawEntry_6_00_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 2=sparseCoefficient rawEntry_6_00_02 r := by decide +kernel
theorem rawEntry_6_00_02_coordinates : sparsePolynomial 1 rawEntry_6_00_02=rawPlusCoordinates 0 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_02,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_02_physical : invariantSubst (rawCoordinate 6 0 2)=rawPlusPolynomial 0 2 := by
  rw [rawCoordinate_sparse 6 0 2 rawEntry_6_00_02 rawEntry_6_00_02_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_02)=_
  rw [rawEntry_6_00_02_coordinates]
  exact rawPlus_subst 0 2
theorem rawEntry_6_02_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 0=sparseCoefficient rawEntry_6_00_02 r := by decide +kernel
theorem rawEntry_6_02_00_physical : invariantSubst (rawCoordinate 6 2 0)=rawPlusPolynomial 2 0 := by
  have hh : rawCoordinate 6 2 0=rawCoordinate 6 0 2 := by
    rw [rawCoordinate_sparse 6 2 0 rawEntry_6_00_02 rawEntry_6_02_00_data,rawCoordinate_sparse 6 0 2 rawEntry_6_00_02 rawEntry_6_00_02_data]
  rw [hh,rawEntry_6_00_02_physical]
  exact rawPlusPolynomial_symm 0 2
def rawEntry_6_00_03 : SparseEntry := [(3,1)]
theorem rawEntry_6_00_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 3=sparseCoefficient rawEntry_6_00_03 r := by decide +kernel
theorem rawEntry_6_00_03_coordinates : sparsePolynomial 1 rawEntry_6_00_03=rawPlusCoordinates 0 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_03,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_03_physical : invariantSubst (rawCoordinate 6 0 3)=rawPlusPolynomial 0 3 := by
  rw [rawCoordinate_sparse 6 0 3 rawEntry_6_00_03 rawEntry_6_00_03_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_03)=_
  rw [rawEntry_6_00_03_coordinates]
  exact rawPlus_subst 0 3
theorem rawEntry_6_03_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 0=sparseCoefficient rawEntry_6_00_03 r := by decide +kernel
theorem rawEntry_6_03_00_physical : invariantSubst (rawCoordinate 6 3 0)=rawPlusPolynomial 3 0 := by
  have hh : rawCoordinate 6 3 0=rawCoordinate 6 0 3 := by
    rw [rawCoordinate_sparse 6 3 0 rawEntry_6_00_03 rawEntry_6_03_00_data,rawCoordinate_sparse 6 0 3 rawEntry_6_00_03 rawEntry_6_00_03_data]
  rw [hh,rawEntry_6_00_03_physical]
  exact rawPlusPolynomial_symm 0 3
def rawEntry_6_00_04 : SparseEntry := [(4,1)]
theorem rawEntry_6_00_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 4=sparseCoefficient rawEntry_6_00_04 r := by decide +kernel
theorem rawEntry_6_00_04_coordinates : sparsePolynomial 1 rawEntry_6_00_04=rawPlusCoordinates 0 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_04,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_04_physical : invariantSubst (rawCoordinate 6 0 4)=rawPlusPolynomial 0 4 := by
  rw [rawCoordinate_sparse 6 0 4 rawEntry_6_00_04 rawEntry_6_00_04_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_04)=_
  rw [rawEntry_6_00_04_coordinates]
  exact rawPlus_subst 0 4
theorem rawEntry_6_04_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 0=sparseCoefficient rawEntry_6_00_04 r := by decide +kernel
theorem rawEntry_6_04_00_physical : invariantSubst (rawCoordinate 6 4 0)=rawPlusPolynomial 4 0 := by
  have hh : rawCoordinate 6 4 0=rawCoordinate 6 0 4 := by
    rw [rawCoordinate_sparse 6 4 0 rawEntry_6_00_04 rawEntry_6_04_00_data,rawCoordinate_sparse 6 0 4 rawEntry_6_00_04 rawEntry_6_00_04_data]
  rw [hh,rawEntry_6_00_04_physical]
  exact rawPlusPolynomial_symm 0 4
def rawEntry_6_00_05 : SparseEntry := [(5,1)]
theorem rawEntry_6_00_05_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 5=sparseCoefficient rawEntry_6_00_05 r := by decide +kernel
theorem rawEntry_6_00_05_coordinates : sparsePolynomial 1 rawEntry_6_00_05=rawPlusCoordinates 0 5 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_05,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_05_physical : invariantSubst (rawCoordinate 6 0 5)=rawPlusPolynomial 0 5 := by
  rw [rawCoordinate_sparse 6 0 5 rawEntry_6_00_05 rawEntry_6_00_05_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_05)=_
  rw [rawEntry_6_00_05_coordinates]
  exact rawPlus_subst 0 5
theorem rawEntry_6_05_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 5 0=sparseCoefficient rawEntry_6_00_05 r := by decide +kernel
theorem rawEntry_6_05_00_physical : invariantSubst (rawCoordinate 6 5 0)=rawPlusPolynomial 5 0 := by
  have hh : rawCoordinate 6 5 0=rawCoordinate 6 0 5 := by
    rw [rawCoordinate_sparse 6 5 0 rawEntry_6_00_05 rawEntry_6_05_00_data,rawCoordinate_sparse 6 0 5 rawEntry_6_00_05 rawEntry_6_00_05_data]
  rw [hh,rawEntry_6_00_05_physical]
  exact rawPlusPolynomial_symm 0 5
def rawEntry_6_00_06 : SparseEntry := [(6,1)]
theorem rawEntry_6_00_06_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 6=sparseCoefficient rawEntry_6_00_06 r := by decide +kernel
theorem rawEntry_6_00_06_coordinates : sparsePolynomial 1 rawEntry_6_00_06=rawPlusCoordinates 0 6 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_06,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_06_physical : invariantSubst (rawCoordinate 6 0 6)=rawPlusPolynomial 0 6 := by
  rw [rawCoordinate_sparse 6 0 6 rawEntry_6_00_06 rawEntry_6_00_06_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_06)=_
  rw [rawEntry_6_00_06_coordinates]
  exact rawPlus_subst 0 6
theorem rawEntry_6_06_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 6 0=sparseCoefficient rawEntry_6_00_06 r := by decide +kernel
theorem rawEntry_6_06_00_physical : invariantSubst (rawCoordinate 6 6 0)=rawPlusPolynomial 6 0 := by
  have hh : rawCoordinate 6 6 0=rawCoordinate 6 0 6 := by
    rw [rawCoordinate_sparse 6 6 0 rawEntry_6_00_06 rawEntry_6_06_00_data,rawCoordinate_sparse 6 0 6 rawEntry_6_00_06 rawEntry_6_00_06_data]
  rw [hh,rawEntry_6_00_06_physical]
  exact rawPlusPolynomial_symm 0 6
def rawEntry_6_00_07 : SparseEntry := [(7,1)]
theorem rawEntry_6_00_07_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 7=sparseCoefficient rawEntry_6_00_07 r := by decide +kernel
theorem rawEntry_6_00_07_coordinates : sparsePolynomial 1 rawEntry_6_00_07=rawPlusCoordinates 0 7 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_07,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_07_physical : invariantSubst (rawCoordinate 6 0 7)=rawPlusPolynomial 0 7 := by
  rw [rawCoordinate_sparse 6 0 7 rawEntry_6_00_07 rawEntry_6_00_07_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_07)=_
  rw [rawEntry_6_00_07_coordinates]
  exact rawPlus_subst 0 7
theorem rawEntry_6_07_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 7 0=sparseCoefficient rawEntry_6_00_07 r := by decide +kernel
theorem rawEntry_6_07_00_physical : invariantSubst (rawCoordinate 6 7 0)=rawPlusPolynomial 7 0 := by
  have hh : rawCoordinate 6 7 0=rawCoordinate 6 0 7 := by
    rw [rawCoordinate_sparse 6 7 0 rawEntry_6_00_07 rawEntry_6_07_00_data,rawCoordinate_sparse 6 0 7 rawEntry_6_00_07 rawEntry_6_00_07_data]
  rw [hh,rawEntry_6_00_07_physical]
  exact rawPlusPolynomial_symm 0 7
def rawEntry_6_00_08 : SparseEntry := [(8,1)]
theorem rawEntry_6_00_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 8=sparseCoefficient rawEntry_6_00_08 r := by decide +kernel
theorem rawEntry_6_00_08_coordinates : sparsePolynomial 1 rawEntry_6_00_08=rawPlusCoordinates 0 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_08_physical : invariantSubst (rawCoordinate 6 0 8)=rawPlusPolynomial 0 8 := by
  rw [rawCoordinate_sparse 6 0 8 rawEntry_6_00_08 rawEntry_6_00_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_08)=_
  rw [rawEntry_6_00_08_coordinates]
  exact rawPlus_subst 0 8
theorem rawEntry_6_08_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 0=sparseCoefficient rawEntry_6_00_08 r := by decide +kernel
theorem rawEntry_6_08_00_physical : invariantSubst (rawCoordinate 6 8 0)=rawPlusPolynomial 8 0 := by
  have hh : rawCoordinate 6 8 0=rawCoordinate 6 0 8 := by
    rw [rawCoordinate_sparse 6 8 0 rawEntry_6_00_08 rawEntry_6_08_00_data,rawCoordinate_sparse 6 0 8 rawEntry_6_00_08 rawEntry_6_00_08_data]
  rw [hh,rawEntry_6_00_08_physical]
  exact rawPlusPolynomial_symm 0 8
def rawEntry_6_00_09 : SparseEntry := [(9,1)]
theorem rawEntry_6_00_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 9=sparseCoefficient rawEntry_6_00_09 r := by decide +kernel
theorem rawEntry_6_00_09_coordinates : sparsePolynomial 1 rawEntry_6_00_09=rawPlusCoordinates 0 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_09_physical : invariantSubst (rawCoordinate 6 0 9)=rawPlusPolynomial 0 9 := by
  rw [rawCoordinate_sparse 6 0 9 rawEntry_6_00_09 rawEntry_6_00_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_09)=_
  rw [rawEntry_6_00_09_coordinates]
  exact rawPlus_subst 0 9
theorem rawEntry_6_09_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 0=sparseCoefficient rawEntry_6_00_09 r := by decide +kernel
theorem rawEntry_6_09_00_physical : invariantSubst (rawCoordinate 6 9 0)=rawPlusPolynomial 9 0 := by
  have hh : rawCoordinate 6 9 0=rawCoordinate 6 0 9 := by
    rw [rawCoordinate_sparse 6 9 0 rawEntry_6_00_09 rawEntry_6_09_00_data,rawCoordinate_sparse 6 0 9 rawEntry_6_00_09 rawEntry_6_00_09_data]
  rw [hh,rawEntry_6_00_09_physical]
  exact rawPlusPolynomial_symm 0 9
def rawEntry_6_00_10 : SparseEntry := [(10,1)]
theorem rawEntry_6_00_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 10=sparseCoefficient rawEntry_6_00_10 r := by decide +kernel
theorem rawEntry_6_00_10_coordinates : sparsePolynomial 1 rawEntry_6_00_10=rawPlusCoordinates 0 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_10_physical : invariantSubst (rawCoordinate 6 0 10)=rawPlusPolynomial 0 10 := by
  rw [rawCoordinate_sparse 6 0 10 rawEntry_6_00_10 rawEntry_6_00_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_10)=_
  rw [rawEntry_6_00_10_coordinates]
  exact rawPlus_subst 0 10
theorem rawEntry_6_10_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 0=sparseCoefficient rawEntry_6_00_10 r := by decide +kernel
theorem rawEntry_6_10_00_physical : invariantSubst (rawCoordinate 6 10 0)=rawPlusPolynomial 10 0 := by
  have hh : rawCoordinate 6 10 0=rawCoordinate 6 0 10 := by
    rw [rawCoordinate_sparse 6 10 0 rawEntry_6_00_10 rawEntry_6_10_00_data,rawCoordinate_sparse 6 0 10 rawEntry_6_00_10 rawEntry_6_00_10_data]
  rw [hh,rawEntry_6_00_10_physical]
  exact rawPlusPolynomial_symm 0 10
def rawEntry_6_00_11 : SparseEntry := [(11,1)]
theorem rawEntry_6_00_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 11=sparseCoefficient rawEntry_6_00_11 r := by decide +kernel
theorem rawEntry_6_00_11_coordinates : sparsePolynomial 1 rawEntry_6_00_11=rawPlusCoordinates 0 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_11_physical : invariantSubst (rawCoordinate 6 0 11)=rawPlusPolynomial 0 11 := by
  rw [rawCoordinate_sparse 6 0 11 rawEntry_6_00_11 rawEntry_6_00_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_11)=_
  rw [rawEntry_6_00_11_coordinates]
  exact rawPlus_subst 0 11
theorem rawEntry_6_11_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 0=sparseCoefficient rawEntry_6_00_11 r := by decide +kernel
theorem rawEntry_6_11_00_physical : invariantSubst (rawCoordinate 6 11 0)=rawPlusPolynomial 11 0 := by
  have hh : rawCoordinate 6 11 0=rawCoordinate 6 0 11 := by
    rw [rawCoordinate_sparse 6 11 0 rawEntry_6_00_11 rawEntry_6_11_00_data,rawCoordinate_sparse 6 0 11 rawEntry_6_00_11 rawEntry_6_00_11_data]
  rw [hh,rawEntry_6_00_11_physical]
  exact rawPlusPolynomial_symm 0 11
def rawEntry_6_00_12 : SparseEntry := [(12,1)]
theorem rawEntry_6_00_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 12=sparseCoefficient rawEntry_6_00_12 r := by decide +kernel
theorem rawEntry_6_00_12_coordinates : sparsePolynomial 1 rawEntry_6_00_12=rawPlusCoordinates 0 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_12_physical : invariantSubst (rawCoordinate 6 0 12)=rawPlusPolynomial 0 12 := by
  rw [rawCoordinate_sparse 6 0 12 rawEntry_6_00_12 rawEntry_6_00_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_12)=_
  rw [rawEntry_6_00_12_coordinates]
  exact rawPlus_subst 0 12
theorem rawEntry_6_12_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 0=sparseCoefficient rawEntry_6_00_12 r := by decide +kernel
theorem rawEntry_6_12_00_physical : invariantSubst (rawCoordinate 6 12 0)=rawPlusPolynomial 12 0 := by
  have hh : rawCoordinate 6 12 0=rawCoordinate 6 0 12 := by
    rw [rawCoordinate_sparse 6 12 0 rawEntry_6_00_12 rawEntry_6_12_00_data,rawCoordinate_sparse 6 0 12 rawEntry_6_00_12 rawEntry_6_00_12_data]
  rw [hh,rawEntry_6_00_12_physical]
  exact rawPlusPolynomial_symm 0 12
def rawEntry_6_00_13 : SparseEntry := [(13,1)]
theorem rawEntry_6_00_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 13=sparseCoefficient rawEntry_6_00_13 r := by decide +kernel
theorem rawEntry_6_00_13_coordinates : sparsePolynomial 1 rawEntry_6_00_13=rawPlusCoordinates 0 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_13_physical : invariantSubst (rawCoordinate 6 0 13)=rawPlusPolynomial 0 13 := by
  rw [rawCoordinate_sparse 6 0 13 rawEntry_6_00_13 rawEntry_6_00_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_13)=_
  rw [rawEntry_6_00_13_coordinates]
  exact rawPlus_subst 0 13
theorem rawEntry_6_13_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 0=sparseCoefficient rawEntry_6_00_13 r := by decide +kernel
theorem rawEntry_6_13_00_physical : invariantSubst (rawCoordinate 6 13 0)=rawPlusPolynomial 13 0 := by
  have hh : rawCoordinate 6 13 0=rawCoordinate 6 0 13 := by
    rw [rawCoordinate_sparse 6 13 0 rawEntry_6_00_13 rawEntry_6_13_00_data,rawCoordinate_sparse 6 0 13 rawEntry_6_00_13 rawEntry_6_00_13_data]
  rw [hh,rawEntry_6_00_13_physical]
  exact rawPlusPolynomial_symm 0 13
def rawEntry_6_00_14 : SparseEntry := [(14,1)]
theorem rawEntry_6_00_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 14=sparseCoefficient rawEntry_6_00_14 r := by decide +kernel
theorem rawEntry_6_00_14_coordinates : sparsePolynomial 1 rawEntry_6_00_14=rawPlusCoordinates 0 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_14_physical : invariantSubst (rawCoordinate 6 0 14)=rawPlusPolynomial 0 14 := by
  rw [rawCoordinate_sparse 6 0 14 rawEntry_6_00_14 rawEntry_6_00_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_14)=_
  rw [rawEntry_6_00_14_coordinates]
  exact rawPlus_subst 0 14
theorem rawEntry_6_14_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 0=sparseCoefficient rawEntry_6_00_14 r := by decide +kernel
theorem rawEntry_6_14_00_physical : invariantSubst (rawCoordinate 6 14 0)=rawPlusPolynomial 14 0 := by
  have hh : rawCoordinate 6 14 0=rawCoordinate 6 0 14 := by
    rw [rawCoordinate_sparse 6 14 0 rawEntry_6_00_14 rawEntry_6_14_00_data,rawCoordinate_sparse 6 0 14 rawEntry_6_00_14 rawEntry_6_00_14_data]
  rw [hh,rawEntry_6_00_14_physical]
  exact rawPlusPolynomial_symm 0 14
def rawEntry_6_00_15 : SparseEntry := [(15,1)]
theorem rawEntry_6_00_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 0 15=sparseCoefficient rawEntry_6_00_15 r := by decide +kernel
theorem rawEntry_6_00_15_coordinates : sparsePolynomial 1 rawEntry_6_00_15=rawPlusCoordinates 0 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_00_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_00_15_physical : invariantSubst (rawCoordinate 6 0 15)=rawPlusPolynomial 0 15 := by
  rw [rawCoordinate_sparse 6 0 15 rawEntry_6_00_15 rawEntry_6_00_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_00_15)=_
  rw [rawEntry_6_00_15_coordinates]
  exact rawPlus_subst 0 15
theorem rawEntry_6_15_00_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 0=sparseCoefficient rawEntry_6_00_15 r := by decide +kernel
theorem rawEntry_6_15_00_physical : invariantSubst (rawCoordinate 6 15 0)=rawPlusPolynomial 15 0 := by
  have hh : rawCoordinate 6 15 0=rawCoordinate 6 0 15 := by
    rw [rawCoordinate_sparse 6 15 0 rawEntry_6_00_15 rawEntry_6_15_00_data,rawCoordinate_sparse 6 0 15 rawEntry_6_00_15 rawEntry_6_00_15_data]
  rw [hh,rawEntry_6_00_15_physical]
  exact rawPlusPolynomial_symm 0 15
def rawEntry_6_01_01 : SparseEntry := [(3,1)]
theorem rawEntry_6_01_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 1=sparseCoefficient rawEntry_6_01_01 r := by decide +kernel
theorem rawEntry_6_01_01_coordinates : sparsePolynomial 1 rawEntry_6_01_01=rawPlusCoordinates 1 1 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_01,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_01_physical : invariantSubst (rawCoordinate 6 1 1)=rawPlusPolynomial 1 1 := by
  rw [rawCoordinate_sparse 6 1 1 rawEntry_6_01_01 rawEntry_6_01_01_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_01)=_
  rw [rawEntry_6_01_01_coordinates]
  exact rawPlus_subst 1 1
def rawEntry_6_01_02 : SparseEntry := [(5,1)]
theorem rawEntry_6_01_02_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 2=sparseCoefficient rawEntry_6_01_02 r := by decide +kernel
theorem rawEntry_6_01_02_coordinates : sparsePolynomial 1 rawEntry_6_01_02=rawPlusCoordinates 1 2 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_02,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_02_physical : invariantSubst (rawCoordinate 6 1 2)=rawPlusPolynomial 1 2 := by
  rw [rawCoordinate_sparse 6 1 2 rawEntry_6_01_02 rawEntry_6_01_02_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_02)=_
  rw [rawEntry_6_01_02_coordinates]
  exact rawPlus_subst 1 2
theorem rawEntry_6_02_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 2 1=sparseCoefficient rawEntry_6_01_02 r := by decide +kernel
theorem rawEntry_6_02_01_physical : invariantSubst (rawCoordinate 6 2 1)=rawPlusPolynomial 2 1 := by
  have hh : rawCoordinate 6 2 1=rawCoordinate 6 1 2 := by
    rw [rawCoordinate_sparse 6 2 1 rawEntry_6_01_02 rawEntry_6_02_01_data,rawCoordinate_sparse 6 1 2 rawEntry_6_01_02 rawEntry_6_01_02_data]
  rw [hh,rawEntry_6_01_02_physical]
  exact rawPlusPolynomial_symm 1 2
def rawEntry_6_01_03 : SparseEntry := [(6,1)]
theorem rawEntry_6_01_03_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 3=sparseCoefficient rawEntry_6_01_03 r := by decide +kernel
theorem rawEntry_6_01_03_coordinates : sparsePolynomial 1 rawEntry_6_01_03=rawPlusCoordinates 1 3 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_03,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_03_physical : invariantSubst (rawCoordinate 6 1 3)=rawPlusPolynomial 1 3 := by
  rw [rawCoordinate_sparse 6 1 3 rawEntry_6_01_03 rawEntry_6_01_03_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_03)=_
  rw [rawEntry_6_01_03_coordinates]
  exact rawPlus_subst 1 3
theorem rawEntry_6_03_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 3 1=sparseCoefficient rawEntry_6_01_03 r := by decide +kernel
theorem rawEntry_6_03_01_physical : invariantSubst (rawCoordinate 6 3 1)=rawPlusPolynomial 3 1 := by
  have hh : rawCoordinate 6 3 1=rawCoordinate 6 1 3 := by
    rw [rawCoordinate_sparse 6 3 1 rawEntry_6_01_03 rawEntry_6_03_01_data,rawCoordinate_sparse 6 1 3 rawEntry_6_01_03 rawEntry_6_01_03_data]
  rw [hh,rawEntry_6_01_03_physical]
  exact rawPlusPolynomial_symm 1 3
def rawEntry_6_01_04 : SparseEntry := [(8,1)]
theorem rawEntry_6_01_04_data : ∀r : Fin 102, RawData.coefficient 6 r.val 1 4=sparseCoefficient rawEntry_6_01_04 r := by decide +kernel
theorem rawEntry_6_01_04_coordinates : sparsePolynomial 1 rawEntry_6_01_04=rawPlusCoordinates 1 4 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_01_04,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_01_04_physical : invariantSubst (rawCoordinate 6 1 4)=rawPlusPolynomial 1 4 := by
  rw [rawCoordinate_sparse 6 1 4 rawEntry_6_01_04 rawEntry_6_01_04_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_01_04)=_
  rw [rawEntry_6_01_04_coordinates]
  exact rawPlus_subst 1 4
theorem rawEntry_6_04_01_data : ∀r : Fin 102, RawData.coefficient 6 r.val 4 1=sparseCoefficient rawEntry_6_01_04 r := by decide +kernel
theorem rawEntry_6_04_01_physical : invariantSubst (rawCoordinate 6 4 1)=rawPlusPolynomial 4 1 := by
  have hh : rawCoordinate 6 4 1=rawCoordinate 6 1 4 := by
    rw [rawCoordinate_sparse 6 4 1 rawEntry_6_01_04 rawEntry_6_04_01_data,rawCoordinate_sparse 6 1 4 rawEntry_6_01_04 rawEntry_6_01_04_data]
  rw [hh,rawEntry_6_01_04_physical]
  exact rawPlusPolynomial_symm 1 4
end ThomsonNegative.Certificate.Bridges
