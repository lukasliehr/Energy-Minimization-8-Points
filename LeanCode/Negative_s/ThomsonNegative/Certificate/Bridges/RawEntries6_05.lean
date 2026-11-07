import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_08_08 : SparseEntry := [(34,1)]
theorem rawEntry_6_08_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 8=sparseCoefficient rawEntry_6_08_08 r := by decide +kernel
theorem rawEntry_6_08_08_coordinates : sparsePolynomial 1 rawEntry_6_08_08=rawPlusCoordinates 8 8 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_08,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_08_physical : invariantSubst (rawCoordinate 6 8 8)=rawPlusPolynomial 8 8 := by
  rw [rawCoordinate_sparse 6 8 8 rawEntry_6_08_08 rawEntry_6_08_08_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_08)=_
  rw [rawEntry_6_08_08_coordinates]
  exact rawPlus_subst 8 8
def rawEntry_6_08_09 : SparseEntry := [(36,1)]
theorem rawEntry_6_08_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 9=sparseCoefficient rawEntry_6_08_09 r := by decide +kernel
theorem rawEntry_6_08_09_coordinates : sparsePolynomial 1 rawEntry_6_08_09=rawPlusCoordinates 8 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_09_physical : invariantSubst (rawCoordinate 6 8 9)=rawPlusPolynomial 8 9 := by
  rw [rawCoordinate_sparse 6 8 9 rawEntry_6_08_09 rawEntry_6_08_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_09)=_
  rw [rawEntry_6_08_09_coordinates]
  exact rawPlus_subst 8 9
theorem rawEntry_6_09_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 8=sparseCoefficient rawEntry_6_08_09 r := by decide +kernel
theorem rawEntry_6_09_08_physical : invariantSubst (rawCoordinate 6 9 8)=rawPlusPolynomial 9 8 := by
  have hh : rawCoordinate 6 9 8=rawCoordinate 6 8 9 := by
    rw [rawCoordinate_sparse 6 9 8 rawEntry_6_08_09 rawEntry_6_09_08_data,rawCoordinate_sparse 6 8 9 rawEntry_6_08_09 rawEntry_6_08_09_data]
  rw [hh,rawEntry_6_08_09_physical]
  exact rawPlusPolynomial_symm 8 9
def rawEntry_6_08_10 : SparseEntry := [(38,1)]
theorem rawEntry_6_08_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 10=sparseCoefficient rawEntry_6_08_10 r := by decide +kernel
theorem rawEntry_6_08_10_coordinates : sparsePolynomial 1 rawEntry_6_08_10=rawPlusCoordinates 8 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_10_physical : invariantSubst (rawCoordinate 6 8 10)=rawPlusPolynomial 8 10 := by
  rw [rawCoordinate_sparse 6 8 10 rawEntry_6_08_10 rawEntry_6_08_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_10)=_
  rw [rawEntry_6_08_10_coordinates]
  exact rawPlus_subst 8 10
theorem rawEntry_6_10_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 8=sparseCoefficient rawEntry_6_08_10 r := by decide +kernel
theorem rawEntry_6_10_08_physical : invariantSubst (rawCoordinate 6 10 8)=rawPlusPolynomial 10 8 := by
  have hh : rawCoordinate 6 10 8=rawCoordinate 6 8 10 := by
    rw [rawCoordinate_sparse 6 10 8 rawEntry_6_08_10 rawEntry_6_10_08_data,rawCoordinate_sparse 6 8 10 rawEntry_6_08_10 rawEntry_6_08_10_data]
  rw [hh,rawEntry_6_08_10_physical]
  exact rawPlusPolynomial_symm 8 10
def rawEntry_6_08_11 : SparseEntry := [(43,1)]
theorem rawEntry_6_08_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 11=sparseCoefficient rawEntry_6_08_11 r := by decide +kernel
theorem rawEntry_6_08_11_coordinates : sparsePolynomial 1 rawEntry_6_08_11=rawPlusCoordinates 8 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_11_physical : invariantSubst (rawCoordinate 6 8 11)=rawPlusPolynomial 8 11 := by
  rw [rawCoordinate_sparse 6 8 11 rawEntry_6_08_11 rawEntry_6_08_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_11)=_
  rw [rawEntry_6_08_11_coordinates]
  exact rawPlus_subst 8 11
theorem rawEntry_6_11_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 8=sparseCoefficient rawEntry_6_08_11 r := by decide +kernel
theorem rawEntry_6_11_08_physical : invariantSubst (rawCoordinate 6 11 8)=rawPlusPolynomial 11 8 := by
  have hh : rawCoordinate 6 11 8=rawCoordinate 6 8 11 := by
    rw [rawCoordinate_sparse 6 11 8 rawEntry_6_08_11 rawEntry_6_11_08_data,rawCoordinate_sparse 6 8 11 rawEntry_6_08_11 rawEntry_6_08_11_data]
  rw [hh,rawEntry_6_08_11_physical]
  exact rawPlusPolynomial_symm 8 11
def rawEntry_6_08_12 : SparseEntry := [(45,1)]
theorem rawEntry_6_08_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 12=sparseCoefficient rawEntry_6_08_12 r := by decide +kernel
theorem rawEntry_6_08_12_coordinates : sparsePolynomial 1 rawEntry_6_08_12=rawPlusCoordinates 8 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_12_physical : invariantSubst (rawCoordinate 6 8 12)=rawPlusPolynomial 8 12 := by
  rw [rawCoordinate_sparse 6 8 12 rawEntry_6_08_12 rawEntry_6_08_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_12)=_
  rw [rawEntry_6_08_12_coordinates]
  exact rawPlus_subst 8 12
theorem rawEntry_6_12_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 8=sparseCoefficient rawEntry_6_08_12 r := by decide +kernel
theorem rawEntry_6_12_08_physical : invariantSubst (rawCoordinate 6 12 8)=rawPlusPolynomial 12 8 := by
  have hh : rawCoordinate 6 12 8=rawCoordinate 6 8 12 := by
    rw [rawCoordinate_sparse 6 12 8 rawEntry_6_08_12 rawEntry_6_12_08_data,rawCoordinate_sparse 6 8 12 rawEntry_6_08_12 rawEntry_6_08_12_data]
  rw [hh,rawEntry_6_08_12_physical]
  exact rawPlusPolynomial_symm 8 12
def rawEntry_6_08_13 : SparseEntry := [(46,1)]
theorem rawEntry_6_08_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 13=sparseCoefficient rawEntry_6_08_13 r := by decide +kernel
theorem rawEntry_6_08_13_coordinates : sparsePolynomial 1 rawEntry_6_08_13=rawPlusCoordinates 8 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_13_physical : invariantSubst (rawCoordinate 6 8 13)=rawPlusPolynomial 8 13 := by
  rw [rawCoordinate_sparse 6 8 13 rawEntry_6_08_13 rawEntry_6_08_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_13)=_
  rw [rawEntry_6_08_13_coordinates]
  exact rawPlus_subst 8 13
theorem rawEntry_6_13_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 8=sparseCoefficient rawEntry_6_08_13 r := by decide +kernel
theorem rawEntry_6_13_08_physical : invariantSubst (rawCoordinate 6 13 8)=rawPlusPolynomial 13 8 := by
  have hh : rawCoordinate 6 13 8=rawCoordinate 6 8 13 := by
    rw [rawCoordinate_sparse 6 13 8 rawEntry_6_08_13 rawEntry_6_13_08_data,rawCoordinate_sparse 6 8 13 rawEntry_6_08_13 rawEntry_6_08_13_data]
  rw [hh,rawEntry_6_08_13_physical]
  exact rawPlusPolynomial_symm 8 13
def rawEntry_6_08_14 : SparseEntry := [(48,1)]
theorem rawEntry_6_08_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 14=sparseCoefficient rawEntry_6_08_14 r := by decide +kernel
theorem rawEntry_6_08_14_coordinates : sparsePolynomial 1 rawEntry_6_08_14=rawPlusCoordinates 8 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_14_physical : invariantSubst (rawCoordinate 6 8 14)=rawPlusPolynomial 8 14 := by
  rw [rawCoordinate_sparse 6 8 14 rawEntry_6_08_14 rawEntry_6_08_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_14)=_
  rw [rawEntry_6_08_14_coordinates]
  exact rawPlus_subst 8 14
theorem rawEntry_6_14_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 8=sparseCoefficient rawEntry_6_08_14 r := by decide +kernel
theorem rawEntry_6_14_08_physical : invariantSubst (rawCoordinate 6 14 8)=rawPlusPolynomial 14 8 := by
  have hh : rawCoordinate 6 14 8=rawCoordinate 6 8 14 := by
    rw [rawCoordinate_sparse 6 14 8 rawEntry_6_08_14 rawEntry_6_14_08_data,rawCoordinate_sparse 6 8 14 rawEntry_6_08_14 rawEntry_6_08_14_data]
  rw [hh,rawEntry_6_08_14_physical]
  exact rawPlusPolynomial_symm 8 14
def rawEntry_6_08_15 : SparseEntry := [(50,1)]
theorem rawEntry_6_08_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 8 15=sparseCoefficient rawEntry_6_08_15 r := by decide +kernel
theorem rawEntry_6_08_15_coordinates : sparsePolynomial 1 rawEntry_6_08_15=rawPlusCoordinates 8 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_08_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_08_15_physical : invariantSubst (rawCoordinate 6 8 15)=rawPlusPolynomial 8 15 := by
  rw [rawCoordinate_sparse 6 8 15 rawEntry_6_08_15 rawEntry_6_08_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_08_15)=_
  rw [rawEntry_6_08_15_coordinates]
  exact rawPlus_subst 8 15
theorem rawEntry_6_15_08_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 8=sparseCoefficient rawEntry_6_08_15 r := by decide +kernel
theorem rawEntry_6_15_08_physical : invariantSubst (rawCoordinate 6 15 8)=rawPlusPolynomial 15 8 := by
  have hh : rawCoordinate 6 15 8=rawCoordinate 6 8 15 := by
    rw [rawCoordinate_sparse 6 15 8 rawEntry_6_08_15 rawEntry_6_15_08_data,rawCoordinate_sparse 6 8 15 rawEntry_6_08_15 rawEntry_6_08_15_data]
  rw [hh,rawEntry_6_08_15_physical]
  exact rawPlusPolynomial_symm 8 15
def rawEntry_6_09_09 : SparseEntry := [(37,1)]
theorem rawEntry_6_09_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 9=sparseCoefficient rawEntry_6_09_09 r := by decide +kernel
theorem rawEntry_6_09_09_coordinates : sparsePolynomial 1 rawEntry_6_09_09=rawPlusCoordinates 9 9 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_09,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_09_physical : invariantSubst (rawCoordinate 6 9 9)=rawPlusPolynomial 9 9 := by
  rw [rawCoordinate_sparse 6 9 9 rawEntry_6_09_09 rawEntry_6_09_09_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_09)=_
  rw [rawEntry_6_09_09_coordinates]
  exact rawPlus_subst 9 9
def rawEntry_6_09_10 : SparseEntry := [(39,1)]
theorem rawEntry_6_09_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 10=sparseCoefficient rawEntry_6_09_10 r := by decide +kernel
theorem rawEntry_6_09_10_coordinates : sparsePolynomial 1 rawEntry_6_09_10=rawPlusCoordinates 9 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_10_physical : invariantSubst (rawCoordinate 6 9 10)=rawPlusPolynomial 9 10 := by
  rw [rawCoordinate_sparse 6 9 10 rawEntry_6_09_10 rawEntry_6_09_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_10)=_
  rw [rawEntry_6_09_10_coordinates]
  exact rawPlus_subst 9 10
theorem rawEntry_6_10_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 9=sparseCoefficient rawEntry_6_09_10 r := by decide +kernel
theorem rawEntry_6_10_09_physical : invariantSubst (rawCoordinate 6 10 9)=rawPlusPolynomial 10 9 := by
  have hh : rawCoordinate 6 10 9=rawCoordinate 6 9 10 := by
    rw [rawCoordinate_sparse 6 10 9 rawEntry_6_09_10 rawEntry_6_10_09_data,rawCoordinate_sparse 6 9 10 rawEntry_6_09_10 rawEntry_6_09_10_data]
  rw [hh,rawEntry_6_09_10_physical]
  exact rawPlusPolynomial_symm 9 10
def rawEntry_6_09_11 : SparseEntry := [(45,1)]
theorem rawEntry_6_09_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 11=sparseCoefficient rawEntry_6_09_11 r := by decide +kernel
theorem rawEntry_6_09_11_coordinates : sparsePolynomial 1 rawEntry_6_09_11=rawPlusCoordinates 9 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_11_physical : invariantSubst (rawCoordinate 6 9 11)=rawPlusPolynomial 9 11 := by
  rw [rawCoordinate_sparse 6 9 11 rawEntry_6_09_11 rawEntry_6_09_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_11)=_
  rw [rawEntry_6_09_11_coordinates]
  exact rawPlus_subst 9 11
theorem rawEntry_6_11_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 9=sparseCoefficient rawEntry_6_09_11 r := by decide +kernel
theorem rawEntry_6_11_09_physical : invariantSubst (rawCoordinate 6 11 9)=rawPlusPolynomial 11 9 := by
  have hh : rawCoordinate 6 11 9=rawCoordinate 6 9 11 := by
    rw [rawCoordinate_sparse 6 11 9 rawEntry_6_09_11 rawEntry_6_11_09_data,rawCoordinate_sparse 6 9 11 rawEntry_6_09_11 rawEntry_6_09_11_data]
  rw [hh,rawEntry_6_09_11_physical]
  exact rawPlusPolynomial_symm 9 11
def rawEntry_6_09_12 : SparseEntry := [(47,1)]
theorem rawEntry_6_09_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 12=sparseCoefficient rawEntry_6_09_12 r := by decide +kernel
theorem rawEntry_6_09_12_coordinates : sparsePolynomial 1 rawEntry_6_09_12=rawPlusCoordinates 9 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_12_physical : invariantSubst (rawCoordinate 6 9 12)=rawPlusPolynomial 9 12 := by
  rw [rawCoordinate_sparse 6 9 12 rawEntry_6_09_12 rawEntry_6_09_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_12)=_
  rw [rawEntry_6_09_12_coordinates]
  exact rawPlus_subst 9 12
theorem rawEntry_6_12_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 9=sparseCoefficient rawEntry_6_09_12 r := by decide +kernel
theorem rawEntry_6_12_09_physical : invariantSubst (rawCoordinate 6 12 9)=rawPlusPolynomial 12 9 := by
  have hh : rawCoordinate 6 12 9=rawCoordinate 6 9 12 := by
    rw [rawCoordinate_sparse 6 12 9 rawEntry_6_09_12 rawEntry_6_12_09_data,rawCoordinate_sparse 6 9 12 rawEntry_6_09_12 rawEntry_6_09_12_data]
  rw [hh,rawEntry_6_09_12_physical]
  exact rawPlusPolynomial_symm 9 12
def rawEntry_6_09_13 : SparseEntry := [(48,1)]
theorem rawEntry_6_09_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 13=sparseCoefficient rawEntry_6_09_13 r := by decide +kernel
theorem rawEntry_6_09_13_coordinates : sparsePolynomial 1 rawEntry_6_09_13=rawPlusCoordinates 9 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_13_physical : invariantSubst (rawCoordinate 6 9 13)=rawPlusPolynomial 9 13 := by
  rw [rawCoordinate_sparse 6 9 13 rawEntry_6_09_13 rawEntry_6_09_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_13)=_
  rw [rawEntry_6_09_13_coordinates]
  exact rawPlus_subst 9 13
theorem rawEntry_6_13_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 9=sparseCoefficient rawEntry_6_09_13 r := by decide +kernel
theorem rawEntry_6_13_09_physical : invariantSubst (rawCoordinate 6 13 9)=rawPlusPolynomial 13 9 := by
  have hh : rawCoordinate 6 13 9=rawCoordinate 6 9 13 := by
    rw [rawCoordinate_sparse 6 13 9 rawEntry_6_09_13 rawEntry_6_13_09_data,rawCoordinate_sparse 6 9 13 rawEntry_6_09_13 rawEntry_6_09_13_data]
  rw [hh,rawEntry_6_09_13_physical]
  exact rawPlusPolynomial_symm 9 13
def rawEntry_6_09_14 : SparseEntry := [(49,1)]
theorem rawEntry_6_09_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 14=sparseCoefficient rawEntry_6_09_14 r := by decide +kernel
theorem rawEntry_6_09_14_coordinates : sparsePolynomial 1 rawEntry_6_09_14=rawPlusCoordinates 9 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_14_physical : invariantSubst (rawCoordinate 6 9 14)=rawPlusPolynomial 9 14 := by
  rw [rawCoordinate_sparse 6 9 14 rawEntry_6_09_14 rawEntry_6_09_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_14)=_
  rw [rawEntry_6_09_14_coordinates]
  exact rawPlus_subst 9 14
theorem rawEntry_6_14_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 9=sparseCoefficient rawEntry_6_09_14 r := by decide +kernel
theorem rawEntry_6_14_09_physical : invariantSubst (rawCoordinate 6 14 9)=rawPlusPolynomial 14 9 := by
  have hh : rawCoordinate 6 14 9=rawCoordinate 6 9 14 := by
    rw [rawCoordinate_sparse 6 14 9 rawEntry_6_09_14 rawEntry_6_14_09_data,rawCoordinate_sparse 6 9 14 rawEntry_6_09_14 rawEntry_6_09_14_data]
  rw [hh,rawEntry_6_09_14_physical]
  exact rawPlusPolynomial_symm 9 14
def rawEntry_6_09_15 : SparseEntry := [(51,1)]
theorem rawEntry_6_09_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 9 15=sparseCoefficient rawEntry_6_09_15 r := by decide +kernel
theorem rawEntry_6_09_15_coordinates : sparsePolynomial 1 rawEntry_6_09_15=rawPlusCoordinates 9 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_09_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_09_15_physical : invariantSubst (rawCoordinate 6 9 15)=rawPlusPolynomial 9 15 := by
  rw [rawCoordinate_sparse 6 9 15 rawEntry_6_09_15 rawEntry_6_09_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_09_15)=_
  rw [rawEntry_6_09_15_coordinates]
  exact rawPlus_subst 9 15
theorem rawEntry_6_15_09_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 9=sparseCoefficient rawEntry_6_09_15 r := by decide +kernel
theorem rawEntry_6_15_09_physical : invariantSubst (rawCoordinate 6 15 9)=rawPlusPolynomial 15 9 := by
  have hh : rawCoordinate 6 15 9=rawCoordinate 6 9 15 := by
    rw [rawCoordinate_sparse 6 15 9 rawEntry_6_09_15 rawEntry_6_15_09_data,rawCoordinate_sparse 6 9 15 rawEntry_6_09_15 rawEntry_6_09_15_data]
  rw [hh,rawEntry_6_09_15_physical]
  exact rawPlusPolynomial_symm 9 15
def rawEntry_6_10_10 : SparseEntry := [(40,1)]
theorem rawEntry_6_10_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 10=sparseCoefficient rawEntry_6_10_10 r := by decide +kernel
theorem rawEntry_6_10_10_coordinates : sparsePolynomial 1 rawEntry_6_10_10=rawPlusCoordinates 10 10 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_10,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_10_physical : invariantSubst (rawCoordinate 6 10 10)=rawPlusPolynomial 10 10 := by
  rw [rawCoordinate_sparse 6 10 10 rawEntry_6_10_10 rawEntry_6_10_10_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_10)=_
  rw [rawEntry_6_10_10_coordinates]
  exact rawPlus_subst 10 10
def rawEntry_6_10_11 : SparseEntry := [(48,1)]
theorem rawEntry_6_10_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 11=sparseCoefficient rawEntry_6_10_11 r := by decide +kernel
theorem rawEntry_6_10_11_coordinates : sparsePolynomial 1 rawEntry_6_10_11=rawPlusCoordinates 10 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_11_physical : invariantSubst (rawCoordinate 6 10 11)=rawPlusPolynomial 10 11 := by
  rw [rawCoordinate_sparse 6 10 11 rawEntry_6_10_11 rawEntry_6_10_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_11)=_
  rw [rawEntry_6_10_11_coordinates]
  exact rawPlus_subst 10 11
theorem rawEntry_6_11_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 10=sparseCoefficient rawEntry_6_10_11 r := by decide +kernel
theorem rawEntry_6_11_10_physical : invariantSubst (rawCoordinate 6 11 10)=rawPlusPolynomial 11 10 := by
  have hh : rawCoordinate 6 11 10=rawCoordinate 6 10 11 := by
    rw [rawCoordinate_sparse 6 11 10 rawEntry_6_10_11 rawEntry_6_11_10_data,rawCoordinate_sparse 6 10 11 rawEntry_6_10_11 rawEntry_6_10_11_data]
  rw [hh,rawEntry_6_10_11_physical]
  exact rawPlusPolynomial_symm 10 11
def rawEntry_6_10_12 : SparseEntry := [(49,1)]
theorem rawEntry_6_10_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 12=sparseCoefficient rawEntry_6_10_12 r := by decide +kernel
theorem rawEntry_6_10_12_coordinates : sparsePolynomial 1 rawEntry_6_10_12=rawPlusCoordinates 10 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_12_physical : invariantSubst (rawCoordinate 6 10 12)=rawPlusPolynomial 10 12 := by
  rw [rawCoordinate_sparse 6 10 12 rawEntry_6_10_12 rawEntry_6_10_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_12)=_
  rw [rawEntry_6_10_12_coordinates]
  exact rawPlus_subst 10 12
theorem rawEntry_6_12_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 10=sparseCoefficient rawEntry_6_10_12 r := by decide +kernel
theorem rawEntry_6_12_10_physical : invariantSubst (rawCoordinate 6 12 10)=rawPlusPolynomial 12 10 := by
  have hh : rawCoordinate 6 12 10=rawCoordinate 6 10 12 := by
    rw [rawCoordinate_sparse 6 12 10 rawEntry_6_10_12 rawEntry_6_12_10_data,rawCoordinate_sparse 6 10 12 rawEntry_6_10_12 rawEntry_6_10_12_data]
  rw [hh,rawEntry_6_10_12_physical]
  exact rawPlusPolynomial_symm 10 12
def rawEntry_6_10_13 : SparseEntry := [(50,1)]
theorem rawEntry_6_10_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 13=sparseCoefficient rawEntry_6_10_13 r := by decide +kernel
theorem rawEntry_6_10_13_coordinates : sparsePolynomial 1 rawEntry_6_10_13=rawPlusCoordinates 10 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_13_physical : invariantSubst (rawCoordinate 6 10 13)=rawPlusPolynomial 10 13 := by
  rw [rawCoordinate_sparse 6 10 13 rawEntry_6_10_13 rawEntry_6_10_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_13)=_
  rw [rawEntry_6_10_13_coordinates]
  exact rawPlus_subst 10 13
theorem rawEntry_6_13_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 10=sparseCoefficient rawEntry_6_10_13 r := by decide +kernel
theorem rawEntry_6_13_10_physical : invariantSubst (rawCoordinate 6 13 10)=rawPlusPolynomial 13 10 := by
  have hh : rawCoordinate 6 13 10=rawCoordinate 6 10 13 := by
    rw [rawCoordinate_sparse 6 13 10 rawEntry_6_10_13 rawEntry_6_13_10_data,rawCoordinate_sparse 6 10 13 rawEntry_6_10_13 rawEntry_6_10_13_data]
  rw [hh,rawEntry_6_10_13_physical]
  exact rawPlusPolynomial_symm 10 13
def rawEntry_6_10_14 : SparseEntry := [(51,1)]
theorem rawEntry_6_10_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 14=sparseCoefficient rawEntry_6_10_14 r := by decide +kernel
theorem rawEntry_6_10_14_coordinates : sparsePolynomial 1 rawEntry_6_10_14=rawPlusCoordinates 10 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_14_physical : invariantSubst (rawCoordinate 6 10 14)=rawPlusPolynomial 10 14 := by
  rw [rawCoordinate_sparse 6 10 14 rawEntry_6_10_14 rawEntry_6_10_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_14)=_
  rw [rawEntry_6_10_14_coordinates]
  exact rawPlus_subst 10 14
theorem rawEntry_6_14_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 10=sparseCoefficient rawEntry_6_10_14 r := by decide +kernel
theorem rawEntry_6_14_10_physical : invariantSubst (rawCoordinate 6 14 10)=rawPlusPolynomial 14 10 := by
  have hh : rawCoordinate 6 14 10=rawCoordinate 6 10 14 := by
    rw [rawCoordinate_sparse 6 14 10 rawEntry_6_10_14 rawEntry_6_14_10_data,rawCoordinate_sparse 6 10 14 rawEntry_6_10_14 rawEntry_6_10_14_data]
  rw [hh,rawEntry_6_10_14_physical]
  exact rawPlusPolynomial_symm 10 14
end ThomsonNegative.Certificate.Bridges
