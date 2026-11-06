import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.RawSymmetry
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option linter.unusedSimpArgs false
def rawEntry_6_10_15 : SparseEntry := [(52,1)]
theorem rawEntry_6_10_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 10 15=sparseCoefficient rawEntry_6_10_15 r := by decide +kernel
theorem rawEntry_6_10_15_coordinates : sparsePolynomial 1 rawEntry_6_10_15=rawPlusCoordinates 10 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_10_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_10_15_physical : invariantSubst (rawCoordinate 6 10 15)=rawPlusPolynomial 10 15 := by
  rw [rawCoordinate_sparse 6 10 15 rawEntry_6_10_15 rawEntry_6_10_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_10_15)=_
  rw [rawEntry_6_10_15_coordinates]
  exact rawPlus_subst 10 15
theorem rawEntry_6_15_10_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 10=sparseCoefficient rawEntry_6_10_15 r := by decide +kernel
theorem rawEntry_6_15_10_physical : invariantSubst (rawCoordinate 6 15 10)=rawPlusPolynomial 15 10 := by
  have hh : rawCoordinate 6 15 10=rawCoordinate 6 10 15 := by
    rw [rawCoordinate_sparse 6 15 10 rawEntry_6_10_15 rawEntry_6_15_10_data,rawCoordinate_sparse 6 10 15 rawEntry_6_10_15 rawEntry_6_10_15_data]
  rw [hh,rawEntry_6_10_15_physical]
  exact rawPlusPolynomial_symm 10 15
def rawEntry_6_11_11 : SparseEntry := [(53,1)]
theorem rawEntry_6_11_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 11=sparseCoefficient rawEntry_6_11_11 r := by decide +kernel
theorem rawEntry_6_11_11_coordinates : sparsePolynomial 1 rawEntry_6_11_11=rawPlusCoordinates 11 11 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_11_11,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_11_11_physical : invariantSubst (rawCoordinate 6 11 11)=rawPlusPolynomial 11 11 := by
  rw [rawCoordinate_sparse 6 11 11 rawEntry_6_11_11 rawEntry_6_11_11_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_11_11)=_
  rw [rawEntry_6_11_11_coordinates]
  exact rawPlus_subst 11 11
def rawEntry_6_11_12 : SparseEntry := [(56,1)]
theorem rawEntry_6_11_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 12=sparseCoefficient rawEntry_6_11_12 r := by decide +kernel
theorem rawEntry_6_11_12_coordinates : sparsePolynomial 1 rawEntry_6_11_12=rawPlusCoordinates 11 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_11_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_11_12_physical : invariantSubst (rawCoordinate 6 11 12)=rawPlusPolynomial 11 12 := by
  rw [rawCoordinate_sparse 6 11 12 rawEntry_6_11_12 rawEntry_6_11_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_11_12)=_
  rw [rawEntry_6_11_12_coordinates]
  exact rawPlus_subst 11 12
theorem rawEntry_6_12_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 11=sparseCoefficient rawEntry_6_11_12 r := by decide +kernel
theorem rawEntry_6_12_11_physical : invariantSubst (rawCoordinate 6 12 11)=rawPlusPolynomial 12 11 := by
  have hh : rawCoordinate 6 12 11=rawCoordinate 6 11 12 := by
    rw [rawCoordinate_sparse 6 12 11 rawEntry_6_11_12 rawEntry_6_12_11_data,rawCoordinate_sparse 6 11 12 rawEntry_6_11_12 rawEntry_6_11_12_data]
  rw [hh,rawEntry_6_11_12_physical]
  exact rawPlusPolynomial_symm 11 12
def rawEntry_6_11_13 : SparseEntry := [(57,1)]
theorem rawEntry_6_11_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 13=sparseCoefficient rawEntry_6_11_13 r := by decide +kernel
theorem rawEntry_6_11_13_coordinates : sparsePolynomial 1 rawEntry_6_11_13=rawPlusCoordinates 11 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_11_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_11_13_physical : invariantSubst (rawCoordinate 6 11 13)=rawPlusPolynomial 11 13 := by
  rw [rawCoordinate_sparse 6 11 13 rawEntry_6_11_13 rawEntry_6_11_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_11_13)=_
  rw [rawEntry_6_11_13_coordinates]
  exact rawPlus_subst 11 13
theorem rawEntry_6_13_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 11=sparseCoefficient rawEntry_6_11_13 r := by decide +kernel
theorem rawEntry_6_13_11_physical : invariantSubst (rawCoordinate 6 13 11)=rawPlusPolynomial 13 11 := by
  have hh : rawCoordinate 6 13 11=rawCoordinate 6 11 13 := by
    rw [rawCoordinate_sparse 6 13 11 rawEntry_6_11_13 rawEntry_6_13_11_data,rawCoordinate_sparse 6 11 13 rawEntry_6_11_13 rawEntry_6_11_13_data]
  rw [hh,rawEntry_6_11_13_physical]
  exact rawPlusPolynomial_symm 11 13
def rawEntry_6_11_14 : SparseEntry := [(59,1)]
theorem rawEntry_6_11_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 14=sparseCoefficient rawEntry_6_11_14 r := by decide +kernel
theorem rawEntry_6_11_14_coordinates : sparsePolynomial 1 rawEntry_6_11_14=rawPlusCoordinates 11 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_11_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_11_14_physical : invariantSubst (rawCoordinate 6 11 14)=rawPlusPolynomial 11 14 := by
  rw [rawCoordinate_sparse 6 11 14 rawEntry_6_11_14 rawEntry_6_11_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_11_14)=_
  rw [rawEntry_6_11_14_coordinates]
  exact rawPlus_subst 11 14
theorem rawEntry_6_14_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 11=sparseCoefficient rawEntry_6_11_14 r := by decide +kernel
theorem rawEntry_6_14_11_physical : invariantSubst (rawCoordinate 6 14 11)=rawPlusPolynomial 14 11 := by
  have hh : rawCoordinate 6 14 11=rawCoordinate 6 11 14 := by
    rw [rawCoordinate_sparse 6 14 11 rawEntry_6_11_14 rawEntry_6_14_11_data,rawCoordinate_sparse 6 11 14 rawEntry_6_11_14 rawEntry_6_11_14_data]
  rw [hh,rawEntry_6_11_14_physical]
  exact rawPlusPolynomial_symm 11 14
def rawEntry_6_11_15 : SparseEntry := [(62,1)]
theorem rawEntry_6_11_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 11 15=sparseCoefficient rawEntry_6_11_15 r := by decide +kernel
theorem rawEntry_6_11_15_coordinates : sparsePolynomial 1 rawEntry_6_11_15=rawPlusCoordinates 11 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_11_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_11_15_physical : invariantSubst (rawCoordinate 6 11 15)=rawPlusPolynomial 11 15 := by
  rw [rawCoordinate_sparse 6 11 15 rawEntry_6_11_15 rawEntry_6_11_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_11_15)=_
  rw [rawEntry_6_11_15_coordinates]
  exact rawPlus_subst 11 15
theorem rawEntry_6_15_11_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 11=sparseCoefficient rawEntry_6_11_15 r := by decide +kernel
theorem rawEntry_6_15_11_physical : invariantSubst (rawCoordinate 6 15 11)=rawPlusPolynomial 15 11 := by
  have hh : rawCoordinate 6 15 11=rawCoordinate 6 11 15 := by
    rw [rawCoordinate_sparse 6 15 11 rawEntry_6_11_15 rawEntry_6_15_11_data,rawCoordinate_sparse 6 11 15 rawEntry_6_11_15 rawEntry_6_11_15_data]
  rw [hh,rawEntry_6_11_15_physical]
  exact rawPlusPolynomial_symm 11 15
def rawEntry_6_12_12 : SparseEntry := [(58,1)]
theorem rawEntry_6_12_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 12=sparseCoefficient rawEntry_6_12_12 r := by decide +kernel
theorem rawEntry_6_12_12_coordinates : sparsePolynomial 1 rawEntry_6_12_12=rawPlusCoordinates 12 12 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_12_12,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_12_12_physical : invariantSubst (rawCoordinate 6 12 12)=rawPlusPolynomial 12 12 := by
  rw [rawCoordinate_sparse 6 12 12 rawEntry_6_12_12 rawEntry_6_12_12_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_12_12)=_
  rw [rawEntry_6_12_12_coordinates]
  exact rawPlus_subst 12 12
def rawEntry_6_12_13 : SparseEntry := [(59,1)]
theorem rawEntry_6_12_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 13=sparseCoefficient rawEntry_6_12_13 r := by decide +kernel
theorem rawEntry_6_12_13_coordinates : sparsePolynomial 1 rawEntry_6_12_13=rawPlusCoordinates 12 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_12_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_12_13_physical : invariantSubst (rawCoordinate 6 12 13)=rawPlusPolynomial 12 13 := by
  rw [rawCoordinate_sparse 6 12 13 rawEntry_6_12_13 rawEntry_6_12_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_12_13)=_
  rw [rawEntry_6_12_13_coordinates]
  exact rawPlus_subst 12 13
theorem rawEntry_6_13_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 12=sparseCoefficient rawEntry_6_12_13 r := by decide +kernel
theorem rawEntry_6_13_12_physical : invariantSubst (rawCoordinate 6 13 12)=rawPlusPolynomial 13 12 := by
  have hh : rawCoordinate 6 13 12=rawCoordinate 6 12 13 := by
    rw [rawCoordinate_sparse 6 13 12 rawEntry_6_12_13 rawEntry_6_13_12_data,rawCoordinate_sparse 6 12 13 rawEntry_6_12_13 rawEntry_6_12_13_data]
  rw [hh,rawEntry_6_12_13_physical]
  exact rawPlusPolynomial_symm 12 13
def rawEntry_6_12_14 : SparseEntry := [(61,1)]
theorem rawEntry_6_12_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 14=sparseCoefficient rawEntry_6_12_14 r := by decide +kernel
theorem rawEntry_6_12_14_coordinates : sparsePolynomial 1 rawEntry_6_12_14=rawPlusCoordinates 12 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_12_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_12_14_physical : invariantSubst (rawCoordinate 6 12 14)=rawPlusPolynomial 12 14 := by
  rw [rawCoordinate_sparse 6 12 14 rawEntry_6_12_14 rawEntry_6_12_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_12_14)=_
  rw [rawEntry_6_12_14_coordinates]
  exact rawPlus_subst 12 14
theorem rawEntry_6_14_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 12=sparseCoefficient rawEntry_6_12_14 r := by decide +kernel
theorem rawEntry_6_14_12_physical : invariantSubst (rawCoordinate 6 14 12)=rawPlusPolynomial 14 12 := by
  have hh : rawCoordinate 6 14 12=rawCoordinate 6 12 14 := by
    rw [rawCoordinate_sparse 6 14 12 rawEntry_6_12_14 rawEntry_6_14_12_data,rawCoordinate_sparse 6 12 14 rawEntry_6_12_14 rawEntry_6_12_14_data]
  rw [hh,rawEntry_6_12_14_physical]
  exact rawPlusPolynomial_symm 12 14
def rawEntry_6_12_15 : SparseEntry := [(63,1)]
theorem rawEntry_6_12_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 12 15=sparseCoefficient rawEntry_6_12_15 r := by decide +kernel
theorem rawEntry_6_12_15_coordinates : sparsePolynomial 1 rawEntry_6_12_15=rawPlusCoordinates 12 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_12_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_12_15_physical : invariantSubst (rawCoordinate 6 12 15)=rawPlusPolynomial 12 15 := by
  rw [rawCoordinate_sparse 6 12 15 rawEntry_6_12_15 rawEntry_6_12_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_12_15)=_
  rw [rawEntry_6_12_15_coordinates]
  exact rawPlus_subst 12 15
theorem rawEntry_6_15_12_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 12=sparseCoefficient rawEntry_6_12_15 r := by decide +kernel
theorem rawEntry_6_15_12_physical : invariantSubst (rawCoordinate 6 15 12)=rawPlusPolynomial 15 12 := by
  have hh : rawCoordinate 6 15 12=rawCoordinate 6 12 15 := by
    rw [rawCoordinate_sparse 6 15 12 rawEntry_6_12_15 rawEntry_6_15_12_data,rawCoordinate_sparse 6 12 15 rawEntry_6_12_15 rawEntry_6_12_15_data]
  rw [hh,rawEntry_6_12_15_physical]
  exact rawPlusPolynomial_symm 12 15
def rawEntry_6_13_13 : SparseEntry := [(60,1)]
theorem rawEntry_6_13_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 13=sparseCoefficient rawEntry_6_13_13 r := by decide +kernel
theorem rawEntry_6_13_13_coordinates : sparsePolynomial 1 rawEntry_6_13_13=rawPlusCoordinates 13 13 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_13_13,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_13_13_physical : invariantSubst (rawCoordinate 6 13 13)=rawPlusPolynomial 13 13 := by
  rw [rawCoordinate_sparse 6 13 13 rawEntry_6_13_13 rawEntry_6_13_13_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_13_13)=_
  rw [rawEntry_6_13_13_coordinates]
  exact rawPlus_subst 13 13
def rawEntry_6_13_14 : SparseEntry := [(62,1)]
theorem rawEntry_6_13_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 14=sparseCoefficient rawEntry_6_13_14 r := by decide +kernel
theorem rawEntry_6_13_14_coordinates : sparsePolynomial 1 rawEntry_6_13_14=rawPlusCoordinates 13 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_13_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_13_14_physical : invariantSubst (rawCoordinate 6 13 14)=rawPlusPolynomial 13 14 := by
  rw [rawCoordinate_sparse 6 13 14 rawEntry_6_13_14 rawEntry_6_13_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_13_14)=_
  rw [rawEntry_6_13_14_coordinates]
  exact rawPlus_subst 13 14
theorem rawEntry_6_14_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 13=sparseCoefficient rawEntry_6_13_14 r := by decide +kernel
theorem rawEntry_6_14_13_physical : invariantSubst (rawCoordinate 6 14 13)=rawPlusPolynomial 14 13 := by
  have hh : rawCoordinate 6 14 13=rawCoordinate 6 13 14 := by
    rw [rawCoordinate_sparse 6 14 13 rawEntry_6_13_14 rawEntry_6_14_13_data,rawCoordinate_sparse 6 13 14 rawEntry_6_13_14 rawEntry_6_13_14_data]
  rw [hh,rawEntry_6_13_14_physical]
  exact rawPlusPolynomial_symm 13 14
def rawEntry_6_13_15 : SparseEntry := [(64,1)]
theorem rawEntry_6_13_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 13 15=sparseCoefficient rawEntry_6_13_15 r := by decide +kernel
theorem rawEntry_6_13_15_coordinates : sparsePolynomial 1 rawEntry_6_13_15=rawPlusCoordinates 13 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_13_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_13_15_physical : invariantSubst (rawCoordinate 6 13 15)=rawPlusPolynomial 13 15 := by
  rw [rawCoordinate_sparse 6 13 15 rawEntry_6_13_15 rawEntry_6_13_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_13_15)=_
  rw [rawEntry_6_13_15_coordinates]
  exact rawPlus_subst 13 15
theorem rawEntry_6_15_13_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 13=sparseCoefficient rawEntry_6_13_15 r := by decide +kernel
theorem rawEntry_6_15_13_physical : invariantSubst (rawCoordinate 6 15 13)=rawPlusPolynomial 15 13 := by
  have hh : rawCoordinate 6 15 13=rawCoordinate 6 13 15 := by
    rw [rawCoordinate_sparse 6 15 13 rawEntry_6_13_15 rawEntry_6_15_13_data,rawCoordinate_sparse 6 13 15 rawEntry_6_13_15 rawEntry_6_13_15_data]
  rw [hh,rawEntry_6_13_15_physical]
  exact rawPlusPolynomial_symm 13 15
def rawEntry_6_14_14 : SparseEntry := [(63,1)]
theorem rawEntry_6_14_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 14=sparseCoefficient rawEntry_6_14_14 r := by decide +kernel
theorem rawEntry_6_14_14_coordinates : sparsePolynomial 1 rawEntry_6_14_14=rawPlusCoordinates 14 14 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_14_14,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_14_14_physical : invariantSubst (rawCoordinate 6 14 14)=rawPlusPolynomial 14 14 := by
  rw [rawCoordinate_sparse 6 14 14 rawEntry_6_14_14 rawEntry_6_14_14_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_14_14)=_
  rw [rawEntry_6_14_14_coordinates]
  exact rawPlus_subst 14 14
def rawEntry_6_14_15 : SparseEntry := [(65,1)]
theorem rawEntry_6_14_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 14 15=sparseCoefficient rawEntry_6_14_15 r := by decide +kernel
theorem rawEntry_6_14_15_coordinates : sparsePolynomial 1 rawEntry_6_14_15=rawPlusCoordinates 14 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_14_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_14_15_physical : invariantSubst (rawCoordinate 6 14 15)=rawPlusPolynomial 14 15 := by
  rw [rawCoordinate_sparse 6 14 15 rawEntry_6_14_15 rawEntry_6_14_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_14_15)=_
  rw [rawEntry_6_14_15_coordinates]
  exact rawPlus_subst 14 15
theorem rawEntry_6_15_14_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 14=sparseCoefficient rawEntry_6_14_15 r := by decide +kernel
theorem rawEntry_6_15_14_physical : invariantSubst (rawCoordinate 6 15 14)=rawPlusPolynomial 15 14 := by
  have hh : rawCoordinate 6 15 14=rawCoordinate 6 14 15 := by
    rw [rawCoordinate_sparse 6 15 14 rawEntry_6_14_15 rawEntry_6_15_14_data,rawCoordinate_sparse 6 14 15 rawEntry_6_14_15 rawEntry_6_14_15_data]
  rw [hh,rawEntry_6_14_15_physical]
  exact rawPlusPolynomial_symm 14 15
def rawEntry_6_15_15 : SparseEntry := [(66,1)]
theorem rawEntry_6_15_15_data : ∀r : Fin 102, RawData.coefficient 6 r.val 15 15=sparseCoefficient rawEntry_6_15_15 r := by decide +kernel
theorem rawEntry_6_15_15_coordinates : sparsePolynomial 1 rawEntry_6_15_15=rawPlusCoordinates 15 15 := by
  apply MvPolynomial.funext
  intro x
  simp [sparsePolynomial,rawEntry_6_15_15,coordinateMonomial,rawPlusCoordinates,addTag,plusTag] <;> ring
theorem rawEntry_6_15_15_physical : invariantSubst (rawCoordinate 6 15 15)=rawPlusPolynomial 15 15 := by
  rw [rawCoordinate_sparse 6 15 15 rawEntry_6_15_15 rawEntry_6_15_15_data]
  change invariantSubst (sparsePolynomial 1 rawEntry_6_15_15)=_
  rw [rawEntry_6_15_15_coordinates]
  exact rawPlus_subst 15 15
end ThomsonNegative.Certificate.Bridges
