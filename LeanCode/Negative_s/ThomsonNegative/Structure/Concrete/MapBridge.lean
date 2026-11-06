import ThomsonNegative.Structure.Concrete.MapSound
import ThomsonNegative.Structure.Concrete.System
import ThomsonNegative.Structure.Factored.HighSystem

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed
open ThomsonNegative.Certificate.Bridges

theorem repairUnit_common_denominator (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (r c : Fin 68) :
    coefficientMap a (repairUnit c) (chartIndex r)=
      (∑ i : Fin (rawSize (repairBlock c)),∑ j : Fin (rawSize (repairBlock c)),
        repairMultiplicity c*(RawData.coefficient (repairBlock c).val (chartIndex r).val i.val j.val:ℝ)*
          (clearedBasis a (repairBlock c) i (repairRowFin c)*
            clearedBasis a (repairBlock c) j (repairColFin c)))/
        (basisDenominator a (repairBlock c)*basisDenominator a (repairBlock c)*
          (RawData.denominator (repairBlock c).val:ℝ)) := by
  rw [coefficientMap_repairUnit]
  simp only [Pi.smul_apply,smul_eq_mul,mixedCoefficient,Finset.sum_apply,
    rawCoefficientVector,rawCoefficient]
  simp_rw [clearedBasis_source a ha hb]
  simp only [Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hB := basisDenominator_ne_zero a ha hb (repairBlock c)
  have hR : (RawData.denominator (repairBlock c).val:ℝ)≠0 := by
    exact_mod_cast ne_of_gt (raw_denominator_pos (repairBlock c))
  field_simp
  <;> ring

theorem source_map_entry (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (r c : Fin 68) :
    Factored.HighData.A.eval a r c=coefficientMap a (repairUnit c) (chartIndex r) := by
  rw [repairUnit_common_denominator a ha hb]
  change evalZ (recCoeffs (Factored.HighData.A.numerator r.val c.val)) a/
    evalZ (recCoeffs Factored.HighData.A.denominator) a=_
  have hB := basisDenominator_ne_zero a ha hb (repairBlock c)
  have hR : (RawData.denominator (repairBlock c).val:ℝ)≠0 := by
    exact_mod_cast ne_of_gt (raw_denominator_pos (repairBlock c))
  apply (div_eq_div_iff (Factored.A_regular a ha hb) (mul_ne_zero (mul_ne_zero hB hB) hR)).mpr
  exact (source_map_polynomial_identity a r c).symm

theorem insertRepair_coefficient (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : ChartSpace) :
    retain (coefficientMap a (insertRepair x))=(Factored.HighData.A.eval a).mulVec x := by
  funext r
  change (coefficientMap a (∑ k, x k • repairUnit k)) (chartIndex r)=_
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (∑ k, x k * coefficientMap a (repairUnit k) (chartIndex r))=
    ∑ k, (Factored.HighData.A.eval a) r k*x k
  apply Finset.sum_congr rfl
  intro k hk
  rw [source_map_entry a ha hb]
  ring

/-- The concrete exact inverse, proved through 3+14+15+36 small stages. -/
def stagedRightInverse (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    HybridRightInverse (system a ha hb) where
  correction := insertRepair.comp (Factored.operatorRepair a)
  right_inverse := by
    apply LinearMap.ext
    intro x
    funext r
    change retain (coefficientMap a (insertRepair (Factored.operatorRepair a x))) r=x r
    rw [insertRepair_coefficient a ha hb,Factored.operatorRepair_right_inverse a ha hb]

#print axioms source_map_entry
#print axioms stagedRightInverse
end ThomsonNegative.Structure.Concrete
