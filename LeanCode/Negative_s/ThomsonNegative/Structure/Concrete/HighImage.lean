import ThomsonNegative.Structure.Concrete.HighBlock0
import ThomsonNegative.Structure.Concrete.HighBlock1
import ThomsonNegative.Structure.Concrete.HighBlock2
import ThomsonNegative.Structure.Concrete.HighBlock3
import ThomsonNegative.Structure.Concrete.HighBlock4
import ThomsonNegative.Structure.Concrete.HighBlock5
import ThomsonNegative.Structure.Concrete.HighBlock6
import ThomsonNegative.Structure.Concrete.HighBlock7
import ThomsonNegative.Certificate.Bridges.RawInterface
import ThomsonNegative.Structure.Packed.IdentitySound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Certificate.Bridges ThomsonNegative.Structure.Exact

local instance highFactorsDecidable (h : Fin 35) (j : Fin 3) :
    Decidable ((HighKernel.positive h.val j.val : ℚ)-HighKernel.negative h.val j.val=
      highReconstruction h j) := inferInstance

theorem high_factors : ∀ (h : Fin 35) (j : Fin 3),
    (HighKernel.positive h.val j.val : ℚ)-HighKernel.negative h.val j.val =
      highReconstruction h j := by decide +kernel

theorem raw_size_agrees : ∀ b : Block, RawData.size b.val=rawSize b := by decide +kernel

theorem all_high_blocks (b : Block) : HighKernel.blockCheck b.val=true := by
  fin_cases b
  · exact HighKernel.block0
  · exact HighKernel.block1
  · exact HighKernel.block2
  · exact HighKernel.block3
  · exact HighKernel.block4
  · exact HighKernel.block5
  · exact HighKernel.block6
  · exact HighKernel.block7

theorem high_entry_check (b : Block) (h : Fin 35) (r s : Fin (rawSize b)) :
    HighKernel.entryCheck b.val h.val r.val s.val=true := by
  have hh := allBelow_spec _ _ (all_high_blocks b) h.val h.isLt
  have hr : r.val<RawData.size b.val := by rw [raw_size_agrees];exact r.isLt
  have hs : s.val<RawData.size b.val := by rw [raw_size_agrees];exact s.isLt
  exact allBelow_spec _ _ (allBelow_spec _ _ hh r.val hr) s.val hs

theorem raw_high_numerator (b : Block) (h : Fin 35) (r s : Fin (rawSize b)) :
    (RawData.coefficient b.val (highIndex h).val r.val s.val : ℝ)=
      ∑ j : Fin 3, (highReconstruction h j:ℝ)*
        (RawData.coefficient b.val (highIndex (highPivot j)).val r.val s.val:ℝ) := by
  have he := Nat.eq_of_beq_eq_true (high_entry_check b h r s)
  have heR := congrArg (Nat.cast : ℕ → ℝ) he
  have factors (j : Fin 3) : (highReconstruction h j:ℝ)=
      (HighKernel.positive h.val j.val:ℝ)-HighKernel.negative h.val j.val := by
    have hh := congrArg (Rat.castHom ℝ) (high_factors h j)
    simpa using hh.symm
  simp only [HighKernel.positiveTerm,HighKernel.negativeTerm,nat_add,nat_mul,Nat.cast_add,Nat.cast_mul] at heR
  simp_rw [factors]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,highIndex,highPivot,
    Matrix.cons_val_zero,Matrix.cons_val_succ,RawData.coefficient,Int.cast_sub,Int.cast_natCast]
  change (_:ℝ)=_
  change (_:ℝ)=_ at heR
  norm_num [HighKernel.pivot] at heR ⊢
  linear_combination heR

theorem raw_high (b : Block) (r s : Fin (rawSize b)) :
    HighCompatible (rawCoefficientVector b r s) := by
  intro h
  change (RawData.coefficient b.val (highIndex h).val r.val s.val:ℝ)/
    (RawData.denominator b.val:ℝ)=
    ∑ j, (highReconstruction h j:ℝ)*
      ((RawData.coefficient b.val (highIndex (highPivot j)).val r.val s.val:ℝ)/
        (RawData.denominator b.val:ℝ))
  rw [raw_high_numerator,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def highDefect : FullSpace →ₗ[ℝ] (Fin 35 → ℝ) where
  toFun v h := v (highIndex h)-highRebuild (highCoordinates v) h
  map_add' v w := by
    funext h
    simp [highRebuild,highCoordinates,mul_add,Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    funext h
    simp only [highRebuild,highCoordinates,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [mul_sub,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma highDefect_zero_iff (v : FullSpace) : highDefect v=0 ↔ HighCompatible v := by
  constructor
  · intro hv h
    exact sub_eq_zero.mp (congrFun hv h)
  · intro hv
    funext h
    exact sub_eq_zero.mpr (hv h)

lemma highDefect_raw (b : Block) (r s : Fin (rawSize b)) :
    highDefect (rawCoefficientVector b r s)=0 :=
  (highDefect_zero_iff _).mpr (raw_high b r s)

theorem coefficientMap_high_image (a : ℝ) (W : GramFamily) :
    HighCompatible (coefficientMap a W) := by
  apply (highDefect_zero_iff _).mp
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,mixedCoefficient,
    map_sum,map_smul,highDefect_raw,smul_zero,Finset.sum_const_zero]

#print axioms coefficientMap_high_image
end ThomsonNegative.Structure.Concrete
