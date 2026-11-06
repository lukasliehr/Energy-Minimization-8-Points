import ThomsonNegative.Structure.Concrete.SymmetryBlock0
import ThomsonNegative.Structure.Concrete.SymmetryBlock1
import ThomsonNegative.Structure.Concrete.SymmetryBlock2
import ThomsonNegative.Structure.Concrete.SymmetryBlock3
import ThomsonNegative.Structure.Concrete.SymmetryBlock4
import ThomsonNegative.Structure.Concrete.SymmetryBlock5
import ThomsonNegative.Structure.Concrete.SymmetryBlock6
import ThomsonNegative.Structure.Concrete.SymmetryBlock7
import ThomsonNegative.Structure.Concrete.HighImage
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Structure.Exact ThomsonNegative.Certificate.Bridges
lemma all_symmetry_blocks (b : Block) : SymmetryKernel.blockCheck b.val=true := by
  fin_cases b
  · exact SymmetryKernel.block0
  · exact SymmetryKernel.block1
  · exact SymmetryKernel.block2
  · exact SymmetryKernel.block3
  · exact SymmetryKernel.block4
  · exact SymmetryKernel.block5
  · exact SymmetryKernel.block6
  · exact SymmetryKernel.block7

theorem rawCoefficient_symm (b : Block) (l : Fin 102) (r s : Fin (rawSize b)) :
    rawCoefficient b l r s=rawCoefficient b l s r := by
  have hl := allBelow_spec _ _ (all_symmetry_blocks b) l.val l.isLt
  have hr : r.val<RawData.size b.val := by rw [raw_size_agrees];exact r.isLt
  have hs : s.val<RawData.size b.val := by rw [raw_size_agrees];exact s.isLt
  have hh := allBelow_spec _ _ (allBelow_spec _ _ hl r.val hr) s.val hs
  have hh' : RawData.positiveSlot b.val l.val r.val s.val=RawData.positiveSlot b.val l.val s.val r.val ∧
      RawData.negativeSlot b.val l.val r.val s.val=RawData.negativeSlot b.val l.val s.val r.val := by
    have hpair : Nat.beq (RawData.positiveSlot b.val l.val r.val s.val)
        (RawData.positiveSlot b.val l.val s.val r.val)=true ∧
        Nat.beq (RawData.negativeSlot b.val l.val r.val s.val)
        (RawData.negativeSlot b.val l.val s.val r.val)=true := by
      simpa only [SymmetryKernel.entryCheck,Bool.and_eq_true] using hh
    exact ⟨Nat.eq_of_beq_eq_true hpair.1,Nat.eq_of_beq_eq_true hpair.2⟩
  simp only [rawCoefficient,RawData.coefficient,hh'.1,hh'.2]

theorem mixedCoefficient_symm (B : CanonicalBasis) (b : Block) (i j : Fin (blockSize b)) :
    mixedCoefficient B b i j=mixedCoefficient B b j i := by
  funext l
  simp only [mixedCoefficient,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,rawCoefficientVector]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [rawCoefficient_symm b l s r]
  ring
end ThomsonNegative.Structure.Concrete
