import ThomsonNegative.Structure.Concrete.BasisBlock0Row00
import ThomsonNegative.Structure.Concrete.BasisBlock0Row01
import ThomsonNegative.Structure.Concrete.BasisBlock0Row02
import ThomsonNegative.Structure.Concrete.BasisBlock0Row03
import ThomsonNegative.Structure.Concrete.BasisBlock0Row04
import ThomsonNegative.Structure.Concrete.BasisBlock0Row05
import ThomsonNegative.Structure.Concrete.BasisBlock0Row06
import ThomsonNegative.Structure.Concrete.BasisBlock1Row00
import ThomsonNegative.Structure.Concrete.BasisBlock1Row01
import ThomsonNegative.Structure.Concrete.BasisBlock1Row02
import ThomsonNegative.Structure.Concrete.BasisBlock1Row03
import ThomsonNegative.Structure.Concrete.BasisBlock1Row04
import ThomsonNegative.Structure.Concrete.BasisBlock1Row05
import ThomsonNegative.Structure.Concrete.BasisBlock2Row00
import ThomsonNegative.Structure.Concrete.BasisBlock2Row01
import ThomsonNegative.Structure.Concrete.BasisBlock2Row02
import ThomsonNegative.Structure.Concrete.BasisBlock2Row03
import ThomsonNegative.Structure.Concrete.BasisBlock2Row04
import ThomsonNegative.Structure.Concrete.BasisBlock3Row00
import ThomsonNegative.Structure.Concrete.BasisBlock3Row01
import ThomsonNegative.Structure.Concrete.BasisBlock3Row02
import ThomsonNegative.Structure.Concrete.BasisBlock3Row03
import ThomsonNegative.Structure.Concrete.BasisBlock4Row00
import ThomsonNegative.Structure.Concrete.BasisBlock4Row01
import ThomsonNegative.Structure.Concrete.BasisBlock4Row02
import ThomsonNegative.Structure.Concrete.BasisBlock5Row00
import ThomsonNegative.Structure.Concrete.BasisBlock5Row01
import ThomsonNegative.Structure.Concrete.BasisBlock6Row00
import ThomsonNegative.Structure.Concrete.BasisBlock6Row01
import ThomsonNegative.Structure.Concrete.BasisBlock6Row02
import ThomsonNegative.Structure.Concrete.BasisBlock6Row03
import ThomsonNegative.Structure.Concrete.BasisBlock6Row04
import ThomsonNegative.Structure.Concrete.BasisBlock6Row05
import ThomsonNegative.Structure.Concrete.BasisBlock6Row06
import ThomsonNegative.Structure.Concrete.BasisBlock6Row07
import ThomsonNegative.Structure.Concrete.BasisBlock6Row08
import ThomsonNegative.Structure.Concrete.BasisBlock6Row09
import ThomsonNegative.Structure.Concrete.BasisBlock6Row10
import ThomsonNegative.Structure.Concrete.BasisBlock6Row11
import ThomsonNegative.Structure.Concrete.BasisBlock6Row12
import ThomsonNegative.Structure.Concrete.BasisBlock6Row13
import ThomsonNegative.Structure.Concrete.BasisBlock6Row14
import ThomsonNegative.Structure.Concrete.BasisBlock6Row15
import ThomsonNegative.Structure.Concrete.BasisBlock7Row00
import ThomsonNegative.Structure.Concrete.BasisBlock7Row01
import ThomsonNegative.Structure.Concrete.BasisBlock7Row02
import ThomsonNegative.Structure.Concrete.BasisBlock7Row03
import ThomsonNegative.Structure.Concrete.BasisBlock7Row04
import ThomsonNegative.Structure.Concrete.BasisBlock7Row05
import ThomsonNegative.Structure.Concrete.BasisBlock7Row06
import ThomsonNegative.Structure.Concrete.BasisBlock7Row07
import ThomsonNegative.Structure.Concrete.BasisBlock7Row08
import ThomsonNegative.Structure.Concrete.BasisBlock7Row09
import ThomsonNegative.Structure.Concrete.BasisBlock7Row10
import ThomsonNegative.Structure.Concrete.BasisBlock7Row11
import ThomsonNegative.Structure.Concrete.BasisBlock7Row12
import ThomsonNegative.Structure.Concrete.BasisBlock7Row13
import ThomsonNegative.Structure.Concrete.BasisBlock7Row14
import ThomsonNegative.Structure.Concrete.BasisBlock7Row15
import ThomsonNegative.Structure.Concrete.BasisBlock7Row16
import ThomsonNegative.Structure.Concrete.BasisBlock7Row17
import ThomsonNegative.Structure.Concrete.BasisDen.Regular
import ThomsonNegative.Certificate.Bridges.RawInterface
import ThomsonNegative.Structure.Packed.IdentitySound
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed
open ThomsonNegative.Certificate.Bridges
theorem basis_source_numerator : ∀i : Fin 149,
    recCoeffs (BasisData.sourceNumerator i.val)=(SourceBasis.record i.val).numerator := by decide +kernel

theorem basis_source_denominator : ∀i : Fin 149,
    recCoeffs (BasisData.sourceDenominator i.val)=(SourceBasis.record i.val).denominator := by decide +kernel

theorem basis_source_index_bound : ∀(b : Block)(r : Fin (rawSize b))(i : Fin (blockSize b)),
    ThomsonNegative.Certificate.BasisLayout.index b.val r.val i.val<149 := by decide +kernel

theorem basis_row_accepted (b : Block) (r : Fin (rawSize b)) :
    BasisKernel.rowCheck b.val r.val (blockSize b)=true := by
  fin_cases b
  · fin_cases r
    · exact BasisKernel.block0_row0
    · exact BasisKernel.block0_row1
    · exact BasisKernel.block0_row2
    · exact BasisKernel.block0_row3
    · exact BasisKernel.block0_row4
    · exact BasisKernel.block0_row5
    · exact BasisKernel.block0_row6
  · fin_cases r
    · exact BasisKernel.block1_row0
    · exact BasisKernel.block1_row1
    · exact BasisKernel.block1_row2
    · exact BasisKernel.block1_row3
    · exact BasisKernel.block1_row4
    · exact BasisKernel.block1_row5
  · fin_cases r
    · exact BasisKernel.block2_row0
    · exact BasisKernel.block2_row1
    · exact BasisKernel.block2_row2
    · exact BasisKernel.block2_row3
    · exact BasisKernel.block2_row4
  · fin_cases r
    · exact BasisKernel.block3_row0
    · exact BasisKernel.block3_row1
    · exact BasisKernel.block3_row2
    · exact BasisKernel.block3_row3
  · fin_cases r
    · exact BasisKernel.block4_row0
    · exact BasisKernel.block4_row1
    · exact BasisKernel.block4_row2
  · fin_cases r
    · exact BasisKernel.block5_row0
    · exact BasisKernel.block5_row1
  · fin_cases r
    · exact BasisKernel.block6_row0
    · exact BasisKernel.block6_row1
    · exact BasisKernel.block6_row2
    · exact BasisKernel.block6_row3
    · exact BasisKernel.block6_row4
    · exact BasisKernel.block6_row5
    · exact BasisKernel.block6_row6
    · exact BasisKernel.block6_row7
    · exact BasisKernel.block6_row8
    · exact BasisKernel.block6_row9
    · exact BasisKernel.block6_row10
    · exact BasisKernel.block6_row11
    · exact BasisKernel.block6_row12
    · exact BasisKernel.block6_row13
    · exact BasisKernel.block6_row14
    · exact BasisKernel.block6_row15
  · fin_cases r
    · exact BasisKernel.block7_row0
    · exact BasisKernel.block7_row1
    · exact BasisKernel.block7_row2
    · exact BasisKernel.block7_row3
    · exact BasisKernel.block7_row4
    · exact BasisKernel.block7_row5
    · exact BasisKernel.block7_row6
    · exact BasisKernel.block7_row7
    · exact BasisKernel.block7_row8
    · exact BasisKernel.block7_row9
    · exact BasisKernel.block7_row10
    · exact BasisKernel.block7_row11
    · exact BasisKernel.block7_row12
    · exact BasisKernel.block7_row13
    · exact BasisKernel.block7_row14
    · exact BasisKernel.block7_row15
    · exact BasisKernel.block7_row16
    · exact BasisKernel.block7_row17
theorem basis_checks (b : Block) (r : Fin (rawSize b)) (i : Fin (blockSize b)) :
    (BasisKernel.numeratorEquation b.val r.val i.val).check=true ∧
      (BasisKernel.denominatorEquation b.val r.val i.val).check=true := by
  have hh := allBelow_spec _ _ (basis_row_accepted b r) i.val i.isLt
  simpa only [Bool.and_eq_true] using hh

def clearedBasis (a : ℝ) (b : Block) : Matrix (Fin (rawSize b)) (Fin (blockSize b)) ℝ :=
  fun r i => evalZ (recCoeffs (BasisData.numerator b.val r.val i.val)) a

def basisDenominator (a : ℝ) (b : Block) : ℝ :=
  evalZ (recCoeffs (BasisData.denominator b.val)) a

theorem basisDenominator_ne_zero (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (b : Block) :
    basisDenominator a b≠0 := by
  have hh : BasisDen.DenData.word b.val=BasisData.denominator b.val := by fin_cases b <;> rfl
  have hn := BasisDen.denominator_nonzero b a ha hb
  simpa only [hh,basisDenominator] using hn

theorem clearedBasis_source (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (b : Block) (r : Fin (rawSize b)) (i : Fin (blockSize b)) :
    blockBasis (sourceBasis.eval a) b r i=clearedBasis a b r i/basisDenominator a b := by
  have hs := basis_source_index_bound b r i
  have hn := (BasisKernel.numeratorEquation b.val r.val i.val).sound (basis_checks b r i).1 a
  have hd := (BasisKernel.denominatorEquation b.val r.val i.val).sound (basis_checks b r i).2 a
  simp only [BasisKernel.numeratorEquation,BasisKernel.denominatorEquation,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    oneRecord_decode,evalZ,horner,List.map_cons,List.map_nil,Int.cast_one,mul_zero,add_zero,mul_one] at hn hd
  change evalZ (recCoeffs (BasisData.sourceNumerator _)) a *
    evalZ (recCoeffs (BasisData.quotient b.val r.val i.val)) a=clearedBasis a b r i at hn
  change evalZ (recCoeffs (BasisData.sourceDenominator _)) a *
    evalZ (recCoeffs (BasisData.quotient b.val r.val i.val)) a=basisDenominator a b at hd
  rw [basis_source_numerator ⟨_,hs⟩] at hn
  rw [basis_source_denominator ⟨_,hs⟩] at hd
  have hbD := basisDenominator_ne_zero a ha hb b
  have hden : evalZ (SourceBasis.record
      (ThomsonNegative.Certificate.BasisLayout.index b.val r.val i.val)).denominator a≠0 := by
    intro hz
    rw [hz,zero_mul] at hd
    exact hbD hd.symm
  rw [blockBasis_source_entry,RF.eval]
  apply (div_eq_div_iff hden hbD).mpr
  rw [← hd,← hn]
  ring

theorem evalZ_differentiableAt (p : List ℤ) (a : ℝ) :
    DifferentiableAt ℝ (fun t => evalZ p t) a := by
  induction p with
  | nil => exact differentiableAt_const 0
  | cons c p ih =>
    change DifferentiableAt ℝ (fun t => (c:ℝ)+t*evalZ p t) a
    exact (differentiableAt_const _).add (differentiableAt_id.mul ih)

theorem clearedBasis_differentiableAt (b : Block) (r : Fin (rawSize b))
    (i : Fin (blockSize b)) (a : ℝ) :
    DifferentiableAt ℝ (fun t => clearedBasis t b r i) a :=
  evalZ_differentiableAt _ a

#print axioms clearedBasis_source
end ThomsonNegative.Structure.Concrete
