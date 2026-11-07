import ThomsonNegative.Certificate.Bridges.RFTranslations00
import ThomsonNegative.Certificate.Bridges.RFTranslations01
import ThomsonNegative.Certificate.Bridges.RFTranslations02
import ThomsonNegative.Certificate.Bridges.RFTranslations03
import ThomsonNegative.Certificate.Bridges.RFTranslations04
import ThomsonNegative.Certificate.Bridges.RFTranslations05
import ThomsonNegative.Certificate.Bridges.RFTranslations06
import ThomsonNegative.Certificate.Bridges.RFTranslations07
import ThomsonNegative.Certificate.Bridges.RFTranslations08
import ThomsonNegative.Certificate.Bridges.RFTranslations09
import ThomsonNegative.Certificate.Bridges.RFTranslations10
import ThomsonNegative.Certificate.Bridges.RFTranslations11
import ThomsonNegative.Certificate.Bridges.RFTranslations12
import ThomsonNegative.Certificate.Bridges.RFTranslations13
import ThomsonNegative.Certificate.Bridges.RFTranslations14
import ThomsonNegative.Certificate.BasisLayout
import ThomsonNegative.Structure.CanonicalBasis
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem record_translation (i : Fin 149) (a : ℝ) :
    (BasisData.record i.val).eval (a-83/256)=(SourceBasis.record i.val).eval a := by
  fin_cases i
  · exact rf0_translation a
  · exact rf1_translation a
  · exact rf2_translation a
  · exact rf3_translation a
  · exact rf4_translation a
  · exact rf5_translation a
  · exact rf6_translation a
  · exact rf7_translation a
  · exact rf8_translation a
  · exact rf9_translation a
  · exact rf10_translation a
  · exact rf11_translation a
  · exact rf12_translation a
  · exact rf13_translation a
  · exact rf14_translation a
  · exact rf15_translation a
  · exact rf16_translation a
  · exact rf17_translation a
  · exact rf18_translation a
  · exact rf19_translation a
  · exact rf20_translation a
  · exact rf21_translation a
  · exact rf22_translation a
  · exact rf23_translation a
  · exact rf24_translation a
  · exact rf25_translation a
  · exact rf26_translation a
  · exact rf27_translation a
  · exact rf28_translation a
  · exact rf29_translation a
  · exact rf30_translation a
  · exact rf31_translation a
  · exact rf32_translation a
  · exact rf33_translation a
  · exact rf34_translation a
  · exact rf35_translation a
  · exact rf36_translation a
  · exact rf37_translation a
  · exact rf38_translation a
  · exact rf39_translation a
  · exact rf40_translation a
  · exact rf41_translation a
  · exact rf42_translation a
  · exact rf43_translation a
  · exact rf44_translation a
  · exact rf45_translation a
  · exact rf46_translation a
  · exact rf47_translation a
  · exact rf48_translation a
  · exact rf49_translation a
  · exact rf50_translation a
  · exact rf51_translation a
  · exact rf52_translation a
  · exact rf53_translation a
  · exact rf54_translation a
  · exact rf55_translation a
  · exact rf56_translation a
  · exact rf57_translation a
  · exact rf58_translation a
  · exact rf59_translation a
  · exact rf60_translation a
  · exact rf61_translation a
  · exact rf62_translation a
  · exact rf63_translation a
  · exact rf64_translation a
  · exact rf65_translation a
  · exact rf66_translation a
  · exact rf67_translation a
  · exact rf68_translation a
  · exact rf69_translation a
  · exact rf70_translation a
  · exact rf71_translation a
  · exact rf72_translation a
  · exact rf73_translation a
  · exact rf74_translation a
  · exact rf75_translation a
  · exact rf76_translation a
  · exact rf77_translation a
  · exact rf78_translation a
  · exact rf79_translation a
  · exact rf80_translation a
  · exact rf81_translation a
  · exact rf82_translation a
  · exact rf83_translation a
  · exact rf84_translation a
  · exact rf85_translation a
  · exact rf86_translation a
  · exact rf87_translation a
  · exact rf88_translation a
  · exact rf89_translation a
  · exact rf90_translation a
  · exact rf91_translation a
  · exact rf92_translation a
  · exact rf93_translation a
  · exact rf94_translation a
  · exact rf95_translation a
  · exact rf96_translation a
  · exact rf97_translation a
  · exact rf98_translation a
  · exact rf99_translation a
  · exact rf100_translation a
  · exact rf101_translation a
  · exact rf102_translation a
  · exact rf103_translation a
  · exact rf104_translation a
  · exact rf105_translation a
  · exact rf106_translation a
  · exact rf107_translation a
  · exact rf108_translation a
  · exact rf109_translation a
  · exact rf110_translation a
  · exact rf111_translation a
  · exact rf112_translation a
  · exact rf113_translation a
  · exact rf114_translation a
  · exact rf115_translation a
  · exact rf116_translation a
  · exact rf117_translation a
  · exact rf118_translation a
  · exact rf119_translation a
  · exact rf120_translation a
  · exact rf121_translation a
  · exact rf122_translation a
  · exact rf123_translation a
  · exact rf124_translation a
  · exact rf125_translation a
  · exact rf126_translation a
  · exact rf127_translation a
  · exact rf128_translation a
  · exact rf129_translation a
  · exact rf130_translation a
  · exact rf131_translation a
  · exact rf132_translation a
  · exact rf133_translation a
  · exact rf134_translation a
  · exact rf135_translation a
  · exact rf136_translation a
  · exact rf137_translation a
  · exact rf138_translation a
  · exact rf139_translation a
  · exact rf140_translation a
  · exact rf141_translation a
  · exact rf142_translation a
  · exact rf143_translation a
  · exact rf144_translation a
  · exact rf145_translation a
  · exact rf146_translation a
  · exact rf147_translation a
  · exact rf148_translation a
theorem moment_index_bound : ∀ (k : Fin 6) (i : Fin (7-k.val)) (j : Fin (6-k.val)),
    BasisLayout.index k.val i.val j.val < 149 := by decide +kernel

theorem plus_index_bound : ∀ (i : Fin 16) (j : Fin 11),
    BasisLayout.index 6 i.val j.val < 149 := by decide +kernel

theorem standard_index_bound : ∀ (i : Fin 18) (j : Fin 11),
    BasisLayout.index 7 i.val j.val < 149 := by decide +kernel

def sourceBasis : RFBasis where
  moment := fun k i j => SourceBasis.record (BasisLayout.index k.val i.val j.val)
  plus := fun i j => SourceBasis.record (BasisLayout.index 6 i.val j.val)
  standard := fun i j => SourceBasis.record (BasisLayout.index 7 i.val j.val)

def encodedBasis (a : ℝ) : CanonicalBasis where
  moment := fun k i j => (BasisData.record (BasisLayout.index k.val i.val j.val)).eval (a-83/256)
  plus := fun i j => (BasisData.record (BasisLayout.index 6 i.val j.val)).eval (a-83/256)
  standard := fun i j => (BasisData.record (BasisLayout.index 7 i.val j.val)).eval (a-83/256)

theorem encodedBasis_eq_source (a : ℝ) : encodedBasis a=sourceBasis.eval a := by
  have hm : (encodedBasis a).moment=(sourceBasis.eval a).moment := by
    funext k i j
    exact record_translation ⟨_,moment_index_bound k i j⟩ a
  have hp : (encodedBasis a).plus=(sourceBasis.eval a).plus := by
    funext i j
    exact record_translation ⟨_,plus_index_bound i j⟩ a
  have hs : (encodedBasis a).standard=(sourceBasis.eval a).standard := by
    funext i j
    exact record_translation ⟨_,standard_index_bound i j⟩ a
  cases h1 : encodedBasis a
  cases h2 : sourceBasis.eval a
  simp_all

def sourcePolynomialFamily (a : ℝ) : PolynomialFamily := canonicalPolynomialFamily (sourceBasis.eval a)

theorem sourcePolynomialFamily_realization (a : ℝ) (b : Block) :
    ThomsonNegative.Geometry.BlockRealization (sourcePolynomialFamily a b) :=
  canonicalPolynomialFamily_realization (sourceBasis.eval a) b

theorem encodedPolynomialFamily_eq_source (a : ℝ) :
    canonicalPolynomialFamily (encodedBasis a)=sourcePolynomialFamily a := by
  rw [encodedBasis_eq_source]
  rfl

#print axioms record_translation
#print axioms encodedBasis_eq_source
#print axioms sourcePolynomialFamily_realization
end ThomsonNegative.Certificate.Bridges
