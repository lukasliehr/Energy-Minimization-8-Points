import AllS.Units.N_FI.N_kernels.RFColumns.Odd027_Fiber0
import AllS.Units.N_FI.N_kernels.RFColumns.Odd027_Fiber1
import AllS.Units.N_FI.N_kernels.RFColumns.Odd027_Fiber2
import AllS.Units.N_FI.N_kernels.RFColumns.Odd027_Fiber3
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd027
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values (a : ℝ) (ha : physical a) (h0 : rf1526.DefinedAt a) (h1 : rf1541.DefinedAt a) (h2 : rf1570.DefinedAt a) (h3 : rf1555.DefinedAt a) (h4 : rf1583.DefinedAt a) (h5 : rf1612.DefinedAt a) (h6 : rf1597.DefinedAt a) (h7 : rf1626.DefinedAt a) (h8 : rf1640.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a true i)^r.1.val*(parityFiberZ a true i j)^r.2.val)=paritySourceData a true (0,4,1) i j := by
  intro i j
  fin_cases i
  · exact values0 a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 j
  · exact values1 a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 j
  · exact values2 a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 j
  · exact values3 a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 j

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf1526.DefinedAt a) (h1 : rf1541.DefinedAt a) (h2 : rf1570.DefinedAt a) (h3 : rf1555.DefinedAt a) (h4 : rf1583.DefinedAt a) (h5 : rf1612.DefinedAt a) (h6 : rf1597.DefinedAt a) (h7 : rf1626.DefinedAt a) (h8 : rf1640.DefinedAt a) :
    ∀ r,parityKernelCoefficients a true (0,4,1) (parityIndexTag true r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8)

#print axioms coefficients

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf1526,rf1541,rf1555,rf0013,rf1570,rf1583,rf1597,rf0013,rf0013,rf0013,rf1612,rf1626,rf1640,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf1526.DefinedAt a) (h1 : rf1541.DefinedAt a) (h2 : rf1570.DefinedAt a) (h3 : rf1555.DefinedAt a) (h4 : rf1583.DefinedAt a) (h5 : rf1612.DefinedAt a) (h6 : rf1597.DefinedAt a) (h7 : rf1626.DefinedAt a) (h8 : rf1640.DefinedAt a) :
    rawColumn7 a=parityKernelFeature true a (0,4,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf1526,rf1541,rf1555,rf0013,rf1570,rf1583,rf1597,rf0013,rf0013,rf0013,rf1612,rf1626,rf1640,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0),parityOdd*parityMonomial (0,1,3),parityOdd*parityMonomial (0,3,2),parityOdd*parityMonomial (0,5,1),parityOdd*parityMonomial (0,7,0),parityOdd*parityMonomial (1,0,3),parityOdd*parityMonomial (1,2,2),parityOdd*parityMonomial (1,4,1),parityOdd*parityMonomial (1,6,0),parityOdd*parityMonomial (2,1,2),parityOdd*parityMonomial (2,3,1),parityOdd*parityMonomial (2,5,0),parityOdd*parityMonomial (3,0,2),parityOdd*parityMonomial (3,2,1),parityOdd*parityMonomial (3,4,0),parityOdd*parityMonomial (4,1,1),parityOdd*parityMonomial (4,3,0),parityOdd*parityMonomial (5,0,1),parityOdd*parityMonomial (5,2,0),parityOdd*parityMonomial (6,1,0),parityOdd*parityMonomial (7,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf1526.DefinedAt a) (h1 : rf1541.DefinedAt a) (h2 : rf1570.DefinedAt a) (h3 : rf1555.DefinedAt a) (h4 : rf1583.DefinedAt a) (h5 : rf1612.DefinedAt a) (h6 : rf1597.DefinedAt a) (h7 : rf1626.DefinedAt a) (h8 : rf1640.DefinedAt a) :
    rawColumn8 a=parityKernelFeature true a (0,4,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf1526,rf1541,rf1555,rf0013,rf1570,rf1583,rf1597,rf0013,rf0013,rf0013,rf1612,rf1626,rf1640,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0),parityOdd*parityMonomial (0,1,3),parityOdd*parityMonomial (0,3,2),parityOdd*parityMonomial (0,5,1),parityOdd*parityMonomial (0,7,0),parityOdd*parityMonomial (1,0,3),parityOdd*parityMonomial (1,2,2),parityOdd*parityMonomial (1,4,1),parityOdd*parityMonomial (1,6,0),parityOdd*parityMonomial (2,1,2),parityOdd*parityMonomial (2,3,1),parityOdd*parityMonomial (2,5,0),parityOdd*parityMonomial (3,0,2),parityOdd*parityMonomial (3,2,1),parityOdd*parityMonomial (3,4,0),parityOdd*parityMonomial (4,1,1),parityOdd*parityMonomial (4,3,0),parityOdd*parityMonomial (5,0,1),parityOdd*parityMonomial (5,2,0),parityOdd*parityMonomial (6,1,0),parityOdd*parityMonomial (7,0,0),parityOdd*parityMonomial (0,0,4),parityOdd*parityMonomial (0,2,3),parityOdd*parityMonomial (0,4,2),parityOdd*parityMonomial (0,6,1),parityOdd*parityMonomial (0,8,0),parityOdd*parityMonomial (1,1,3),parityOdd*parityMonomial (1,3,2),parityOdd*parityMonomial (1,5,1),parityOdd*parityMonomial (1,7,0),parityOdd*parityMonomial (2,0,3),parityOdd*parityMonomial (2,2,2),parityOdd*parityMonomial (2,4,1),parityOdd*parityMonomial (2,6,0),parityOdd*parityMonomial (3,1,2),parityOdd*parityMonomial (3,3,1),parityOdd*parityMonomial (3,5,0),parityOdd*parityMonomial (4,0,2),parityOdd*parityMonomial (4,2,1),parityOdd*parityMonomial (4,4,0),parityOdd*parityMonomial (5,1,1),parityOdd*parityMonomial (5,3,0),parityOdd*parityMonomial (6,0,1),parityOdd*parityMonomial (6,2,0),parityOdd*parityMonomial (7,1,0),parityOdd*parityMonomial (8,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf1526.DefinedAt a) (h1 : rf1541.DefinedAt a) (h2 : rf1570.DefinedAt a) (h3 : rf1555.DefinedAt a) (h4 : rf1583.DefinedAt a) (h5 : rf1612.DefinedAt a) (h6 : rf1597.DefinedAt a) (h7 : rf1626.DefinedAt a) (h8 : rf1640.DefinedAt a) :
    rawColumn9 a=parityKernelFeature true a (0,4,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Odd027
