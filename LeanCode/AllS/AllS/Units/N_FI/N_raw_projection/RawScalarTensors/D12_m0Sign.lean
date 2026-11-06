import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0102
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0103
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0104
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0105
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0106
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0107
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0108
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0109
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0110
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0111
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0112
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0113
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0114
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0115
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0116
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0117
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0118
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0119
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0120
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0121
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0122
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0123
import AllS.Units.N_FI.N_raw_projection.RawScalarTensorSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawScalarTensors.D12_m0Sign
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Fintype.decidableForallFintype
def denominator : ℕ := 1
def tags : Fin 7 → StandardTag := ![(false,(0,0,0)),(false,(1,0,0)),(false,(0,1,0)),(false,(2,0,0)),(false,(0,0,1)),(false,(1,1,0)),(false,(3,0,0))]
def specs : Fin 22 → RawScalarSpec := ![RawScalarCatalogue.Entry0102.spec,RawScalarCatalogue.Entry0103.spec,RawScalarCatalogue.Entry0104.spec,RawScalarCatalogue.Entry0105.spec,RawScalarCatalogue.Entry0106.spec,RawScalarCatalogue.Entry0107.spec,RawScalarCatalogue.Entry0108.spec,RawScalarCatalogue.Entry0109.spec,RawScalarCatalogue.Entry0110.spec,RawScalarCatalogue.Entry0111.spec,RawScalarCatalogue.Entry0112.spec,RawScalarCatalogue.Entry0113.spec,RawScalarCatalogue.Entry0114.spec,RawScalarCatalogue.Entry0115.spec,RawScalarCatalogue.Entry0116.spec,RawScalarCatalogue.Entry0117.spec,RawScalarCatalogue.Entry0118.spec,RawScalarCatalogue.Entry0119.spec,RawScalarCatalogue.Entry0120.spec,RawScalarCatalogue.Entry0121.spec,RawScalarCatalogue.Entry0122.spec,RawScalarCatalogue.Entry0123.spec]
def entries : Fin 22 → RawCatalogue.SparsePoly := ![RawScalarCatalogue.Entry0102.entry,RawScalarCatalogue.Entry0103.entry,RawScalarCatalogue.Entry0104.entry,RawScalarCatalogue.Entry0105.entry,RawScalarCatalogue.Entry0106.entry,RawScalarCatalogue.Entry0107.entry,RawScalarCatalogue.Entry0108.entry,RawScalarCatalogue.Entry0109.entry,RawScalarCatalogue.Entry0110.entry,RawScalarCatalogue.Entry0111.entry,RawScalarCatalogue.Entry0112.entry,RawScalarCatalogue.Entry0113.entry,RawScalarCatalogue.Entry0114.entry,RawScalarCatalogue.Entry0115.entry,RawScalarCatalogue.Entry0116.entry,RawScalarCatalogue.Entry0117.entry,RawScalarCatalogue.Entry0118.entry,RawScalarCatalogue.Entry0119.entry,RawScalarCatalogue.Entry0120.entry,RawScalarCatalogue.Entry0121.entry,RawScalarCatalogue.Entry0122.entry,RawScalarCatalogue.Entry0123.entry]
def rawTemplates : Fin 22 → List (Tag × ℤ) := ![RawScalarCatalogue.Entry0102.raw1,RawScalarCatalogue.Entry0103.raw1,RawScalarCatalogue.Entry0104.raw1,RawScalarCatalogue.Entry0105.raw1,RawScalarCatalogue.Entry0106.raw1,RawScalarCatalogue.Entry0107.raw1,RawScalarCatalogue.Entry0108.raw1,RawScalarCatalogue.Entry0109.raw1,RawScalarCatalogue.Entry0110.raw1,RawScalarCatalogue.Entry0111.raw1,RawScalarCatalogue.Entry0112.raw1,RawScalarCatalogue.Entry0113.raw1,RawScalarCatalogue.Entry0114.raw1,RawScalarCatalogue.Entry0115.raw1,RawScalarCatalogue.Entry0116.raw1,RawScalarCatalogue.Entry0117.raw1,RawScalarCatalogue.Entry0118.raw1,RawScalarCatalogue.Entry0119.raw1,RawScalarCatalogue.Entry0120.raw1,RawScalarCatalogue.Entry0121.raw1,RawScalarCatalogue.Entry0122.raw1,RawScalarCatalogue.Entry0123.raw1]
def indices : Matrix (Fin 7) (Fin 7) (Fin 22) := ![![0,1,2,3,4,5,6],![1,3,5,6,7,8,9],![2,5,10,8,11,12,13],![3,6,8,9,14,13,15],![4,7,11,14,16,17,18],![5,8,12,13,17,19,20],![6,9,13,15,18,20,21]]
def source : Matrix (Fin 7) (Fin 7) (List (Tag × ℤ)) := fun i j => rawTemplates (indices i j)
def coordinatePolynomial (i j : Fin 7) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem tags_source : List.ofFn tags=rawScalarTagList .m0Sign 6 := by
  simp only [rawScalarTagList,standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide +kernel
theorem index_spec : ∀ i j,specs (indices i j)=rawScalarProductSpec .m0Sign (tags i) (tags j) := by decide +kernel
theorem templates_normalize (i : Fin 22) : normalizeIntegerRawEntry denominator (rawTemplates i)=entries i := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0102.normalize_1
  · exact RawScalarCatalogue.Entry0103.normalize_1
  · exact RawScalarCatalogue.Entry0104.normalize_1
  · exact RawScalarCatalogue.Entry0105.normalize_1
  · exact RawScalarCatalogue.Entry0106.normalize_1
  · exact RawScalarCatalogue.Entry0107.normalize_1
  · exact RawScalarCatalogue.Entry0108.normalize_1
  · exact RawScalarCatalogue.Entry0109.normalize_1
  · exact RawScalarCatalogue.Entry0110.normalize_1
  · exact RawScalarCatalogue.Entry0111.normalize_1
  · exact RawScalarCatalogue.Entry0112.normalize_1
  · exact RawScalarCatalogue.Entry0113.normalize_1
  · exact RawScalarCatalogue.Entry0114.normalize_1
  · exact RawScalarCatalogue.Entry0115.normalize_1
  · exact RawScalarCatalogue.Entry0116.normalize_1
  · exact RawScalarCatalogue.Entry0117.normalize_1
  · exact RawScalarCatalogue.Entry0118.normalize_1
  · exact RawScalarCatalogue.Entry0119.normalize_1
  · exact RawScalarCatalogue.Entry0120.normalize_1
  · exact RawScalarCatalogue.Entry0121.normalize_1
  · exact RawScalarCatalogue.Entry0122.normalize_1
  · exact RawScalarCatalogue.Entry0123.normalize_1
theorem templates_identity (i : Fin 22) : RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (entries i))=rawScalarCoordinates (specs i) := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0102.identity
  · exact RawScalarCatalogue.Entry0103.identity
  · exact RawScalarCatalogue.Entry0104.identity
  · exact RawScalarCatalogue.Entry0105.identity
  · exact RawScalarCatalogue.Entry0106.identity
  · exact RawScalarCatalogue.Entry0107.identity
  · exact RawScalarCatalogue.Entry0108.identity
  · exact RawScalarCatalogue.Entry0109.identity
  · exact RawScalarCatalogue.Entry0110.identity
  · exact RawScalarCatalogue.Entry0111.identity
  · exact RawScalarCatalogue.Entry0112.identity
  · exact RawScalarCatalogue.Entry0113.identity
  · exact RawScalarCatalogue.Entry0114.identity
  · exact RawScalarCatalogue.Entry0115.identity
  · exact RawScalarCatalogue.Entry0116.identity
  · exact RawScalarCatalogue.Entry0117.identity
  · exact RawScalarCatalogue.Entry0118.identity
  · exact RawScalarCatalogue.Entry0119.identity
  · exact RawScalarCatalogue.Entry0120.identity
  · exact RawScalarCatalogue.Entry0121.identity
  · exact RawScalarCatalogue.Entry0122.identity
  · exact RawScalarCatalogue.Entry0123.identity
theorem subst_coordinatePolynomial (i j : Fin 7) :
    invariantSubst (coordinatePolynomial i j)=rawScalarBilinear .m0Sign (tags i) (tags j) := by
  simp only [coordinatePolynomial,source,templates_normalize,templates_identity,index_spec,rawScalarProductSpec_subst]
#print axioms tags_source
#print axioms index_spec
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawScalarTensors.D12_m0Sign
