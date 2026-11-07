import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0575
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0576
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0577
import AllS.Units.N_FI.N_raw_projection.RawScalarTensorSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetSign
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Fintype.decidableForallFintype
def denominator : ℕ := 1
def tags : Fin 2 → StandardTag := ![(false,(0,0,0)),(false,(1,0,0))]
def specs : Fin 3 → RawScalarSpec := ![RawScalarCatalogue.Entry0575.spec,RawScalarCatalogue.Entry0576.spec,RawScalarCatalogue.Entry0577.spec]
def entries : Fin 3 → RawCatalogue.SparsePoly := ![RawScalarCatalogue.Entry0575.entry,RawScalarCatalogue.Entry0576.entry,RawScalarCatalogue.Entry0577.entry]
def rawTemplates : Fin 3 → List (Tag × ℤ) := ![RawScalarCatalogue.Entry0575.raw1,RawScalarCatalogue.Entry0576.raw1,RawScalarCatalogue.Entry0577.raw1]
def indices : Matrix (Fin 2) (Fin 2) (Fin 3) := ![![0,1],![1,2]]
def source : Matrix (Fin 2) (Fin 2) (List (Tag × ℤ)) := fun i j => rawTemplates (indices i j)
def coordinatePolynomial (i j : Fin 2) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem tags_source : List.ofFn tags=rawScalarTagList .mdetSign 6 := by
  simp only [rawScalarTagList,standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide +kernel
theorem index_spec : ∀ i j,specs (indices i j)=rawScalarProductSpec .mdetSign (tags i) (tags j) := by decide +kernel
theorem templates_normalize (i : Fin 3) : normalizeIntegerRawEntry denominator (rawTemplates i)=entries i := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0575.normalize_1
  · exact RawScalarCatalogue.Entry0576.normalize_1
  · exact RawScalarCatalogue.Entry0577.normalize_1
theorem templates_identity (i : Fin 3) : RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (entries i))=rawScalarCoordinates (specs i) := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0575.identity
  · exact RawScalarCatalogue.Entry0576.identity
  · exact RawScalarCatalogue.Entry0577.identity
theorem subst_coordinatePolynomial (i j : Fin 2) :
    invariantSubst (coordinatePolynomial i j)=rawScalarBilinear .mdetSign (tags i) (tags j) := by
  simp only [coordinatePolynomial,source,templates_normalize,templates_identity,index_spec,rawScalarProductSpec_subst]
#print axioms tags_source
#print axioms index_spec
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetSign
