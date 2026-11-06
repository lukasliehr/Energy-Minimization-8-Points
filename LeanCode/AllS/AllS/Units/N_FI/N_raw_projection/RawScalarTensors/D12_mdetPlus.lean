import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0535
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0536
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0537
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0538
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0539
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0540
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0541
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0542
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0543
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0544
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0545
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0546
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0547
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0548
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0549
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0550
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0551
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0552
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0553
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0554
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0555
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0556
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0557
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0558
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0559
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0560
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0561
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0562
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0563
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0564
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0565
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0566
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0567
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0568
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0569
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0570
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0571
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0572
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0573
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0574
import AllS.Units.N_FI.N_raw_projection.RawScalarTensorSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetPlus
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Fintype.decidableForallFintype
def denominator : ℕ := 1
def tags : Fin 11 → StandardTag := ![(false,(0,0,0)),(false,(1,0,0)),(false,(0,1,0)),(false,(2,0,0)),(false,(0,0,1)),(false,(1,1,0)),(false,(3,0,0)),(false,(0,2,0)),(false,(1,0,1)),(false,(2,1,0)),(false,(4,0,0))]
def specs : Fin 40 → RawScalarSpec := ![RawScalarCatalogue.Entry0535.spec,RawScalarCatalogue.Entry0536.spec,RawScalarCatalogue.Entry0537.spec,RawScalarCatalogue.Entry0538.spec,RawScalarCatalogue.Entry0539.spec,RawScalarCatalogue.Entry0540.spec,RawScalarCatalogue.Entry0541.spec,RawScalarCatalogue.Entry0542.spec,RawScalarCatalogue.Entry0543.spec,RawScalarCatalogue.Entry0544.spec,RawScalarCatalogue.Entry0545.spec,RawScalarCatalogue.Entry0546.spec,RawScalarCatalogue.Entry0547.spec,RawScalarCatalogue.Entry0548.spec,RawScalarCatalogue.Entry0549.spec,RawScalarCatalogue.Entry0550.spec,RawScalarCatalogue.Entry0551.spec,RawScalarCatalogue.Entry0552.spec,RawScalarCatalogue.Entry0553.spec,RawScalarCatalogue.Entry0554.spec,RawScalarCatalogue.Entry0555.spec,RawScalarCatalogue.Entry0556.spec,RawScalarCatalogue.Entry0557.spec,RawScalarCatalogue.Entry0558.spec,RawScalarCatalogue.Entry0559.spec,RawScalarCatalogue.Entry0560.spec,RawScalarCatalogue.Entry0561.spec,RawScalarCatalogue.Entry0562.spec,RawScalarCatalogue.Entry0563.spec,RawScalarCatalogue.Entry0564.spec,RawScalarCatalogue.Entry0565.spec,RawScalarCatalogue.Entry0566.spec,RawScalarCatalogue.Entry0567.spec,RawScalarCatalogue.Entry0568.spec,RawScalarCatalogue.Entry0569.spec,RawScalarCatalogue.Entry0570.spec,RawScalarCatalogue.Entry0571.spec,RawScalarCatalogue.Entry0572.spec,RawScalarCatalogue.Entry0573.spec,RawScalarCatalogue.Entry0574.spec]
def entries : Fin 40 → RawCatalogue.SparsePoly := ![RawScalarCatalogue.Entry0535.entry,RawScalarCatalogue.Entry0536.entry,RawScalarCatalogue.Entry0537.entry,RawScalarCatalogue.Entry0538.entry,RawScalarCatalogue.Entry0539.entry,RawScalarCatalogue.Entry0540.entry,RawScalarCatalogue.Entry0541.entry,RawScalarCatalogue.Entry0542.entry,RawScalarCatalogue.Entry0543.entry,RawScalarCatalogue.Entry0544.entry,RawScalarCatalogue.Entry0545.entry,RawScalarCatalogue.Entry0546.entry,RawScalarCatalogue.Entry0547.entry,RawScalarCatalogue.Entry0548.entry,RawScalarCatalogue.Entry0549.entry,RawScalarCatalogue.Entry0550.entry,RawScalarCatalogue.Entry0551.entry,RawScalarCatalogue.Entry0552.entry,RawScalarCatalogue.Entry0553.entry,RawScalarCatalogue.Entry0554.entry,RawScalarCatalogue.Entry0555.entry,RawScalarCatalogue.Entry0556.entry,RawScalarCatalogue.Entry0557.entry,RawScalarCatalogue.Entry0558.entry,RawScalarCatalogue.Entry0559.entry,RawScalarCatalogue.Entry0560.entry,RawScalarCatalogue.Entry0561.entry,RawScalarCatalogue.Entry0562.entry,RawScalarCatalogue.Entry0563.entry,RawScalarCatalogue.Entry0564.entry,RawScalarCatalogue.Entry0565.entry,RawScalarCatalogue.Entry0566.entry,RawScalarCatalogue.Entry0567.entry,RawScalarCatalogue.Entry0568.entry,RawScalarCatalogue.Entry0569.entry,RawScalarCatalogue.Entry0570.entry,RawScalarCatalogue.Entry0571.entry,RawScalarCatalogue.Entry0572.entry,RawScalarCatalogue.Entry0573.entry,RawScalarCatalogue.Entry0574.entry]
def rawTemplates : Fin 40 → List (Tag × ℤ) := ![RawScalarCatalogue.Entry0535.raw1,RawScalarCatalogue.Entry0536.raw1,RawScalarCatalogue.Entry0537.raw1,RawScalarCatalogue.Entry0538.raw1,RawScalarCatalogue.Entry0539.raw1,RawScalarCatalogue.Entry0540.raw1,RawScalarCatalogue.Entry0541.raw1,RawScalarCatalogue.Entry0542.raw1,RawScalarCatalogue.Entry0543.raw1,RawScalarCatalogue.Entry0544.raw1,RawScalarCatalogue.Entry0545.raw1,RawScalarCatalogue.Entry0546.raw1,RawScalarCatalogue.Entry0547.raw1,RawScalarCatalogue.Entry0548.raw1,RawScalarCatalogue.Entry0549.raw1,RawScalarCatalogue.Entry0550.raw1,RawScalarCatalogue.Entry0551.raw1,RawScalarCatalogue.Entry0552.raw1,RawScalarCatalogue.Entry0553.raw1,RawScalarCatalogue.Entry0554.raw1,RawScalarCatalogue.Entry0555.raw1,RawScalarCatalogue.Entry0556.raw1,RawScalarCatalogue.Entry0557.raw1,RawScalarCatalogue.Entry0558.raw1,RawScalarCatalogue.Entry0559.raw1,RawScalarCatalogue.Entry0560.raw1,RawScalarCatalogue.Entry0561.raw1,RawScalarCatalogue.Entry0562.raw1,RawScalarCatalogue.Entry0563.raw1,RawScalarCatalogue.Entry0564.raw1,RawScalarCatalogue.Entry0565.raw1,RawScalarCatalogue.Entry0566.raw1,RawScalarCatalogue.Entry0567.raw1,RawScalarCatalogue.Entry0568.raw1,RawScalarCatalogue.Entry0569.raw1,RawScalarCatalogue.Entry0570.raw1,RawScalarCatalogue.Entry0571.raw1,RawScalarCatalogue.Entry0572.raw1,RawScalarCatalogue.Entry0573.raw1,RawScalarCatalogue.Entry0574.raw1]
def indices : Matrix (Fin 11) (Fin 11) (Fin 40) := ![![0,1,2,3,4,5,6,7,8,9,10],![1,3,5,6,8,9,10,11,12,13,14],![2,5,7,9,15,11,13,16,17,18,19],![3,6,9,10,12,13,14,18,20,19,21],![4,8,15,12,22,17,20,23,24,25,26],![5,9,11,13,17,18,19,27,25,28,29],![6,10,13,14,20,19,21,28,26,29,30],![7,11,16,18,23,27,28,31,32,33,34],![8,12,17,20,24,25,26,32,35,36,37],![9,13,18,19,25,28,29,33,36,34,38],![10,14,19,21,26,29,30,34,37,38,39]]
def source : Matrix (Fin 11) (Fin 11) (List (Tag × ℤ)) := fun i j => rawTemplates (indices i j)
def coordinatePolynomial (i j : Fin 11) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem tags_source : List.ofFn tags=rawScalarTagList .mdetPlus 6 := by
  simp only [rawScalarTagList,standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide +kernel
theorem index_spec : ∀ i j,specs (indices i j)=rawScalarProductSpec .mdetPlus (tags i) (tags j) := by decide +kernel
theorem templates_normalize (i : Fin 40) : normalizeIntegerRawEntry denominator (rawTemplates i)=entries i := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0535.normalize_1
  · exact RawScalarCatalogue.Entry0536.normalize_1
  · exact RawScalarCatalogue.Entry0537.normalize_1
  · exact RawScalarCatalogue.Entry0538.normalize_1
  · exact RawScalarCatalogue.Entry0539.normalize_1
  · exact RawScalarCatalogue.Entry0540.normalize_1
  · exact RawScalarCatalogue.Entry0541.normalize_1
  · exact RawScalarCatalogue.Entry0542.normalize_1
  · exact RawScalarCatalogue.Entry0543.normalize_1
  · exact RawScalarCatalogue.Entry0544.normalize_1
  · exact RawScalarCatalogue.Entry0545.normalize_1
  · exact RawScalarCatalogue.Entry0546.normalize_1
  · exact RawScalarCatalogue.Entry0547.normalize_1
  · exact RawScalarCatalogue.Entry0548.normalize_1
  · exact RawScalarCatalogue.Entry0549.normalize_1
  · exact RawScalarCatalogue.Entry0550.normalize_1
  · exact RawScalarCatalogue.Entry0551.normalize_1
  · exact RawScalarCatalogue.Entry0552.normalize_1
  · exact RawScalarCatalogue.Entry0553.normalize_1
  · exact RawScalarCatalogue.Entry0554.normalize_1
  · exact RawScalarCatalogue.Entry0555.normalize_1
  · exact RawScalarCatalogue.Entry0556.normalize_1
  · exact RawScalarCatalogue.Entry0557.normalize_1
  · exact RawScalarCatalogue.Entry0558.normalize_1
  · exact RawScalarCatalogue.Entry0559.normalize_1
  · exact RawScalarCatalogue.Entry0560.normalize_1
  · exact RawScalarCatalogue.Entry0561.normalize_1
  · exact RawScalarCatalogue.Entry0562.normalize_1
  · exact RawScalarCatalogue.Entry0563.normalize_1
  · exact RawScalarCatalogue.Entry0564.normalize_1
  · exact RawScalarCatalogue.Entry0565.normalize_1
  · exact RawScalarCatalogue.Entry0566.normalize_1
  · exact RawScalarCatalogue.Entry0567.normalize_1
  · exact RawScalarCatalogue.Entry0568.normalize_1
  · exact RawScalarCatalogue.Entry0569.normalize_1
  · exact RawScalarCatalogue.Entry0570.normalize_1
  · exact RawScalarCatalogue.Entry0571.normalize_1
  · exact RawScalarCatalogue.Entry0572.normalize_1
  · exact RawScalarCatalogue.Entry0573.normalize_1
  · exact RawScalarCatalogue.Entry0574.normalize_1
theorem templates_identity (i : Fin 40) : RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (entries i))=rawScalarCoordinates (specs i) := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0535.identity
  · exact RawScalarCatalogue.Entry0536.identity
  · exact RawScalarCatalogue.Entry0537.identity
  · exact RawScalarCatalogue.Entry0538.identity
  · exact RawScalarCatalogue.Entry0539.identity
  · exact RawScalarCatalogue.Entry0540.identity
  · exact RawScalarCatalogue.Entry0541.identity
  · exact RawScalarCatalogue.Entry0542.identity
  · exact RawScalarCatalogue.Entry0543.identity
  · exact RawScalarCatalogue.Entry0544.identity
  · exact RawScalarCatalogue.Entry0545.identity
  · exact RawScalarCatalogue.Entry0546.identity
  · exact RawScalarCatalogue.Entry0547.identity
  · exact RawScalarCatalogue.Entry0548.identity
  · exact RawScalarCatalogue.Entry0549.identity
  · exact RawScalarCatalogue.Entry0550.identity
  · exact RawScalarCatalogue.Entry0551.identity
  · exact RawScalarCatalogue.Entry0552.identity
  · exact RawScalarCatalogue.Entry0553.identity
  · exact RawScalarCatalogue.Entry0554.identity
  · exact RawScalarCatalogue.Entry0555.identity
  · exact RawScalarCatalogue.Entry0556.identity
  · exact RawScalarCatalogue.Entry0557.identity
  · exact RawScalarCatalogue.Entry0558.identity
  · exact RawScalarCatalogue.Entry0559.identity
  · exact RawScalarCatalogue.Entry0560.identity
  · exact RawScalarCatalogue.Entry0561.identity
  · exact RawScalarCatalogue.Entry0562.identity
  · exact RawScalarCatalogue.Entry0563.identity
  · exact RawScalarCatalogue.Entry0564.identity
  · exact RawScalarCatalogue.Entry0565.identity
  · exact RawScalarCatalogue.Entry0566.identity
  · exact RawScalarCatalogue.Entry0567.identity
  · exact RawScalarCatalogue.Entry0568.identity
  · exact RawScalarCatalogue.Entry0569.identity
  · exact RawScalarCatalogue.Entry0570.identity
  · exact RawScalarCatalogue.Entry0571.identity
  · exact RawScalarCatalogue.Entry0572.identity
  · exact RawScalarCatalogue.Entry0573.identity
  · exact RawScalarCatalogue.Entry0574.identity
theorem subst_coordinatePolynomial (i j : Fin 11) :
    invariantSubst (coordinatePolynomial i j)=rawScalarBilinear .mdetPlus (tags i) (tags j) := by
  simp only [coordinatePolynomial,source,templates_normalize,templates_identity,index_spec,rawScalarProductSpec_subst]
#print axioms tags_source
#print axioms index_spec
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetPlus
