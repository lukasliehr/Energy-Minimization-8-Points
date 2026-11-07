import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0578
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0579
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0580
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0581
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0582
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0583
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0584
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0585
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0586
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0587
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0588
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0589
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0590
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0591
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0592
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0593
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0594
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0595
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0596
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0597
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0598
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0599
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0600
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0601
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0602
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0603
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0604
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0605
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0606
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0607
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0608
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0609
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0610
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0611
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0612
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0613
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0614
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0615
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0616
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0617
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0618
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0619
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0620
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0621
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0622
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0623
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogue.Entry0624
import AllS.Units.N_FI.N_raw_projection.RawScalarTensorSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetStandard
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Fintype.decidableForallFintype
def denominator : ℕ := 81
def tags : Fin 11 → StandardTag := ![(false,(0,0,0)),(false,(1,0,0)),(false,(0,1,0)),(false,(2,0,0)),(false,(0,0,1)),(false,(1,1,0)),(false,(3,0,0)),(true,(0,0,0)),(true,(1,0,0)),(true,(0,1,0)),(true,(2,0,0))]
def specs : Fin 47 → RawScalarSpec := ![RawScalarCatalogue.Entry0578.spec,RawScalarCatalogue.Entry0579.spec,RawScalarCatalogue.Entry0580.spec,RawScalarCatalogue.Entry0581.spec,RawScalarCatalogue.Entry0582.spec,RawScalarCatalogue.Entry0583.spec,RawScalarCatalogue.Entry0584.spec,RawScalarCatalogue.Entry0585.spec,RawScalarCatalogue.Entry0586.spec,RawScalarCatalogue.Entry0587.spec,RawScalarCatalogue.Entry0588.spec,RawScalarCatalogue.Entry0589.spec,RawScalarCatalogue.Entry0590.spec,RawScalarCatalogue.Entry0591.spec,RawScalarCatalogue.Entry0592.spec,RawScalarCatalogue.Entry0593.spec,RawScalarCatalogue.Entry0594.spec,RawScalarCatalogue.Entry0595.spec,RawScalarCatalogue.Entry0596.spec,RawScalarCatalogue.Entry0597.spec,RawScalarCatalogue.Entry0598.spec,RawScalarCatalogue.Entry0599.spec,RawScalarCatalogue.Entry0600.spec,RawScalarCatalogue.Entry0601.spec,RawScalarCatalogue.Entry0602.spec,RawScalarCatalogue.Entry0603.spec,RawScalarCatalogue.Entry0604.spec,RawScalarCatalogue.Entry0605.spec,RawScalarCatalogue.Entry0606.spec,RawScalarCatalogue.Entry0607.spec,RawScalarCatalogue.Entry0608.spec,RawScalarCatalogue.Entry0609.spec,RawScalarCatalogue.Entry0610.spec,RawScalarCatalogue.Entry0611.spec,RawScalarCatalogue.Entry0612.spec,RawScalarCatalogue.Entry0613.spec,RawScalarCatalogue.Entry0614.spec,RawScalarCatalogue.Entry0615.spec,RawScalarCatalogue.Entry0616.spec,RawScalarCatalogue.Entry0617.spec,RawScalarCatalogue.Entry0618.spec,RawScalarCatalogue.Entry0619.spec,RawScalarCatalogue.Entry0620.spec,RawScalarCatalogue.Entry0621.spec,RawScalarCatalogue.Entry0622.spec,RawScalarCatalogue.Entry0623.spec,RawScalarCatalogue.Entry0624.spec]
def entries : Fin 47 → RawCatalogue.SparsePoly := ![RawScalarCatalogue.Entry0578.entry,RawScalarCatalogue.Entry0579.entry,RawScalarCatalogue.Entry0580.entry,RawScalarCatalogue.Entry0581.entry,RawScalarCatalogue.Entry0582.entry,RawScalarCatalogue.Entry0583.entry,RawScalarCatalogue.Entry0584.entry,RawScalarCatalogue.Entry0585.entry,RawScalarCatalogue.Entry0586.entry,RawScalarCatalogue.Entry0587.entry,RawScalarCatalogue.Entry0588.entry,RawScalarCatalogue.Entry0589.entry,RawScalarCatalogue.Entry0590.entry,RawScalarCatalogue.Entry0591.entry,RawScalarCatalogue.Entry0592.entry,RawScalarCatalogue.Entry0593.entry,RawScalarCatalogue.Entry0594.entry,RawScalarCatalogue.Entry0595.entry,RawScalarCatalogue.Entry0596.entry,RawScalarCatalogue.Entry0597.entry,RawScalarCatalogue.Entry0598.entry,RawScalarCatalogue.Entry0599.entry,RawScalarCatalogue.Entry0600.entry,RawScalarCatalogue.Entry0601.entry,RawScalarCatalogue.Entry0602.entry,RawScalarCatalogue.Entry0603.entry,RawScalarCatalogue.Entry0604.entry,RawScalarCatalogue.Entry0605.entry,RawScalarCatalogue.Entry0606.entry,RawScalarCatalogue.Entry0607.entry,RawScalarCatalogue.Entry0608.entry,RawScalarCatalogue.Entry0609.entry,RawScalarCatalogue.Entry0610.entry,RawScalarCatalogue.Entry0611.entry,RawScalarCatalogue.Entry0612.entry,RawScalarCatalogue.Entry0613.entry,RawScalarCatalogue.Entry0614.entry,RawScalarCatalogue.Entry0615.entry,RawScalarCatalogue.Entry0616.entry,RawScalarCatalogue.Entry0617.entry,RawScalarCatalogue.Entry0618.entry,RawScalarCatalogue.Entry0619.entry,RawScalarCatalogue.Entry0620.entry,RawScalarCatalogue.Entry0621.entry,RawScalarCatalogue.Entry0622.entry,RawScalarCatalogue.Entry0623.entry,RawScalarCatalogue.Entry0624.entry]
def rawTemplates : Fin 47 → List (Tag × ℤ) := ![RawScalarCatalogue.Entry0578.raw81,RawScalarCatalogue.Entry0579.raw81,RawScalarCatalogue.Entry0580.raw81,RawScalarCatalogue.Entry0581.raw81,RawScalarCatalogue.Entry0582.raw81,RawScalarCatalogue.Entry0583.raw81,RawScalarCatalogue.Entry0584.raw81,RawScalarCatalogue.Entry0585.raw81,RawScalarCatalogue.Entry0586.raw81,RawScalarCatalogue.Entry0587.raw81,RawScalarCatalogue.Entry0588.raw81,RawScalarCatalogue.Entry0589.raw81,RawScalarCatalogue.Entry0590.raw81,RawScalarCatalogue.Entry0591.raw81,RawScalarCatalogue.Entry0592.raw81,RawScalarCatalogue.Entry0593.raw81,RawScalarCatalogue.Entry0594.raw81,RawScalarCatalogue.Entry0595.raw81,RawScalarCatalogue.Entry0596.raw81,RawScalarCatalogue.Entry0597.raw81,RawScalarCatalogue.Entry0598.raw81,RawScalarCatalogue.Entry0599.raw81,RawScalarCatalogue.Entry0600.raw81,RawScalarCatalogue.Entry0601.raw81,RawScalarCatalogue.Entry0602.raw81,RawScalarCatalogue.Entry0603.raw81,RawScalarCatalogue.Entry0604.raw81,RawScalarCatalogue.Entry0605.raw81,RawScalarCatalogue.Entry0606.raw81,RawScalarCatalogue.Entry0607.raw81,RawScalarCatalogue.Entry0608.raw81,RawScalarCatalogue.Entry0609.raw81,RawScalarCatalogue.Entry0610.raw81,RawScalarCatalogue.Entry0611.raw81,RawScalarCatalogue.Entry0612.raw81,RawScalarCatalogue.Entry0613.raw81,RawScalarCatalogue.Entry0614.raw81,RawScalarCatalogue.Entry0615.raw81,RawScalarCatalogue.Entry0616.raw81,RawScalarCatalogue.Entry0617.raw81,RawScalarCatalogue.Entry0618.raw81,RawScalarCatalogue.Entry0619.raw81,RawScalarCatalogue.Entry0620.raw81,RawScalarCatalogue.Entry0621.raw81,RawScalarCatalogue.Entry0622.raw81,RawScalarCatalogue.Entry0623.raw81,RawScalarCatalogue.Entry0624.raw81]
def indices : Matrix (Fin 11) (Fin 11) (Fin 47) := ![![0,1,2,3,4,5,6,7,8,9,10],![1,3,5,6,11,12,13,8,10,14,15],![2,5,16,12,17,18,19,9,14,20,21],![3,6,12,13,22,19,23,10,15,21,24],![4,11,17,22,25,26,27,28,29,30,31],![5,12,18,19,26,32,33,14,21,34,35],![6,13,19,23,27,33,36,15,24,35,37],![7,8,9,10,28,14,15,38,39,40,41],![8,10,14,15,29,21,24,39,41,42,43],![9,14,20,21,30,34,35,40,42,44,45],![10,15,21,24,31,35,37,41,43,45,46]]
def source : Matrix (Fin 11) (Fin 11) (List (Tag × ℤ)) := fun i j => rawTemplates (indices i j)
def coordinatePolynomial (i j : Fin 11) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem tags_source : List.ofFn tags=rawScalarTagList .mdetStandard 6 := by
  simp only [rawScalarTagList,standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide +kernel
theorem index_spec : ∀ i j,specs (indices i j)=rawScalarProductSpec .mdetStandard (tags i) (tags j) := by decide +kernel
theorem templates_normalize (i : Fin 47) : normalizeIntegerRawEntry denominator (rawTemplates i)=entries i := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0578.normalize_81
  · exact RawScalarCatalogue.Entry0579.normalize_81
  · exact RawScalarCatalogue.Entry0580.normalize_81
  · exact RawScalarCatalogue.Entry0581.normalize_81
  · exact RawScalarCatalogue.Entry0582.normalize_81
  · exact RawScalarCatalogue.Entry0583.normalize_81
  · exact RawScalarCatalogue.Entry0584.normalize_81
  · exact RawScalarCatalogue.Entry0585.normalize_81
  · exact RawScalarCatalogue.Entry0586.normalize_81
  · exact RawScalarCatalogue.Entry0587.normalize_81
  · exact RawScalarCatalogue.Entry0588.normalize_81
  · exact RawScalarCatalogue.Entry0589.normalize_81
  · exact RawScalarCatalogue.Entry0590.normalize_81
  · exact RawScalarCatalogue.Entry0591.normalize_81
  · exact RawScalarCatalogue.Entry0592.normalize_81
  · exact RawScalarCatalogue.Entry0593.normalize_81
  · exact RawScalarCatalogue.Entry0594.normalize_81
  · exact RawScalarCatalogue.Entry0595.normalize_81
  · exact RawScalarCatalogue.Entry0596.normalize_81
  · exact RawScalarCatalogue.Entry0597.normalize_81
  · exact RawScalarCatalogue.Entry0598.normalize_81
  · exact RawScalarCatalogue.Entry0599.normalize_81
  · exact RawScalarCatalogue.Entry0600.normalize_81
  · exact RawScalarCatalogue.Entry0601.normalize_81
  · exact RawScalarCatalogue.Entry0602.normalize_81
  · exact RawScalarCatalogue.Entry0603.normalize_81
  · exact RawScalarCatalogue.Entry0604.normalize_81
  · exact RawScalarCatalogue.Entry0605.normalize_81
  · exact RawScalarCatalogue.Entry0606.normalize_81
  · exact RawScalarCatalogue.Entry0607.normalize_81
  · exact RawScalarCatalogue.Entry0608.normalize_81
  · exact RawScalarCatalogue.Entry0609.normalize_81
  · exact RawScalarCatalogue.Entry0610.normalize_81
  · exact RawScalarCatalogue.Entry0611.normalize_81
  · exact RawScalarCatalogue.Entry0612.normalize_81
  · exact RawScalarCatalogue.Entry0613.normalize_81
  · exact RawScalarCatalogue.Entry0614.normalize_81
  · exact RawScalarCatalogue.Entry0615.normalize_81
  · exact RawScalarCatalogue.Entry0616.normalize_81
  · exact RawScalarCatalogue.Entry0617.normalize_81
  · exact RawScalarCatalogue.Entry0618.normalize_81
  · exact RawScalarCatalogue.Entry0619.normalize_81
  · exact RawScalarCatalogue.Entry0620.normalize_81
  · exact RawScalarCatalogue.Entry0621.normalize_81
  · exact RawScalarCatalogue.Entry0622.normalize_81
  · exact RawScalarCatalogue.Entry0623.normalize_81
  · exact RawScalarCatalogue.Entry0624.normalize_81
theorem templates_identity (i : Fin 47) : RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (entries i))=rawScalarCoordinates (specs i) := by
  fin_cases i
  · exact RawScalarCatalogue.Entry0578.identity
  · exact RawScalarCatalogue.Entry0579.identity
  · exact RawScalarCatalogue.Entry0580.identity
  · exact RawScalarCatalogue.Entry0581.identity
  · exact RawScalarCatalogue.Entry0582.identity
  · exact RawScalarCatalogue.Entry0583.identity
  · exact RawScalarCatalogue.Entry0584.identity
  · exact RawScalarCatalogue.Entry0585.identity
  · exact RawScalarCatalogue.Entry0586.identity
  · exact RawScalarCatalogue.Entry0587.identity
  · exact RawScalarCatalogue.Entry0588.identity
  · exact RawScalarCatalogue.Entry0589.identity
  · exact RawScalarCatalogue.Entry0590.identity
  · exact RawScalarCatalogue.Entry0591.identity
  · exact RawScalarCatalogue.Entry0592.identity
  · exact RawScalarCatalogue.Entry0593.identity
  · exact RawScalarCatalogue.Entry0594.identity
  · exact RawScalarCatalogue.Entry0595.identity
  · exact RawScalarCatalogue.Entry0596.identity
  · exact RawScalarCatalogue.Entry0597.identity
  · exact RawScalarCatalogue.Entry0598.identity
  · exact RawScalarCatalogue.Entry0599.identity
  · exact RawScalarCatalogue.Entry0600.identity
  · exact RawScalarCatalogue.Entry0601.identity
  · exact RawScalarCatalogue.Entry0602.identity
  · exact RawScalarCatalogue.Entry0603.identity
  · exact RawScalarCatalogue.Entry0604.identity
  · exact RawScalarCatalogue.Entry0605.identity
  · exact RawScalarCatalogue.Entry0606.identity
  · exact RawScalarCatalogue.Entry0607.identity
  · exact RawScalarCatalogue.Entry0608.identity
  · exact RawScalarCatalogue.Entry0609.identity
  · exact RawScalarCatalogue.Entry0610.identity
  · exact RawScalarCatalogue.Entry0611.identity
  · exact RawScalarCatalogue.Entry0612.identity
  · exact RawScalarCatalogue.Entry0613.identity
  · exact RawScalarCatalogue.Entry0614.identity
  · exact RawScalarCatalogue.Entry0615.identity
  · exact RawScalarCatalogue.Entry0616.identity
  · exact RawScalarCatalogue.Entry0617.identity
  · exact RawScalarCatalogue.Entry0618.identity
  · exact RawScalarCatalogue.Entry0619.identity
  · exact RawScalarCatalogue.Entry0620.identity
  · exact RawScalarCatalogue.Entry0621.identity
  · exact RawScalarCatalogue.Entry0622.identity
  · exact RawScalarCatalogue.Entry0623.identity
  · exact RawScalarCatalogue.Entry0624.identity
theorem subst_coordinatePolynomial (i j : Fin 11) :
    invariantSubst (coordinatePolynomial i j)=rawScalarBilinear .mdetStandard (tags i) (tags j) := by
  simp only [coordinatePolynomial,source,templates_normalize,templates_identity,index_spec,rawScalarProductSpec_subst]
#print axioms tags_source
#print axioms index_spec
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawScalarTensors.D12_mdetStandard
