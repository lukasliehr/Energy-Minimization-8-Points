import AllS.Units.N_GI.N_variance_sharp.N_absorption_operator
import AllS.Units.N_GI.N_signed_mean.N_basis_coefficients
import AllS.Units.N_GI.N_signed_mean.N_radical_operations

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceHeightData : MeanRadical := ![-1/7,2/7,0,0]
def varianceZData : MeanRadical := ![0,0,1,0]
def varianceRadiusSquareData : MeanRadical := ![8/7,-2/7,0,0]
def varianceSineData (k : Fin 2) : MeanRadical := if k=0 then ![0,1/2,0,0] else ![1,0,0,0]
def varianceCosineData (k : Fin 2) : MeanRadical := if k=0 then ![0,1/2,0,0] else 0
def varianceParityData (k : Fin 2) : MeanRadical := if k=0 then ![-1,0,0,0] else ![1,0,0,0]
def varianceMeridianData (k : Fin 2) : MeanRadical := if k=0 then ![-1,-1/2,0,0] else ![1,0,0,0]
def varianceWeightData (k : Fin 2) : MeanRadical := if k=0 then ![1,0,0,0] else ![1,1/2,0,0]
def varianceBasisKernel (p : Fin 8) (b : Fin 2) (i : Fin 16) : MeanRadical :=
  meanBasisData (finProdFinEquiv (p,b)) i

theorem varianceScalarData_eval (k : Fin 2) :
    meanRadicalEval varianceHeightData=packingHeight ∧
    meanRadicalEval varianceZData=packingZHeight ∧
    meanRadicalEval varianceRadiusSquareData=packingRadius^2 ∧
    meanRadicalEval (varianceSineData k)=contactSine k ∧
    meanRadicalEval (varianceCosineData k)=contactCosine k ∧
    meanRadicalEval (varianceParityData k)=contactParity k ∧
    meanRadicalEval (varianceMeridianData k)=contactMeridianFactor k ∧
    meanRadicalEval (varianceWeightData k)=contactWeight (0,k) := by
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  have hr := packing_parameters.2.2.2
  fin_cases k <;>
    norm_num [varianceHeightData,varianceZData,varianceRadiusSquareData,varianceSineData,
      varianceCosineData,varianceParityData,varianceMeridianData,varianceWeightData,
      meanRadicalEval,packingHeight,contactSine,contactCosine,contactParity,
      contactMeridianFactor,contactWeight,contactKappa_formula,div_eq_mul_inv,hi,hr,
      Fin.instOfNat,Fin.ofNat,Fin.succ,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] <;>
    (repeat' constructor) <;> ring

theorem varianceWeightData_eval (e : ContactIndex) :
    meanRadicalEval (varianceWeightData e.2)=contactWeight e :=
  (varianceScalarData_eval e.2).2.2.2.2.2.2.2

def varianceLinearKernel (e : ContactIndex) (i : Fin 16) : MeanRadical :=
  (-2:ℚ) • (meanRadicalMul (varianceSineData e.2)
    (varianceBasisKernel e.1 0 i-varianceBasisKernel (contactNext e) 0 i)+
    meanRadicalMul (meanRadicalMul varianceZData (varianceMeridianData e.2))
      (varianceBasisKernel e.1 1 i+varianceBasisKernel (contactNext e) 1 i))

def varianceDotKernel (p : Fin 8) (i j : Fin 16) : MeanRadical :=
  meanRadicalMul (varianceBasisKernel p 0 i) (varianceBasisKernel p 0 j)+
  meanRadicalMul (varianceBasisKernel p 1 i) (varianceBasisKernel p 1 j)

def varianceFrameKernel (e : ContactIndex) (i j : Fin 16) : MeanRadical :=
  meanRadicalMul (meanRadicalMul (varianceCosineData e.2) (varianceBasisKernel e.1 0 i))
    (varianceBasisKernel (contactNext e) 0 j)-
  meanRadicalMul (meanRadicalMul (meanRadicalMul varianceZData (varianceSineData e.2))
    (varianceBasisKernel e.1 0 i)) (varianceBasisKernel (contactNext e) 1 j)+
  meanRadicalMul (meanRadicalMul (meanRadicalMul varianceZData (varianceSineData e.2))
    (varianceBasisKernel e.1 1 i)) (varianceBasisKernel (contactNext e) 0 j)+
  meanRadicalMul (meanRadicalMul
    (meanRadicalMul varianceHeightData (varianceCosineData e.2)+
      meanRadicalMul varianceRadiusSquareData (varianceParityData e.2))
    (varianceBasisKernel e.1 1 i)) (varianceBasisKernel (contactNext e) 1 j)

def varianceMKernel (e : ContactIndex) (i j : Fin 16) : MeanRadical :=
  meanRadicalMul varianceHeightData (varianceDotKernel e.1 i j+varianceDotKernel (contactNext e) i j)-
    varianceFrameKernel e i j-varianceFrameKernel e j i

theorem varianceLinearKernel_eval (e : ContactIndex) (i : Fin 16) :
    contactLinearArray (meanFlatBasis i) e=packingRadius*meanRadicalEval (varianceLinearKernel e i) := by
  have hz := (varianceScalarData_eval e.2).2.1
  have hs := (varianceScalarData_eval e.2).2.2.2.1
  have hm := (varianceScalarData_eval e.2).2.2.2.2.2.2.1
  rw [contactLinearArray,contactLinear_cyclic_formula]
  simp only [varianceLinearKernel,meanRadicalEval_smul,meanRadicalEval_add,
    meanRadicalEval_mul,show ∀x y,meanRadicalEval (x-y)=meanRadicalEval x-meanRadicalEval y from
      fun x y=>meanRadicalEvalHom.map_sub x y,hz,hs,hm,varianceBasisKernel,
    meanFlatBasis_coordinates]
  norm_num
  ring

theorem varianceMKernel_eval (e : ContactIndex) (i j : Fin 16) :
    inner ℝ (meanFlatBasis i) (contactM e (meanFlatBasis j))=meanRadicalEval (varianceMKernel e i j) := by
  obtain ⟨hH,hZ,hR,hS,hC,hP,hM,hW⟩ := varianceScalarData_eval e.2
  have hr : packingRadius^2=1-packingHeight := by linarith [packing_parameters.2.2.2]
  rw [contactM_inner]
  simp only [contactMBilinear,contactFrameDot,meanFlatBasis_coordinates,
    varianceMKernel,varianceDotKernel,varianceFrameKernel,varianceBasisKernel,
    meanRadicalEval_add,meanRadicalEval_mul,
    show ∀x y,meanRadicalEval (x-y)=meanRadicalEval x-meanRadicalEval y from
      fun x y=>meanRadicalEvalHom.map_sub x y,hH,hZ,hR,hS,hC,hP,hr]

#print axioms varianceLinearKernel_eval
#print axioms varianceMKernel_eval
end Blueprint.Thomson.Tail.Implementation
