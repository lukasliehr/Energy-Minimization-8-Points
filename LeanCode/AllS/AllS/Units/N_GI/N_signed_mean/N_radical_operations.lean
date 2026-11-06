import AllS.Units.N_GI.N_signed_mean.N_radical_arithmetic

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanRadicalMul_comm (x y : MeanRadical) : meanRadicalMul x y=meanRadicalMul y x := by
  ext i
  fin_cases i <;> norm_num [meanRadicalMul] <;> ring

theorem meanRadicalEval_add (x y : MeanRadical) :
    meanRadicalEval (x+y)=meanRadicalEval x+meanRadicalEval y :=
  meanRadicalEvalHom.map_add x y

theorem meanRadicalEval_smul (r : ℚ) (x : MeanRadical) :
    meanRadicalEval (r • x)=(r:ℝ)*meanRadicalEval x := by
  simp [meanRadicalEval]
  ring

theorem meanRadicalEval_neg (x : MeanRadical) : meanRadicalEval (-x)= -meanRadicalEval x :=
  map_neg meanRadicalEvalHom x

end Blueprint.Thomson.Tail.Implementation
