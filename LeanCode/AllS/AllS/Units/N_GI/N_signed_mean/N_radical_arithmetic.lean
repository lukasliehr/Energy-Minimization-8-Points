import AllS.Units.N_GI.N_nearest_chart.N_frame

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Exact coefficients in the physical tower Q(sqrt(2), packingZHeight). -/
abbrev MeanRadical := Fin 4 → ℚ

def meanRadicalEval (x : MeanRadical) : ℝ :=
  x 0+(x 1:ℝ)*Real.sqrt 2+(x 2:ℝ)*packingZHeight+(x 3:ℝ)*Real.sqrt 2*packingZHeight

def meanRadicalMul (x y : MeanRadical) : MeanRadical :=
  ![x 0*y 0+2*x 1*y 1-(x 2*y 2+2*x 3*y 3)/7+4*(x 2*y 3+x 3*y 2)/7,
    x 0*y 1+x 1*y 0+2*(x 2*y 2+2*x 3*y 3)/7-(x 2*y 3+x 3*y 2)/7,
    x 0*y 2+2*x 1*y 3+x 2*y 0+2*x 3*y 1,
    x 0*y 3+x 1*y 2+x 2*y 1+x 3*y 0]

def meanRadicalEvalHom : MeanRadical →+ ℝ where
  toFun := meanRadicalEval
  map_zero' := by simp [meanRadicalEval]
  map_add' x y := by simp [meanRadicalEval]; ring

theorem meanRadicalEval_sum {ι : Type*} (s : Finset ι) (f : ι → MeanRadical) :
    meanRadicalEval (∑i∈s,f i)=∑i∈s,meanRadicalEval (f i) := map_sum meanRadicalEvalHom f s

theorem meanRadicalEval_mul (x y : MeanRadical) :
    meanRadicalEval (meanRadicalMul x y)=meanRadicalEval x*meanRadicalEval y := by
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt (2:ℝ))^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
  have hH := packing_parameters.2.2.1
  norm_num [meanRadicalEval,meanRadicalMul]
  push_cast
  ring_nf
  simp only [hH,packingHeight,hs,hs3]
  ring_nf
  simp only [hs,hs3]
  ring

def meanRadicalMatrixMul {m n k : ℕ} (A : Fin m → Fin n → MeanRadical)
    (B : Fin n → Fin k → MeanRadical) : Fin m → Fin k → MeanRadical :=
  fun i j=>∑t,meanRadicalMul (A i t) (B t j)

theorem meanRadicalMatrixMul_eval {m n k : ℕ} (A : Fin m → Fin n → MeanRadical)
    (B : Fin n → Fin k → MeanRadical) (i : Fin m) (j : Fin k) :
    meanRadicalEval (meanRadicalMatrixMul A B i j)=∑t,meanRadicalEval (A i t)*meanRadicalEval (B t j) := by
  simp only [meanRadicalMatrixMul,meanRadicalEval_sum,meanRadicalEval_mul]

#print axioms meanRadicalEval_mul
end Blueprint.Thomson.Tail.Implementation
