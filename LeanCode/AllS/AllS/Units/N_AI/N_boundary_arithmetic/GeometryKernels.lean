import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple00
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple01
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple02
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple03
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple04
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple05
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple06
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple07
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple08
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple09
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple10
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple11
import AllS.Units.N_AI.N_boundary_arithmetic.GeometryTriple12
import AllS.Units.N_GI.N_boundary_polynomials.N_polynomial_model

namespace Blueprint.CAP.BoundaryDirect
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

theorem triple_physical (j : Fin 13) (i : Fin 8) (k : Fin 3) :
    qeval (tripleData j i k) = boundaryTriple j i k := by
  fin_cases j
  · exact triple_physical_00 i k
  · exact triple_physical_01 i k
  · exact triple_physical_02 i k
  · exact triple_physical_03 i k
  · exact triple_physical_04 i k
  · exact triple_physical_05 i k
  · exact triple_physical_06 i k
  · exact triple_physical_07 i k
  · exact triple_physical_08 i k
  · exact triple_physical_09 i k
  · exact triple_physical_10 i k
  · exact triple_physical_11 i k
  · exact triple_physical_12 i k

def qCos : Fin 8 → Q2 := ![(1,0),(0,1/2),(0,0),(0,-1/2),(-1,0),(0,-1/2),(0,0),(0,1/2)]
def qSin : Fin 8 → Q2 := ![(0,0),(0,1/2),(1,0),(0,1/2),(0,0),(0,-1/2),(-1,0),(0,-1/2)]
def qSign : Fin 8 → Q2 := ![(1,0),(-1,0),(1,0),(-1,0),(1,0),(-1,0),(1,0),(-1,0)]
def qHeight : Q2 := (-1/7,2/7)
def qReferenceDot (i : Fin 8) (x : Fin 3 → Q2) : Q2 :=
  qadd (qadd (qmul (qCos i) (x 0)) (qmul (qSin i) (x 1))) (qmul (qSign i) (x 2))
def qPhysicalDot (x z : Fin 3 → Q2) : Q2 :=
  qadd (qmul (1,1/4) (qadd (qmul (x 0) (z 0)) (qmul (x 1) (z 1))))
    (qmul (1,2) (qmul (x 2) (z 2)))
def qContactRow (e : ContactIndex) (j : Fin 13) : Q2 :=
  qmul (-2,0) (qadd (qReferenceDot (contactNext e) (tripleData j e.1))
    (qReferenceDot e.1 (tripleData j (contactNext e))))
def qContactT (e : ContactIndex) (j l : Fin 13) : Q2 :=
  qadd (qPhysicalDot (tripleData j e.1) (tripleData l e.1))
    (qPhysicalDot (tripleData j (contactNext e)) (tripleData l (contactNext e)))
def qContactM (e : ContactIndex) (j l : Fin 13) : Q2 :=
  qadd (qadd (qmul qHeight (qContactT e j l))
    (qneg (qPhysicalDot (tripleData j e.1) (tripleData l (contactNext e)))))
    (qneg (qPhysicalDot (tripleData j (contactNext e)) (tripleData l e.1)))

theorem qCos_eval (i : Fin 8) : qeval (qCos i) = angularCos i := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  fin_cases i <;> norm_num [qCos,qeval,angularCos] <;> field_simp <;> nlinarith

theorem qSin_eval (i : Fin 8) : qeval (qSin i) = angularSin i := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  fin_cases i <;> norm_num [qSin,qeval,angularSin] <;> field_simp <;> nlinarith

theorem qSign_eval (i : Fin 8) : qeval (qSign i) = layerSign i := by
  fin_cases i <;> norm_num [qSign,qeval,layerSign]

theorem qHeight_eval : qeval qHeight = packingHeight := by
  norm_num [qeval,qHeight,packingHeight]
  ring

theorem qReferenceDot_eval (i k : Fin 8) (j : Fin 13) :
    qeval (qReferenceDot i (tripleData j k)) =
      inner ℝ (packingReference i) (boundaryPhysical j k) := by
  rw [boundary_reference_dot]
  simp only [qReferenceDot,qeval_add,qeval_mul,qCos_eval,qSin_eval,qSign_eval,triple_physical]

theorem qPhysicalDot_eval (i k : Fin 8) (j l : Fin 13) :
    qeval (qPhysicalDot (tripleData j i) (tripleData l k)) =
      inner ℝ (boundaryPhysical j i) (boundaryPhysical l k) := by
  rw [boundary_physical_dot]
  simp only [qPhysicalDot,qeval_add,qeval_mul,triple_physical]
  norm_num [qeval,boundaryZ]
  ring

theorem qContactRow_eval (e : ContactIndex) (j : Fin 13) :
    qeval (qContactRow e j) = boundaryContactRow e j := by
  simp only [qContactRow,qeval_mul,qeval_add,qReferenceDot_eval,boundaryContactRow]
  norm_num [qeval]

theorem qContactT_eval (e : ContactIndex) (j l : Fin 13) :
    qeval (qContactT e j l) = boundaryContactT e j l := by
  simp only [qContactT,qeval_add,qPhysicalDot_eval,boundaryContactT]

theorem qContactM_eval (e : ContactIndex) (j l : Fin 13) :
    qeval (qContactM e j l) = boundaryContactM e j l := by
  simp only [qContactM,qeval_add,qeval_mul,qeval_neg,qHeight_eval,qContactT_eval,
    qPhysicalDot_eval,boundaryContactM]
  ring

def contactRaw (e : ContactIndex) : Poly :=
  [([], (33/1000,0))] ++
    List.ofFn (fun j : Fin 13 => ([j], qmul (61/200,0) (qContactRow e j))) ++
    (List.ofFn (fun j : Fin 13 => List.ofFn (fun l : Fin 13 =>
      (wordSort [j,l], qmul (3721/40000,0)
        (qadd (qContactM e j l) (qmul (33/2000,0) (qContactT e j l))))))).flatten

theorem eval_ofFn {n : ℕ} (f : Fin n → Word × Q2) (y : Fin 13 → ℝ) :
    eval (List.ofFn f) y = ∑ i, qeval (f i).2 * wordEval (f i).1 y := by
  simp [eval, List.map_ofFn, List.sum_ofFn]

theorem eval_flatten (ps : List Poly) (y : Fin 13 → ℝ) :
    eval ps.flatten y = (ps.map (fun p => eval p y)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.flatten_cons, eval_append, ih]

theorem eval_flatten_ofFn {n m : ℕ} (f : Fin n → Fin m → Word × Q2) (y : Fin 13 → ℝ) :
    eval ((List.ofFn fun i => List.ofFn (f i)).flatten) y =
      ∑ i, ∑ j, qeval (f i j).2 * wordEval (f i j).1 y := by
  rw [eval_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact eval_ofFn (f i) y

theorem contactRaw_eval (e : ContactIndex) (y : Fin 13 → ℝ) :
    eval (contactRaw e) y = boundaryContactPolynomial e y := by
  rw [contactRaw,eval_append,eval_append,eval_ofFn,eval_flatten_ofFn]
  simp only [qeval_mul,qeval_add,qContactRow_eval,qContactT_eval,qContactM_eval,wordEval_sort]
  norm_num [eval,wordEval,qeval,boundaryContactPolynomial,gap,boundaryRho]
  simp only [Finset.mul_sum]
  congr 1
  · simp only [mul_assoc]
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

#print axioms qContactRow_eval
#print axioms qContactM_eval
#print axioms contactRaw_eval
end Blueprint.CAP.BoundaryDirect
