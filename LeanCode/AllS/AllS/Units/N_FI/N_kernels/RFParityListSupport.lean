import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_AI.N_fixed_tables.ListWitnessSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFParityList
open Blueprint.CAP

abbrev Pair := List ℚ × List ℚ
def add (p q : Pair) : Pair := (qListAdd p.1 q.1,qListAdd p.2 q.2)
def neg (p : Pair) : Pair := (p.1.map (-1*·),p.2.map (-1*·))
def mul (p q : Pair) : Pair :=
  (qListAdd (qListMul p.1 q.1) ((qListMul p.2 q.2).map (2*·)),
   qListAdd (qListMul p.1 q.2) (qListMul p.2 q.1))
def pow (p : Pair) : ℕ → Pair
  | 0 => ([1],[])
  | n+1 => mul (pow p n) p
def sum : List Pair → Pair
  | [] => ([],[])
  | p::ps => add p (sum ps)
def eval (a : ℝ) (p : Pair) : ℝ :=
  evalRationalList p.1 a + Real.sqrt 2 * evalRationalList p.2 a
def Zero (p : Pair) : Prop :=
  p.1.all (fun c => c == 0) = true ∧ p.2.all (fun c => c == 0) = true

@[simp] theorem eval_rat (a : ℝ) (p : List ℚ) : eval a (p,[]) = evalRationalList p a := by
  simp [eval,evalRationalList]

@[simp] theorem eval_add (a : ℝ) (p q : Pair) :
    eval a (add p q) = eval a p + eval a q := by
  simp only [eval,add,evalRationalList_add]
  ring
@[simp] theorem eval_neg (a : ℝ) (p : Pair) : eval a (neg p) = -eval a p := by
  simp only [eval,neg,evalRationalList_scale,Rat.cast_neg,Rat.cast_one]
  ring
@[simp] theorem eval_mul (a : ℝ) (p q : Pair) :
    eval a (mul p q) = eval a p * eval a q := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  simp only [eval,mul,evalRationalList_add,evalRationalList_scale,evalRationalList_mul,
    Rat.cast_ofNat]
  linear_combination -(evalRationalList p.2 a * evalRationalList q.2 a) * hs
@[simp] theorem eval_pow (a : ℝ) (p : Pair) (n : ℕ) :
    eval a (pow p n) = eval a p ^ n := by
  induction n with
  | zero => simp [pow,eval,evalRationalList]
  | succ n ih => simp [pow,pow_succ,ih]
@[simp] theorem eval_sum (a : ℝ) (ps : List Pair) :
    eval a (sum ps) = (ps.map (eval a)).sum := by
  induction ps with
  | nil => simp [sum,eval,evalRationalList]
  | cons p ps ih => simp [sum,ih]
theorem eval_list_zero (a : ℝ) (p : List ℚ)
    (h : p.all (fun c => c == 0)=true) : evalRationalList p a=0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    simp [evalRationalList,h.1,ih h.2]
theorem eval_zero (a : ℝ) (p : Pair) (h : Zero p) : eval a p=0 := by
  simp [eval,eval_list_zero a p.1 h.1,eval_list_zero a p.2 h.2]
theorem eval_eq_of_zero (a : ℝ) (p q : Pair) (h : Zero (add p (neg q))) :
    eval a p=eval a q := by
  have he:=eval_zero a _ h
  simpa only [eval_add,eval_neg,← sub_eq_add_neg,sub_eq_zero] using he

def contact : Fin 4 → Pair :=
  ![([0,1],[]),([-1,2],[]),([0,-1],[1/2,-1/2]),([0,-1],[-1/2,1/2])]
theorem eval_contact (a : ℝ) (i : Fin 4) : eval a (contact i)=contacts a i := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have hi : (Real.sqrt 2)⁻¹=Real.sqrt 2/2 := by
    field_simp
    nlinarith
  fin_cases i <;> norm_num [contact,eval,evalRationalList,contacts,div_eq_mul_inv,hi] <;> ring

def u (odd : Bool) (i : Fin 4) : Pair := contact (parityFiberLabel odd i)
def z (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) : Pair :=
  add (contact (parityFiberPair odd i j).1) (contact (parityFiberPair odd i j).2)
def w (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) : Pair :=
  mul (contact (parityFiberPair odd i j).1) (contact (parityFiberPair odd i j).2)
def basis (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) (t : Tag) : Pair :=
  mul (pow (u odd i) t.1) (pow (z odd i j) t.2.1)
def source (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) (t : Tag) : Pair :=
  mul (basis odd i j t) (pow (w odd i j) t.2.2)

@[simp] theorem eval_u (a : ℝ) (odd : Bool) (i : Fin 4) :
    eval a (u odd i)=parityFiberU a odd i := eval_contact a _
@[simp] theorem eval_z (a : ℝ) (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) :
    eval a (z odd i j)=parityFiberZ a odd i j := by
  simp only [z,eval_add,eval_contact,parityFiberZ]
@[simp] theorem eval_basis (a : ℝ) (odd : Bool) (i : Fin 4)
    (j : Fin (parityFiberSize odd i)) (t : Tag) :
    eval a (basis odd i j t)=parityFiberU a odd i^t.1*parityFiberZ a odd i j^t.2.1 := by
  simp only [basis,eval_mul,eval_pow,eval_u,eval_z]
@[simp] theorem eval_source (a : ℝ) (odd : Bool) (i : Fin 4)
    (j : Fin (parityFiberSize odd i)) (t : Tag) :
    eval a (source odd i j t)=paritySourceData a odd t i j := by
  simp [source,eval_basis,w,eval_mul,eval_pow,eval_contact,paritySourceData,
    parityMonomial,parityZ,parityW,contactTripleEval,parityIndexLabel,
    parityFiberU,parityFiberZ]

def lhs (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i))
    (terms : List (Tag × List ℚ)) : Pair :=
  sum (terms.map (fun t => mul (t.2,[]) (basis odd i j t.1)))
def Gate (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i))
    (terms : List (Tag × List ℚ)) (d : List ℚ) (t : Tag) : Prop :=
  Zero (add (lhs odd i j terms) (neg (mul (d,[]) (source odd i j t))))

theorem checked_identity (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i))
    (terms : List (Tag × List ℚ)) (d : List ℚ) (t : Tag)
    (h : Gate odd i j terms d t) (a : ℝ) :
    (terms.map (fun t => evalRationalList t.2 a * parityFiberU a odd i^t.1.1 *
      parityFiberZ a odd i j^t.1.2.1)).sum =
      evalRationalList d a * paritySourceData a odd t i j := by
  have he:=eval_eq_of_zero a _ _ h
  simpa only [lhs,eval_sum,List.map_map,Function.comp_def,eval_mul,eval_basis,
    eval_source,eval_rat,mul_assoc] using he

#print axioms checked_identity
end Blueprint.Thomson.Finite.RFParityList
