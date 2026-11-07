import AllS.Units.N_AI.N_fixed_tables.PolynomialWitnessSupport

noncomputable section
namespace Blueprint.CAP

def qListAdd : List ℚ → List ℚ → List ℚ
  | [],q => q
  | p,[] => p
  | c::p,d::q => (c+d)::qListAdd p q

def qListMul : List ℚ → List ℚ → List ℚ
  | [],_ => []
  | c::p,q => qListAdd (q.map (fun x => c*x)) (0::qListMul p q)

theorem evalRationalList_add (p q : List ℚ) (a : ℝ) :
    evalRationalList (qListAdd p q) a=evalRationalList p a+evalRationalList q a := by
  induction p generalizing q with
  | nil => simp [qListAdd,evalRationalList]
  | cons c p ih =>
    cases q with
    | nil => simp [qListAdd,evalRationalList]
    | cons d q => simp [qListAdd,evalRationalList,ih];ring

theorem evalRationalList_scale (c : ℚ) (p : List ℚ) (a : ℝ) :
    evalRationalList (p.map (fun x => c*x)) a=(c:ℝ)*evalRationalList p a := by
  induction p with
  | nil => simp [evalRationalList]
  | cons d p ih => simp [evalRationalList,ih];ring

theorem evalRationalList_mul (p q : List ℚ) (a : ℝ) :
    evalRationalList (qListMul p q) a=evalRationalList p a*evalRationalList q a := by
  induction p with
  | nil => simp [qListMul,evalRationalList]
  | cons c p ih =>
    simp [qListMul,evalRationalList_add,evalRationalList_scale,evalRationalList,ih]
    ring

theorem evalRationalList_mul3_checked (q d e v : List ℚ)
    (h : q=qListMul (qListMul d e) v) (a : ℝ) :
    evalRationalList q a=evalRationalList d a*evalRationalList e a*evalRationalList v a := by
  rw [h,evalRationalList_mul,evalRationalList_mul]

theorem evalClearedIntegerIdentity_checked (A : List ℤ) (p v : List ℚ) (lam scale : ℤ)
    (h : (A.map (fun x : ℤ => (lam:ℚ)*(x:ℚ)))=
      (qListMul p v).map (fun x => (scale:ℚ)*x))
    (a : ℝ) : (lam:ℝ)*evalIntegerList A a=
      (scale:ℝ)*evalRationalList p a*evalRationalList v a := by
  have he := congrArg (fun q => evalRationalList q a) h
  have hl : A.map (fun x : ℤ => (lam:ℚ)*(x:ℚ))=
      (A.map (fun x : ℤ => (x:ℚ))).map (fun x => (lam:ℚ)*x) := by
    rw [List.map_map]
    rfl
  rw [hl,evalRationalList_scale,evalRationalList_scale,evalRationalList_mul] at he
  simpa only [← evalIntegerList_rat,Rat.cast_intCast,mul_assoc] using he

#print axioms evalClearedIntegerIdentity_checked
end Blueprint.CAP
