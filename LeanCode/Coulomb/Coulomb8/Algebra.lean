import Coulomb8.Parameter

namespace Coulomb8

abbrev K := List ℚ

namespace K

def zero : K := []
def pack (c : ℚ) (p : K) : K := if c=0 ∧ p=[] then [] else c::p
def ofRat (q : ℚ) : K := pack q []
def one : K := ofRat 1
def parameter : K := [0,1]

def add : K → K → K
  | [],q => q
  | p,[] => p
  | c::p,d::q => (c+d)::add p q

def neg (p : K) : K := p.map (-·)
def scale (q : ℚ) (p : K) : K := if q=0 then [] else p.map (q*·)

def mul : K → K → K
  | [],_ => []
  | _,[] => []
  | c::p,d::q => add (scale c (d::q)) (0::mul p (d::q))

def pow (p : K) : ℕ → K
  | 0 => one
  | n+1 => mul (pow p n) p

def sum : List K → K
  | [] => zero
  | p::ps => add p (sum ps)

noncomputable def evalAt (s : ℝ) : K → ℝ
  | [] => 0
  | c::p => (c : ℝ)+s*evalAt s p

noncomputable def eval (p : K) : ℝ := evalAt a p

@[simp] theorem evalAt_pack (s : ℝ) (c : ℚ) (p : K) :
    evalAt s (pack c p) = (c : ℝ)+s*evalAt s p := by
  by_cases h : c=0 ∧ p=[]
  · rcases h with ⟨rfl,rfl⟩
    simp [pack,evalAt]
  · simp [pack,h,evalAt]

@[simp] theorem evalAt_ofRat (s : ℝ) (q : ℚ) : evalAt s (ofRat q)=(q : ℝ) := by
  simp [ofRat,evalAt]

@[simp] theorem evalAt_add (s : ℝ) (p q : K) :
    evalAt s (add p q)=evalAt s p+evalAt s q := by
  induction p generalizing q with
  | nil => simp [add,evalAt]
  | cons c p ih =>
    cases q with
    | nil => simp [add,evalAt]
    | cons d q =>
      simp only [add,evalAt,Rat.cast_add,ih]
      ring

@[simp] theorem evalAt_neg (s : ℝ) (p : K) : evalAt s (neg p) = -evalAt s p := by
  induction p with
  | nil => simp [neg,evalAt]
  | cons c p ih =>
    simp only [neg,List.map_cons,evalAt,Rat.cast_neg] at *
    rw [ih]
    ring

@[simp] theorem evalAt_scale (s : ℝ) (q : ℚ) (p : K) :
    evalAt s (scale q p)=(q : ℝ)*evalAt s p := by
  by_cases hq : q=0
  · simp [scale,hq,evalAt]
  simp only [scale,if_neg hq]
  induction p with
  | nil => simp [evalAt]
  | cons c p ih =>
    simp only [List.map_cons,evalAt,Rat.cast_mul,ih]
    ring

@[simp] theorem evalAt_mul (s : ℝ) (p q : K) :
    evalAt s (mul p q)=evalAt s p*evalAt s q := by
  induction p with
  | nil => simp [mul,evalAt]
  | cons c p ih =>
    cases q with
    | nil => simp [mul,evalAt]
    | cons d q =>
      simp only [mul,evalAt_add,evalAt_scale,Rat.cast_zero,zero_add,evalAt,ih]
      ring

def isZero (p : K) : Prop := ∀ q ∈ p, q=0
instance (p : K) : Decidable (isZero p) := inferInstanceAs (Decidable (∀ q ∈ p, q=0))

theorem evalAt_of_isZero (s : ℝ) (p : K) (h : p.isZero) : evalAt s p=0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    have hc : c=0 := h c (List.mem_cons_self ..)
    have hp : K.isZero p := fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp [evalAt,hc,ih hp]

theorem eval_of_isZero (p : K) (h : p.isZero) : eval p=0 := evalAt_of_isZero a p h

@[simp] theorem eval_ofRat (q : ℚ) : eval (ofRat q)=(q : ℝ) := evalAt_ofRat _ _
@[simp] theorem eval_zero : eval zero=0 := rfl
@[simp] theorem eval_one : eval one=1 := by simp [one]
@[simp] theorem eval_parameter : eval parameter=a := by simp [eval,parameter,evalAt]
@[simp] theorem eval_add (p q : K) : eval (add p q)=eval p+eval q := evalAt_add _ _ _
@[simp] theorem eval_neg (p : K) : eval (neg p) = -eval p := evalAt_neg _ _
@[simp] theorem eval_scale (q : ℚ) (p : K) : eval (scale q p)=(q : ℝ)*eval p :=
  evalAt_scale _ _ _
@[simp] theorem eval_mul (p q : K) : eval (mul p q)=eval p*eval q := evalAt_mul _ _ _
@[simp] theorem eval_pow (p : K) (n : ℕ) : eval (pow p n)=eval p^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,pow_succ]
@[simp] theorem eval_sum (ps : List K) : eval (sum ps)=(ps.map eval).sum := by
  induction ps with
  | nil => simp [sum]
  | cons p ps ih => simp [sum,ih]

end K
end Coulomb8

#print axioms Coulomb8.K.eval_mul
