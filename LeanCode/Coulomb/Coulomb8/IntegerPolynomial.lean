import Coulomb8.Algebra

namespace Coulomb8
abbrev IP := List ℤ

namespace IP
open scoped BigOperators

def add : IP → IP → IP
  | [],q => q
  | p,[] => p
  | c::p,d::q => (c+d)::add p q

def scale (c : ℤ) (p : IP) : IP := if c=0 then [] else p.map (c*·)

def mul : IP → IP → IP
  | [],_ => []
  | _,[] => []
  | c::p,d::q => add (scale c (d::q)) (0::mul p (d::q))

def dot : List IP → List IP → IP
  | p::ps,q::qs => add (mul p q) (dot ps qs)
  | _,_ => []

noncomputable def evalAt (s : ℝ) : IP → ℝ
  | [] => 0
  | c::p => (c : ℝ)+s*evalAt s p
noncomputable def eval (p : IP) : ℝ := evalAt a p

@[simp] theorem eval_cons (c : ℤ) (p : IP) : eval (c::p)=(c : ℝ)+a*eval p := rfl

def toK (p : IP) : K := p.map (fun z => (z : ℚ))

theorem evalAt_toK (s : ℝ) (p : IP) : K.evalAt s p.toK=evalAt s p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    change ((c : ℚ) : ℝ)+s*K.evalAt s (toK p)=(c : ℝ)+s*evalAt s p
    rw [ih]
    norm_cast

@[simp] theorem eval_toK (p : IP) : K.eval p.toK=eval p := evalAt_toK a p

@[simp] theorem eval_add (p q : IP) : eval (add p q)=eval p+eval q := by
  induction p generalizing q with
  | nil => simp [add,eval,evalAt]
  | cons c p ih =>
    cases q with
    | nil => simp [add,eval,evalAt]
    | cons d q =>
      change ((c+d : ℤ) : ℝ)+a*eval (add p q)=((c : ℝ)+a*eval p)+((d : ℝ)+a*eval q)
      rw [ih,Int.cast_add]
      ring

@[simp] theorem eval_scale (c : ℤ) (p : IP) : eval (scale c p)=(c : ℝ)*eval p := by
  by_cases hc : c=0
  · simp [scale,hc,eval,evalAt]
  simp only [scale,if_neg hc]
  induction p with
  | nil => simp [eval,evalAt]
  | cons d p ih =>
    change ((c*d : ℤ) : ℝ)+a*eval (p.map (c*·))=(c : ℝ)*((d : ℝ)+a*eval p)
    rw [ih,Int.cast_mul]
    ring

@[simp] theorem eval_mul (p q : IP) : eval (mul p q)=eval p*eval q := by
  induction p with
  | nil => simp [mul,eval,evalAt]
  | cons c p ih =>
    cases q with
    | nil => simp [mul,eval,evalAt]
    | cons d q =>
      rw [mul,eval_add,eval_scale]
      rw [eval_cons 0 (mul p (d::q)),ih,eval_cons c p]
      push_cast
      ring

def isZero (p : IP) : Prop := ∀ z ∈ p, z=0
instance (p : IP) : Decidable p.isZero := inferInstanceAs (Decidable (∀ z ∈ p, z=0))

theorem eval_of_isZero (p : IP) (h : p.isZero) : eval p=0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    have hc : c=0 := h c (List.mem_cons_self ..)
    have hp : IP.isZero p := fun q hq => h q (List.mem_cons_of_mem _ hq)
    change (c : ℝ)+a*eval p=0
    rw [hc,ih hp]
    simp

theorem eval_dot_ofFn {n : ℕ} (p q : Fin n → IP) :
    eval (dot (List.ofFn p) (List.ofFn q))=∑ i, eval (p i)*eval (q i) := by
  induction n with
  | zero => simp [dot,eval,evalAt]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,dot,eval_add,eval_mul,ih,Fin.sum_univ_succ]

theorem annihilator_of_check {n : ℕ} (p q : Fin n → IP)
    (h : (dot (List.ofFn p) (List.ofFn q)).isZero) :
    ∑ i, eval (p i)*eval (q i)=0 := by
  rw [←eval_dot_ofFn]
  exact eval_of_isZero _ h

theorem eval_scaled_ofFn {n : ℕ} (p : Fin n → K) (q : Fin n → IP) (c : ℚ)
    (h : List.ofFn p=List.ofFn (fun i => K.scale c (q i).toK)) (i : Fin n) :
    K.eval (p i)=(c : ℝ)*eval (q i) := by
  have he := congrFun (List.ofFn_injective h) i
  rw [he,K.eval_scale,eval_toK]

end IP
end Coulomb8

#print axioms Coulomb8.IP.annihilator_of_check
