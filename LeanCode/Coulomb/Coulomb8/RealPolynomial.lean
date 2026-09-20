import Coulomb8.Interval
import Mathlib.Algebra.Polynomial.Derivative

namespace Coulomb8

abbrev RealPoly := List ℝ

namespace RealPoly

def add : RealPoly → RealPoly → RealPoly
  | [],q => q
  | p,[] => p
  | c::p,d::q => (c+d)::add p q

def scale (c : ℝ) (p : RealPoly) : RealPoly := p.map (c*·)
def mul : RealPoly → RealPoly → RealPoly
  | [],_ => []
  | c::p,q => add (scale c q) (0::mul p q)
def pow (p : RealPoly) : ℕ → RealPoly
  | 0 => [1]
  | n+1 => mul (pow p n) p

def derivFrom (k : ℕ) : RealPoly → RealPoly
  | [] => []
  | c::p => ((k : ℝ)*c)::derivFrom (k+1) p
def derivative (p : RealPoly) : RealPoly := derivFrom 1 p.tail

noncomputable def toPolynomial : RealPoly → Polynomial ℝ
  | [] => 0
  | c::p => Polynomial.C c+Polynomial.X*toPolynomial p

noncomputable def eval (p : RealPoly) (x : ℝ) : ℝ := p.toPolynomial.eval x

@[simp] theorem toPolynomial_add (p q : RealPoly) :
    (add p q).toPolynomial=p.toPolynomial+q.toPolynomial := by
  induction p generalizing q with
  | nil => simp [add,toPolynomial]
  | cons c p ih =>
    cases q with
    | nil => simp [add,toPolynomial]
    | cons d q => simp only [add,toPolynomial,map_add,ih]; ring

@[simp] theorem toPolynomial_scale (c : ℝ) (p : RealPoly) :
    (scale c p).toPolynomial=Polynomial.C c*p.toPolynomial := by
  induction p with
  | nil => simp [scale,toPolynomial]
  | cons d p ih =>
    simp only [scale,List.map_cons,toPolynomial,map_mul] at *
    rw [ih]
    ring

@[simp] theorem toPolynomial_mul (p q : RealPoly) :
    (mul p q).toPolynomial=p.toPolynomial*q.toPolynomial := by
  induction p with
  | nil => simp [mul,toPolynomial]
  | cons c p ih =>
    simp only [mul,toPolynomial_add,toPolynomial_scale,toPolynomial,map_zero,zero_add,ih]
    ring

@[simp] theorem toPolynomial_pow (p : RealPoly) (n : ℕ) :
    (pow p n).toPolynomial=p.toPolynomial^n := by
  induction n with
  | zero => simp [pow,toPolynomial]
  | succ n ih => simp [pow,toPolynomial_mul,ih,pow_succ]

@[simp] theorem coeff_toPolynomial (p : RealPoly) (n : ℕ) :
    p.toPolynomial.coeff n=p.getD n 0 := by
  induction p generalizing n with
  | nil => simp [toPolynomial]
  | cons c p ih =>
    cases n with
    | zero => simp [toPolynomial]
    | succ n => simp [toPolynomial,Polynomial.coeff_X_mul,ih]

theorem getD_derivFrom (p : RealPoly) (k n : ℕ) :
    (derivFrom k p).getD n 0=(k+n : ℕ)*p.getD n 0 := by
  induction p generalizing k n with
  | nil => simp [derivFrom]
  | cons c p ih =>
    cases n with
    | zero => simp [derivFrom]
    | succ n => simpa [derivFrom,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) n

@[simp] theorem toPolynomial_derivative (p : RealPoly) :
    p.derivative.toPolynomial=p.toPolynomial.derivative := by
  ext n
  rw [coeff_toPolynomial,Polynomial.coeff_derivative,coeff_toPolynomial]
  cases p with
  | nil => simp [derivative,derivFrom]
  | cons c p =>
    change (derivFrom 1 p).getD n 0=(c::p).getD (n+1) 0*(n+1)
    rw [getD_derivFrom]
    simp [add_comm,mul_comm]

theorem coeff_eq_zero_of_length_le (p : RealPoly) {n : ℕ} (hn : p.length ≤ n) :
    p.toPolynomial.coeff n=0 := by
  rw [coeff_toPolynomial]
  simp [List.getD,List.getElem?_eq_none hn]

@[simp] theorem eval_nil (x : ℝ) : eval [] x=0 := by simp [eval,toPolynomial]
@[simp] theorem eval_cons (c : ℝ) (p : RealPoly) (x : ℝ) :
    eval (c::p) x=c+x*eval p x := by simp [eval,toPolynomial]

end RealPoly

namespace PolyBox

open Thomson8

def Contains (bs : List Box) (p : RealPoly) : Prop := List.Forall₂ Box.Contains bs p

def add : List Box → List Box → List Box
  | [],q => q
  | p,[] => p
  | c::p,d::q => Box.add c d::add p q

def scale (c : Box) (p : List Box) : List Box := p.map (Box.times c)
def mul : List Box → List Box → List Box
  | [],_ => []
  | c::p,q => add (scale c q) (Box.exact 0::mul p q)

def eval (p : List Box) (x : Box) : Box :=
  match p with
  | [] => Box.exact 0
  | c::p => Box.add c (Box.times x (eval p x))

theorem contains_add {bs cs : List Box} {p q : RealPoly}
    (hp : Contains bs p) (hq : Contains cs q) : Contains (add bs cs) (RealPoly.add p q) := by
  induction hp generalizing cs q with
  | nil => simpa [add,RealPoly.add] using hq
  | @cons b c bs p hbc hp ih =>
    cases hq with
    | nil => exact List.Forall₂.cons hbc hp
    | cons hcd hq => exact List.Forall₂.cons (Box.contains_add hbc hcd) (ih hq)

theorem contains_scale {b : Box} {c : ℝ} {bs : List Box} {p : RealPoly}
    (hc : b.Contains c) (hp : Contains bs p) : Contains (scale b bs) (RealPoly.scale c p) := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | cons h hp ih => exact List.Forall₂.cons (Box.contains_times hc h) ih

theorem contains_mul {bs cs : List Box} {p q : RealPoly}
    (hp : Contains bs p) (hq : Contains cs q) : Contains (mul bs cs) (RealPoly.mul p q) := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | cons h hp ih =>
    exact contains_add (contains_scale h hq)
      (List.Forall₂.cons (by simpa using Box.exact_contains 0) ih)

theorem contains_eval {bs : List Box} {p : RealPoly} {b : Box} {x : ℝ}
    (hp : Contains bs p) (hx : b.Contains x) : (eval bs b).Contains (p.eval x) := by
  induction hp with
  | nil => simpa [eval] using Box.exact_contains 0
  | cons hc hp ih =>
    simpa only [eval,RealPoly.eval_cons] using Box.contains_add hc (Box.contains_times hx ih)

end PolyBox
end Coulomb8

#print axioms Coulomb8.RealPoly.toPolynomial_mul
#print axioms Coulomb8.PolyBox.contains_mul
