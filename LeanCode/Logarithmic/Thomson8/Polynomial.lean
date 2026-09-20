import Thomson8.Algebra

namespace Thomson8

structure Exponent where
  u : ℕ
  v : ℕ
  t : ℕ
  deriving DecidableEq, Repr

namespace Exponent
def key (a : Exponent) : ℕ := 169*a.u+13*a.v+a.t
def add (a b : Exponent) : Exponent := ⟨a.u+b.u, a.v+b.v, a.t+b.t⟩
def eval (a : Exponent) (u v t : ℝ) : ℝ := u^a.u * v^a.v * t^a.t
theorem eval_add (a b : Exponent) (u v t : ℝ) :
    (add a b).eval u v t = a.eval u v t * b.eval u v t := by
  simp only [add, eval, pow_add]
  ring
end Exponent

abbrev Poly := List (Exponent × K)

namespace Poly

noncomputable def eval (p : Poly) (u v t : ℝ) : ℝ :=
  (p.map fun m => m.2.eval * m.1.eval u v t).sum

def insert (a : Exponent) (c : K) : Poly → Poly
  | [] => [(a,c)]
  | (b,d)::ps => if a=b then (b,K.add c d)::ps else (b,d)::insert a c ps

/- Merge polynomial lists. The fuel-zero fallback preserves interpretation
even for arbitrary or unsorted input. Successful zero checks remain sound. -/
def merge : ℕ → Poly → Poly → Poly
  | 0, p, q => p++q
  | _+1, [], q => q
  | _+1, p, [] => p
  | fuel+1, (a,c)::ps, (b,d)::qs =>
    if a=b then (a,K.add c d)::merge fuel ps qs
    else if a.key ≤ b.key then (a,c)::merge fuel ps ((b,d)::qs)
    else (b,d)::merge fuel ((a,c)::ps) qs

def add (p q : Poly) : Poly := merge 1000 p q

def normalize : Poly → Poly
  | [] => []
  | m::ms => add [m] (normalize ms)

def scale (c : K) (p : Poly) : Poly :=
  if c=K.zero then [] else p.map fun (a,d) => (a,K.mul c d)

def shift (a : Exponent) (c : K) (p : Poly) : Poly :=
  if c=K.zero then [] else p.map fun (b,d) => (a.add b, K.mul c d)

def mul : Poly → Poly → Poly
  | [], _ => []
  | (a,c)::ps, q => add (shift a c q) (mul ps q)

def pow (p : Poly) : ℕ → Poly
  | 0 => [(⟨0,0,0⟩,K.one)]
  | n+1 => mul (pow p n) p

def sum : List Poly → Poly
  | [] => []
  | p::ps => add p (sum ps)

def const (c : K) : Poly := [(⟨0,0,0⟩,c)]
def monomial (a : Exponent) : Poly := [(a,K.one)]

def permute (i : ℕ) (p : Poly) : Poly := normalize (p.map fun (a,c) =>
  (match i with
   | 0 => a
   | 1 => ⟨a.u,a.t,a.v⟩
   | 2 => ⟨a.v,a.u,a.t⟩
   | 3 => ⟨a.v,a.t,a.u⟩
   | 4 => ⟨a.t,a.u,a.v⟩
   | _ => ⟨a.t,a.v,a.u⟩, c))

def symmetrize (p : Poly) : Poly :=
  scale (K.ofRat (1/6)) (sum ((List.range 6).map fun i => permute i p))

def repeated (axis : ℕ) (p : Poly) : Poly :=
  p.foldr (fun (a,c) rest => add [(
    (if axis=0 then ⟨a.u+a.v,0,0⟩ else if axis=1 then ⟨0,a.u+a.v,0⟩
      else ⟨0,0,a.u+a.v⟩), c)] rest) []

def isZero (p : Poly) : Prop := ∀ m ∈ p, m.2 = K.zero
instance (p : Poly) : Decidable (isZero p) := inferInstanceAs (Decidable (∀ m ∈ p, m.2 = K.zero))

@[simp] theorem eval_nil (u v t : ℝ) : eval [] u v t = 0 := by simp [eval]
@[simp] theorem eval_cons (a : Exponent) (c : K) (p : Poly) (u v t : ℝ) :
    eval ((a,c)::p) u v t = c.eval*a.eval u v t + eval p u v t := by simp [eval]

theorem eval_insert (a : Exponent) (c : K) (p : Poly) (u v t : ℝ) :
    eval (insert a c p) u v t = c.eval*a.eval u v t + eval p u v t := by
  induction p with
  | nil => simp [insert]
  | cons m ps ih =>
    rcases m with ⟨b,d⟩
    by_cases h : a=b
    · subst b
      simp [insert, K.eval_add]
      ring
    · simp only [insert, if_neg h, eval_cons, ih]
      ring

theorem eval_merge (fuel : ℕ) (p q : Poly) (u v t : ℝ) :
    eval (merge fuel p q) u v t = eval p u v t + eval q u v t := by
  induction fuel generalizing p q with
  | zero => simp [merge, eval, List.map_append, List.sum_append]
  | succ fuel ih =>
    cases p with
    | nil => simp [merge]
    | cons m ps =>
      cases q with
      | nil => simp [merge]
      | cons m' qs =>
        rcases m with ⟨a,c⟩
        rcases m' with ⟨b,d⟩
        by_cases he : a=b
        · subst b
          simp [merge, ih, K.eval_add]
          ring
        · by_cases hk : a.key ≤ b.key
          · simp only [merge, if_neg he, if_pos hk, eval_cons, ih]
            ring
          · simp only [merge, if_neg he, if_neg hk, eval_cons, ih]
            ring

@[simp] theorem eval_add (p q : Poly) (u v t : ℝ) :
    eval (add p q) u v t = eval p u v t + eval q u v t := eval_merge _ _ _ _ _ _

@[simp] theorem eval_normalize (p : Poly) (u v t : ℝ) :
    eval (normalize p) u v t = eval p u v t := by
  induction p with
  | nil => simp [normalize]
  | cons m ms ih =>
    rcases m with ⟨a,c⟩
    simp [normalize, ih]

@[simp] theorem eval_scale (c : K) (p : Poly) (u v t : ℝ) :
    eval (scale c p) u v t = c.eval * eval p u v t := by
  by_cases hc : c=K.zero
  · simp [hc, scale]
  simp only [scale, if_neg hc]
  induction p with
  | nil => simp
  | cons m ps ih =>
    rcases m with ⟨a,d⟩
    simp only [List.map_cons, eval_cons, K.eval_mul]
    rw [ih]
    ring

theorem eval_shift (a : Exponent) (c : K) (p : Poly) (u v t : ℝ) :
    eval (shift a c p) u v t = c.eval*a.eval u v t*eval p u v t := by
  by_cases hc : c=K.zero
  · simp [hc, shift]
  simp only [shift, if_neg hc]
  induction p with
  | nil => simp
  | cons m ps ih =>
    rcases m with ⟨b,d⟩
    simp only [List.map_cons, eval_cons, K.eval_mul, Exponent.eval_add]
    rw [ih]
    ring

@[simp] theorem eval_mul (p q : Poly) (u v t : ℝ) :
    eval (mul p q) u v t = eval p u v t * eval q u v t := by
  induction p with
  | nil => simp [mul]
  | cons m ps ih =>
    rcases m with ⟨a,c⟩
    simp only [mul, eval_add, eval_shift, ih, eval_cons]
    ring

@[simp] theorem eval_pow (p : Poly) (n : ℕ) (u v t : ℝ) :
    eval (pow p n) u v t = eval p u v t ^ n := by
  induction n with
  | zero => simp [pow, Exponent.eval]
  | succ n ih => simp [pow, ih, pow_succ]

theorem eval_of_isZero (p : Poly) (h : p.isZero) (u v t : ℝ) : eval p u v t = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hx
  rw [h m hm, K.eval_zero, zero_mul]

@[simp] theorem eval_sum (ps : List Poly) (u v t : ℝ) :
    eval (sum ps) u v t = (ps.map fun p => eval p u v t).sum := by
  induction ps with
  | nil => simp [sum]
  | cons p ps ih => simp [sum, ih]

@[simp] theorem eval_const (c : K) (u v t : ℝ) :
    eval (const c) u v t = c.eval := by simp [const, Exponent.eval]
@[simp] theorem eval_monomial (a : Exponent) (u v t : ℝ) :
    eval (monomial a) u v t = a.eval u v t := by simp [monomial]

theorem eval_eq_of_check (p q : Poly)
    (h : (add p (scale (K.ofRat (-1)) q)).isZero) (u v t : ℝ) :
    eval p u v t = eval q u v t := by
  have hz := eval_of_isZero _ h u v t
  simp only [eval_add, eval_scale, K.eval_ofRat, Rat.cast_neg, Rat.cast_one] at hz
  linarith

end Poly
end Thomson8
