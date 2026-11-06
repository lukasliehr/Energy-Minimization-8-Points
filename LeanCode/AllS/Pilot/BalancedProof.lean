import Lean.Elab.Tactic.Omega
namespace BalancedProof

def encode (b : Int) : List Int → Int
  | [] => 0
  | c :: cs => c + b * encode b cs

def decode (b h : Int) : Nat → Int → List Int
  | 0, _ => []
  | n+1, w =>
    let c := (w+h)%b-h
    c :: decode b h n ((w-c)/b)

theorem digit (h c v : Int) (hh : 0 < h) (hc : -h ≤ c ∧ c < h) :
    ((c + (2*h)*v + h) % (2*h))-h = c := by
  have e : c + (2*h)*v + h = (c+h) + (2*h)*v := by omega
  rw [e, Int.add_mul_emod_self_left]
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ c+h) (by omega : c+h < 2*h)]
  omega

theorem shift (h c v : Int) (hh : 0 < h) :
    (c + (2*h)*v-c)/(2*h) = v := by
  have e : c + (2*h)*v-c = (2*h)*v := by omega
  rw [e, Int.mul_ediv_cancel_left _ (by omega : 2*h ≠ 0)]

theorem decode_encode (h : Int) (hh : 0 < h) (xs : List Int)
    (hb : ∀ c ∈ xs, -h ≤ c ∧ c < h) :
    decode (2*h) h xs.length (encode (2*h) xs) = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hb c (by simp)
    have ht : ∀ x ∈ cs, -h ≤ x ∧ x < h := by
      intro x hx
      exact hb x (by simp [hx])
    simp only [List.length_cons, encode, decode]
    rw [digit h c (encode (2*h) cs) hh hc]
    rw [shift h c (encode (2*h) cs) hh, ih ht]

def add : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (a : Int) : List Int → List Int
  | [] => []
  | x::xs => (a*x)::scale a xs

def conv : List Int → List Int → List Int
  | [], _ => []
  | x::xs, ys => add (scale x ys) (0::conv xs ys)

theorem encode_add (b : Int) (xs ys : List Int) :
    encode b (add xs ys) = encode b xs + encode b ys := by
  induction xs generalizing ys with
  | nil => simp [add, encode]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add, encode]
    | cons y ys =>
      simp only [add, encode]
      rw [ih, Int.mul_add]
      omega

theorem encode_scale (b a : Int) (xs : List Int) :
    encode b (scale a xs) = a * encode b xs := by
  induction xs with
  | nil => simp [scale, encode]
  | cons x xs ih =>
    simp only [scale, encode, ih, Int.mul_add]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem encode_conv (b : Int) (xs ys : List Int) :
    encode b (conv xs ys) = encode b xs * encode b ys := by
  induction xs with
  | nil => simp [conv, encode]
  | cons x xs ih =>
    rw [conv, encode_add, encode_scale]
    simp only [encode, Int.zero_add, ih, Int.add_mul, Int.mul_assoc]

theorem convolution_by_balanced_decode (h : Int) (hh : 0 < h)
    (xs ys : List Int)
    (hb : ∀ c ∈ conv xs ys, -h ≤ c ∧ c < h) :
    decode (2*h) h (conv xs ys).length
      (encode (2*h) xs * encode (2*h) ys) = conv xs ys := by
  rw [← encode_conv]
  exact decode_encode h hh (conv xs ys) hb

#print axioms decode_encode
#print axioms convolution_by_balanced_decode
end BalancedProof
