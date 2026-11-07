import Pilot.BalancedProof

namespace SharedPolynomialProof
open BalancedProof

theorem bounded_encoding_injective (h : Int) (hh : 0 < h)
    (xs ys : List Int)
    (hx : ∀ c ∈ xs, -h ≤ c ∧ c < h)
    (hy : ∀ c ∈ ys, -h ≤ c ∧ c < h)
    (hlen : xs.length = ys.length)
    (heq : encode (2*h) xs = encode (2*h) ys) : xs = ys := by
  calc
    xs = decode (2*h) h xs.length (encode (2*h) xs) := (decode_encode h hh xs hx).symm
    _ = decode (2*h) h ys.length (encode (2*h) ys) := by rw [hlen, heq]
    _ = ys := decode_encode h hh ys hy

def polyDot : List (List Int) → List (List Int) → List Int
  | x::xs,y::ys => add (conv x y) (polyDot xs ys)
  | _,_ => []

def dot : List Int → List Int → Int
  | x::xs,y::ys => x*y+dot xs ys
  | _,_ => 0

theorem encode_polyDot (b : Int) (xs ys : List (List Int)) :
    encode b (polyDot xs ys) =
      dot (xs.map (encode b)) (ys.map (encode b)) := by
  induction xs generalizing ys with
  | nil => simp [polyDot, encode, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [polyDot, encode, dot]
    | cons y ys =>
      simp only [polyDot, List.map_cons, dot]
      rw [encode_add, encode_conv, ih]

theorem polyDot_by_output_encoding (h : Int) (hh : 0 < h)
    (xs ys : List (List Int)) (out : List Int)
    (hb : ∀ c ∈ polyDot xs ys, -h ≤ c ∧ c < h)
    (ho : ∀ c ∈ out, -h ≤ c ∧ c < h)
    (hlen : (polyDot xs ys).length = out.length)
    (heq : dot (xs.map (encode (2*h))) (ys.map (encode (2*h))) = encode (2*h) out) :
    polyDot xs ys = out := by
  apply bounded_encoding_injective h hh (polyDot xs ys) out hb ho hlen
  rw [encode_polyDot, heq]

#print axioms bounded_encoding_injective
#print axioms polyDot_by_output_encoding
end SharedPolynomialProof
