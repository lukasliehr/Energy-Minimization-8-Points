import Thomson8.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option cbv.warning false

namespace Thomson8

def hermiteDerivativeComponent (x : K) (order ell : ℕ) : K :=
  K.sum ((List.range 13).map fun j =>
    if order ≤ j then
      K.scale ((Nat.factorial j : ℚ) / (Nat.factorial (j-order) : ℚ))
        (K.mul ((Data.hermite.getD j []).getD ell K.zero) (K.pow x (j-order)))
    else K.zero)

def contactValue (node ell : ℕ) : K := K.ofRat (
  if node=0 then (if ell=2 then -1/2 else 0)
  else if node=1 then (if ell=1 ∨ ell=2 then -1/2 else 0)
  else if node=2 then (if ell=3 then -1/2 else 0)
  else (if ell=4 then -1/2 else 0))

abbrev checkContact (i : ℕ) : Prop := ∀ ell ∈ List.range 5,
  hermiteDerivativeComponent (nodes.getD i K.zero) 0 ell = contactValue i ell ∧
  K.mul (K.scale 2 (K.add K.one (K.neg (nodes.getD i K.zero))))
    (hermiteDerivativeComponent (nodes.getD i K.zero) 1 ell) =
      K.ofRat (if ell=0 then 1 else 0)

theorem contact_A : checkContact 0 := by decide +kernel
theorem contact_B : checkContact 1 := by decide +kernel
theorem contact_C : checkContact 2 := by decide +kernel
theorem contact_D : checkContact 3 := by decide +kernel

abbrev checkMinusOne (order : ℕ) : Prop := ∀ ell ∈ List.range 5,
  hermiteDerivativeComponent (K.ofRat (-1)) order ell =
    K.ofRat (if order=0 then (if ell=1 then -1 else 0)
      else if ell=0 then (Nat.factorial (order-1) : ℚ)/(2*2^order) else 0)

theorem contact_minus_one_0 : checkMinusOne 0 := by decide +kernel
theorem contact_minus_one_1 : checkMinusOne 1 := by decide +kernel
theorem contact_minus_one_2 : checkMinusOne 2 := by decide +kernel
theorem contact_minus_one_3 : checkMinusOne 3 := by decide +kernel
theorem contact_minus_one_4 : checkMinusOne 4 := by decide +kernel

#print axioms contact_A
#print axioms contact_C
#print axioms contact_minus_one_4

end Thomson8
