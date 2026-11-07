import ThomsonNegative.Structure.Packed.PolyKernel

/-! Cold exact affine translations, checked directly on short integer lists.
This module uses Init only and introduces no arithmetic receipts. -/
namespace ThomsonNegative.Certificate.Correction.Inverse

def recordInts (x : Nat) : List Int :=
  let w := Nat.land (Nat.shiftRight x 20) 4095
  let n := Nat.land (Nat.shiftRight x 12) 255
  let p := Nat.shiftRight x 32
  ((List.range n).map (fun k =>
    Int.sub (Int.ofNat (ThomsonNegative.Structure.Exact.fld p (Nat.mul w k) w))
      (Int.ofNat (Nat.pow 2 (Nat.sub w 1))))).reverse

def addI : List Int → List Int → List Int
  | [], ys => ys
  | x::xs, [] => x::xs
  | x::xs, y::ys => Int.add x y :: addI xs ys

def scaleI (c : Int) : List Int → List Int
  | [] => []
  | x::xs => Int.mul c x :: scaleI c xs

/-- Multiply by `c+d*X` and add the constant term in one traversal. -/
def affineStep (c d carry : Int) : List Int → List Int
  | [] => [carry]
  | x::xs => Int.add carry (Int.mul c x) :: affineStep c d (Int.mul d x) xs

def shiftI : List Int → Int → Int → List Int
  | [], _, _ => []
  | b::L, c, d => affineStep c d (b*d^(L.length+1)) (shiftI L c d)

def shiftCheck (degree source shifted : Nat) : Bool :=
  Nat.ble (Nat.land (Nat.shiftRight source 12) 255) degree &&
    (recordInts shifted == scaleI (256^(degree-Nat.land (Nat.shiftRight source 12) 255))
      (shiftI (recordInts source) 83 256))

end ThomsonNegative.Certificate.Correction.Inverse
