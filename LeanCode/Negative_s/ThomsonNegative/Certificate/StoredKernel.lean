import ThomsonNegative.Compact.Packed.Core2

/-! Small checkpoints cut matrix recomputation at the block boundary. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

structure StoredTM where
  width : Nat
  positive : Nat
  negative : Nat
  error : Nat

def repack (fromWidth toWidth count value : Nat) : Nat :=
  let mask := Nat.sub (Nat.pow 2 fromWidth) 1
  Nat.rec 0 (fun k acc => Nat.add acc (Nat.shiftLeft
    (Nat.land (Nat.shiftRight value (Nat.mul fromWidth k)) mask) (Nat.mul toWidth k))) count

def StoredTM.load (c : Ctx) (s : StoredTM) : TM :=
  ofPQ c (repack s.width c.W c.m s.positive) (repack s.width c.W c.m s.negative) s.error

def sameTM (a b : TM) : Bool :=
  Nat.beq a.v b.v && Nat.beq a.a b.a && Nat.beq a.s b.s && Nat.beq a.e b.e && a.ok && b.ok

def sameModels : List TM → List TM → Bool
  | [], [] => true
  | a :: as, b :: bs => sameTM a b && sameModels as bs
  | _, _ => false

end ThomsonNegative.Certificate
