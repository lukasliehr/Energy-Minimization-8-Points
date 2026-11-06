import ThomsonNegative.Compact.Target.Kernel
import ThomsonNegative.Compact.Packed.Input

/-! One fixed kernel/data interface for all five scalar cells. -/
namespace ThomsonNegative.Compact.Target.Cells
open ThomsonNegative.Compact.Packed

def context : Ctx := mkCtx 10 384 448 1024

structure Data where
  centerNumerator : Nat
  heightPositive : Nat
  heightNegative : Nat
  inverseSqrtTwo : Nat
  heightCheckpoint : TM
  coefficientCheckpoints : List TM

def parameterInput (d : Data) : TM :=
  affineInput context (ratMag context d.centerNumerator 10) (ratMag context 1 10)
    (if Nat.beq d.centerNumerator 5 then 1 else 2)

def heightInput (d : Data) : TM := ofPQ context d.heightPositive d.heightNegative 0
def result (d : Data) : Result := build context (parameterInput d) (heightInput d) d.inverseSqrtTwo

def sameTM (x y : TM) : Bool :=
  Nat.beq x.v y.v && Nat.beq x.a y.a && Nat.beq x.s y.s && Nat.beq x.e y.e && (x.ok == y.ok)
def sameList : List TM → List TM → Bool
  | [],[] => true
  | x::xs,y::ys => sameTM x y && sameList xs ys
  | _,_ => false

def gate (d : Data) : Bool :=
  Nat.ble 1 d.centerNumerator && Nat.ble d.centerNumerator 9 && (result d).ok &&
    sameTM (result d).height d.heightCheckpoint &&
    sameList (result d).coefficients d.coefficientCheckpoints

theorem centerFive_exact : ratMag context 5 10=Nat.pow 2 383 := by decide +kernel

end ThomsonNegative.Compact.Target.Cells
