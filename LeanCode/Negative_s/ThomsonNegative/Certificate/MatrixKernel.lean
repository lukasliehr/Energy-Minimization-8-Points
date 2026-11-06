import ThomsonNegative.Compact.Packed.Core2

/-! Init-only matrix arithmetic. No arithmetic receipts or rational literals. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

def sumTM (c : Ctx) (f : Nat → TM) (n : Nat) : TM :=
  Nat.rec zeroTM (fun i acc => add c acc (f i)) n

def dotTM (c : Ctx) (f g : Nat → TM) (n : Nat) : TM :=
  refresh c (sumTM c (fun i => mul c (f i) (g i)) n)

abbrev TMMatrix := List (List TM)

def entry (A : TMMatrix) (i j : Nat) : TM := (A.getD i []).getD j zeroTM

def tabulate (rows cols : Nat) (f : Nat → Nat → TM) : TMMatrix :=
  (List.range rows).map (fun i => (List.range cols).map (f i))

def matmulTM (c : Ctx) (rows inner cols : Nat) (A B : TMMatrix) : TMMatrix :=
  tabulate rows cols (fun i j => dotTM c (fun k => entry A i k) (fun k => entry B k j) inner)

def transposeTM (rows cols : Nat) (A : TMMatrix) : TMMatrix :=
  tabulate cols rows (fun i j => entry A j i)

def gramTM (c : Ctx) (raw free : Nat) (B W : TMMatrix) : TMMatrix :=
  let BW := matmulTM c raw free free B W
  matmulTM c raw free raw BW (transposeTM raw free B)

def allOk (A : TMMatrix) : Bool :=
  A.all (fun row => row.all TM.ok)

def rationalScale (c : Ctx) (ng : Bool) (n d : Nat) (A : TM) : TM :=
  smul c ng (ratMag c n d) 1 A

end ThomsonNegative.Certificate
