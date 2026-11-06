import ThomsonNegative.Certificate.BasisData
import ThomsonNegative.Certificate.BasisLayout
import ThomsonNegative.Certificate.FactorKernel
import ThomsonNegative.Certificate.Bridges.RawData

/-! Uniform Init-only basis and raw coefficient contraction. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open Bridges

def shiftedHeight (c : Ctx) (A : TM) : TM :=
  refresh c (addC c true (ratMag c 83 256) 1 A)

noncomputable def basisModels (c : Ctx) (A : TM) : List TM :=
  let U := shiftedHeight c A
  BasisData.records.map (rationalFunctionTM c 9 1 U)

noncomputable def basisGate (c : Ctx) (A : TM) : Bool :=
  (shiftedHeight c A).ok && (basisModels c A).all TM.ok

noncomputable def basisMatrix (models : List TM) (b : Nat) : TMMatrix :=
  tabulate (BasisLayout.rawOrder b) (BasisLayout.freeOrder b)
    (fun i j => models.getD (BasisLayout.index b i j) zeroTM)

noncomputable def rawTermTM (c : Ctx) (b row i j : Nat) (G : TMMatrix) : TM :=
  let p := RawData.positiveSlot b row i j
  let n := RawData.negativeSlot b row i j
  cond (Nat.beq p n) zeroTM
    (rationalScale c (Nat.blt p n) (Nat.add (Nat.sub p n) (Nat.sub n p))
      (RawData.denominator b) (entry G i j))

noncomputable def rawRowTM (c : Ctx) (b row : Nat) (G : TMMatrix) : TM :=
  refresh c (sumTM c (fun i => sumTM c (fun j => rawTermTM c b row i j G)
    (RawData.size b)) (RawData.size b))

structure BlockImage where
  intermediate : TMMatrix
  rawGram : TMMatrix
  coefficients : List TM
  ok : Bool

noncomputable def blockImage (c : Ctx) (models : List TM) (b : Nat) (G : TMMatrix) : BlockImage :=
  let B := basisMatrix models b
  let m := BasisLayout.rawOrder b
  let n := BasisLayout.freeOrder b
  let BG := matmulTM c m n n B G
  let raw := matmulTM c m n m BG (transposeTM m n B)
  let coeffs := (List.range 68).map (fun r => rawRowTM c b (BasisLayout.fullRow r) raw)
  ⟨BG,raw,coeffs,allOk BG && allOk raw && coeffs.all TM.ok⟩

end ThomsonNegative.Certificate
