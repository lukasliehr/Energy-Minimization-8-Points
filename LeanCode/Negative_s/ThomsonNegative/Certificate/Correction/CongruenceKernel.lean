import ThomsonNegative.Certificate.Correction.BoundsKernel

namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

def metricTM (c : Ctx) (n : Nat) (J : FactorData) : TMMatrix :=
  tabulate n n (fun i j => rationalTM c
    (differenceArg (factorEntry J i j) (Nat.pow 2 J.bits)))

def congruenceTM (c : Ctx) (n : Nat) (J : FactorData) (M : TMMatrix) : TMMatrix :=
  let Z := metricTM c n J
  let ZM := matmulTM c n n n Z M
  matmulTM c n n n ZM (transposeTM n n Z)

def congruenceGate (c : Ctx) (n : Nat) (J : FactorData) (M : TMMatrix) : Bool :=
  let Z := metricTM c n J
  allOk Z && allOk M && allOk (matmulTM c n n n Z M) && allOk (congruenceTM c n J M)

end ThomsonNegative.Certificate.Correction
