import ThomsonNegative.Certificate.Correction.CenterKernel
import ThomsonNegative.Certificate.StoredKernel

namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

structure RowWitness where
  numerator : Nat → Nat
  denominator : Nat
  normalizer : Nat
  inverse : TM
  centers : Nat → Nat
  models : Nat → TM
  columns : Nat → Nat
  radix : Nat
  length : Nat
  width : Nat

end ThomsonNegative.Certificate.Correction
