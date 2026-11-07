import ThomsonNegative.Certificate.Correction.RecordKernel

/-! One direct normalized denominator per correction row. Both the numerical
and structural proofs consume the same exact polynomial words. -/
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

def denominatorInverse (c : Ctx) (A : TM) (denominator normalizer : Nat) : TM :=
  invN c 9 1 (recordTM c A denominator normalizer)

def ratioTM (c : Ctx) (A inverse : TM) (numerator normalizer inputScale : Nat) : TM :=
  refresh c (mul c (recordTM c A numerator (Nat.mul normalizer inputScale)) inverse)

end ThomsonNegative.Certificate.Correction
