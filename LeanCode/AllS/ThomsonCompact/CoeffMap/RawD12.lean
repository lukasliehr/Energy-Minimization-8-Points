import AllS.Units.N_AI.N_residual_replay.RawSparseLookupSupport
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F0
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F1
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F2
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F3
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F4
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D12_F5
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_m0Plus
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_m0Sign
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_m0Standard
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_m1Even
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_m1Odd
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_mdetPlus
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_mdetSign
import AllS.Units.N_FI.N_raw_projection.RawScalarTensors.D12_mdetStandard
import AllS.Units.N_FI.N_gram_map.N_family_and_map

/-!
# The D12 raw tensors and block indexing (no `Interface` import)

Raw scalar/moment tensors of the D12 layout with their substitution lemmas, the computable rational
coefficients `blockCoef`, raw dimensions and the block order `blockEquiv : Fin 14 ≃ GramBlock 6`. Imported by
`W0Link` and by the one-time table checks `ECheck.*` (which therefore do not depend on `Interface`).
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.CoeffMap.D12

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-! ## Raw tensors of the D12 layout -/

/-- Raw scalar basis sizes. -/
def rawSize : ScalarBlockName → ℕ
  | .m0Plus => 23
  | .m0Sign => 7
  | .m0Standard => 27
  | .m1Even => 34
  | .m1Odd => 22
  | .mdetPlus => 11
  | .mdetSign => 2
  | .mdetStandard => 11

def rawTags : (b : ScalarBlockName) → Fin (rawSize b) → StandardTag
  | .m0Plus => RawScalarTensors.D12_m0Plus.tags
  | .m0Sign => RawScalarTensors.D12_m0Sign.tags
  | .m0Standard => RawScalarTensors.D12_m0Standard.tags
  | .m1Even => RawScalarTensors.D12_m1Even.tags
  | .m1Odd => RawScalarTensors.D12_m1Odd.tags
  | .mdetPlus => RawScalarTensors.D12_mdetPlus.tags
  | .mdetSign => RawScalarTensors.D12_mdetSign.tags
  | .mdetStandard => RawScalarTensors.D12_mdetStandard.tags

def rawSource : (b : ScalarBlockName) → Matrix (Fin (rawSize b)) (Fin (rawSize b)) (List (Tag × ℤ))
  | .m0Plus => RawScalarTensors.D12_m0Plus.source
  | .m0Sign => RawScalarTensors.D12_m0Sign.source
  | .m0Standard => RawScalarTensors.D12_m0Standard.source
  | .m1Even => RawScalarTensors.D12_m1Even.source
  | .m1Odd => RawScalarTensors.D12_m1Odd.source
  | .mdetPlus => RawScalarTensors.D12_mdetPlus.source
  | .mdetSign => RawScalarTensors.D12_mdetSign.source
  | .mdetStandard => RawScalarTensors.D12_mdetStandard.source

def rawDen : ScalarBlockName → ℕ
  | .m0Plus => RawScalarTensors.D12_m0Plus.denominator
  | .m0Sign => RawScalarTensors.D12_m0Sign.denominator
  | .m0Standard => RawScalarTensors.D12_m0Standard.denominator
  | .m1Even => RawScalarTensors.D12_m1Even.denominator
  | .m1Odd => RawScalarTensors.D12_m1Odd.denominator
  | .mdetPlus => RawScalarTensors.D12_mdetPlus.denominator
  | .mdetSign => RawScalarTensors.D12_mdetSign.denominator
  | .mdetStandard => RawScalarTensors.D12_mdetStandard.denominator

def rawQ (b : ScalarBlockName) (u v : Fin (rawSize b)) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial
    (normalizeIntegerRawEntry (rawDen b) (rawSource b u v)))

theorem rawQ_subst (b : ScalarBlockName) (u v : Fin (rawSize b)) :
    invariantSubst (rawQ b u v) = rawScalarBilinear b (rawTags b u) (rawTags b v) := by
  cases b
  · exact RawScalarTensors.D12_m0Plus.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_m0Sign.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_m0Standard.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_m1Even.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_m1Odd.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_mdetPlus.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_mdetSign.subst_coordinatePolynomial u v
  · exact RawScalarTensors.D12_mdetStandard.subst_coordinatePolynomial u v

def momSource : (k : Fin 6) → Matrix (Fin (6 - k.val + 1)) (Fin (6 - k.val + 1)) (List (Tag × ℤ))
  | ⟨0, _⟩ => RawMomentTensors.D12_F0.source
  | ⟨1, _⟩ => RawMomentTensors.D12_F1.source
  | ⟨2, _⟩ => RawMomentTensors.D12_F2.source
  | ⟨3, _⟩ => RawMomentTensors.D12_F3.source
  | ⟨4, _⟩ => RawMomentTensors.D12_F4.source
  | ⟨5, _⟩ => RawMomentTensors.D12_F5.source
  | ⟨_ + 6, h⟩ => absurd h (by omega)

def momDen : Fin 6 → ℕ
  | ⟨0, _⟩ => RawMomentTensors.D12_F0.denominator
  | ⟨1, _⟩ => RawMomentTensors.D12_F1.denominator
  | ⟨2, _⟩ => RawMomentTensors.D12_F2.denominator
  | ⟨3, _⟩ => RawMomentTensors.D12_F3.denominator
  | ⟨4, _⟩ => RawMomentTensors.D12_F4.denominator
  | ⟨5, _⟩ => RawMomentTensors.D12_F5.denominator
  | ⟨_ + 6, _⟩ => 1

def momQ (k : Fin 6) (u v : Fin (6 - k.val + 1)) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial
    (normalizeIntegerRawEntry (momDen k) (momSource k u v)))

theorem momQ_subst (k : Fin 6) (u v : Fin (6 - k.val + 1)) :
    invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val := by
  revert u v
  fin_cases k <;> intro u v
  · exact RawMomentTensors.D12_F0.subst_coordinatePolynomial u v
  · exact RawMomentTensors.D12_F1.subst_coordinatePolynomial u v
  · exact RawMomentTensors.D12_F2.subst_coordinatePolynomial u v
  · exact RawMomentTensors.D12_F3.subst_coordinatePolynomial u v
  · exact RawMomentTensors.D12_F4.subst_coordinatePolynomial u v
  · exact RawMomentTensors.D12_F5.subst_coordinatePolynomial u v

/-- Raw dimension of a Gram block (rows of its column matrix). -/
def rawDim : GramBlock 6 → ℕ
  | .inl k => 6 - k.val + 1
  | .inr b => rawSize b

/-- Rational raw-tensor coefficient at tag `t` (computable). -/
def blockCoef : (b : GramBlock 6) → Tag → Matrix (Fin (rawDim b)) (Fin (rawDim b)) ℚ
  | .inl k => fun t u v => (rawIntegerLookup (momSource k u v) t : ℚ) / (momDen k : ℚ)
  | .inr b => fun t u v => (rawIntegerLookup (rawSource b u v) t : ℚ) / (rawDen b : ℚ)

/-- Scalar blocks in declaration order. -/
def scalarOfFin : Fin 8 → ScalarBlockName :=
  ![.m0Plus, .m0Sign, .m0Standard, .m1Even, .m1Odd, .mdetPlus, .mdetSign, .mdetStandard]

def finOfScalar : ScalarBlockName → Fin 8
  | .m0Plus => 0
  | .m0Sign => 1
  | .m0Standard => 2
  | .m1Even => 3
  | .m1Odd => 4
  | .mdetPlus => 5
  | .mdetSign => 6
  | .mdetStandard => 7

def scalarEquiv : Fin 8 ≃ ScalarBlockName where
  toFun := scalarOfFin
  invFun := finOfScalar
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-- Gram blocks as `Fin 14`: the six moment blocks, then the eight scalar blocks. -/
def blockEquiv : Fin 14 ≃ GramBlock 6 :=
  (finSumFinEquiv (m := 6) (n := 8)).symm.trans (Equiv.sumCongr (Equiv.refl _) scalarEquiv)

end ThomsonCompact.CoeffMap.D12
