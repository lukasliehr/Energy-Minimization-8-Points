import ThomsonNegative.Certificate.Correction.CenterKernel
import ThomsonNegative.Certificate.Correction.RecordSound
import ThomsonNegative.Structure.Packed.IdentitySound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000

open ThomsonNegative.Compact.Packed
open ThomsonNegative.Structure.Exact (recCoeffs)
local notation "seval" => ThomsonNegative.Structure.Packed.evalZ

lemma constantRecord_coeffs (w slot : ℕ) (hw : 0<w) (hw' : w<4096)
    (hs : slot<2^w) :
    recCoeffs (Nat.add (Nat.shiftLeft slot 32)
      (Nat.add (Nat.shiftLeft w 20) 4096))=[(slot:ℤ)-2^(w-1)] := by
  let word := Nat.add (Nat.shiftLeft slot 32) (Nat.add (Nat.shiftLeft w 20) 4096)
  have hL : ThomsonNegative.Structure.Exact.hdrL word=1 := by
    unfold ThomsonNegative.Structure.Exact.hdrL word
    simp only [ThomsonNegative.Structure.Exact.nat_shiftLeft,ThomsonNegative.Structure.Exact.nat_shiftRight,ThomsonNegative.Structure.Exact.nat_land,ThomsonNegative.Structure.Exact.nat_add]
    change ((slot*4294967296+(w*1048576+4096))/4096) &&& (2^8-1)=1
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hW : ThomsonNegative.Structure.Exact.hdrW word=w := by
    unfold ThomsonNegative.Structure.Exact.hdrW word
    simp only [ThomsonNegative.Structure.Exact.nat_shiftLeft,ThomsonNegative.Structure.Exact.nat_shiftRight,ThomsonNegative.Structure.Exact.nat_land,ThomsonNegative.Structure.Exact.nat_add]
    change ((slot*4294967296+(w*1048576+4096))/1048576) &&& (2^12-1)=w
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hP : Nat.shiftRight word 32=slot := by
    unfold word
    simp only [ThomsonNegative.Structure.Exact.nat_shiftLeft,ThomsonNegative.Structure.Exact.nat_shiftRight,ThomsonNegative.Structure.Exact.nat_land,ThomsonNegative.Structure.Exact.nat_add]
    change (slot*4294967296+(w*1048576+4096))/4294967296=slot
    omega
  change recCoeffs word=_
  rw [ThomsonNegative.Structure.Exact.recCoeffs,hL,hW,hP]
  simp only [ThomsonNegative.Structure.Packed.digitsN,List.range_one,List.map_cons,
    List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append,List.map_cons,
    List.map_nil,Nat.mul_zero,pow_zero,Nat.div_one,Nat.mod_eq_of_lt hs]

lemma decode_get (c : Ctx) (T : TM) (k : ℕ) (hk : k<c.m) :
    (decode c T.v).getD k 0=
      (((T.v+c.hb)%2^c.K/2^(c.W*k)%2^c.W:ℕ):ℤ)-2^(c.W-1) := by
  unfold decode digitsN
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hk,Option.map_some,Option.getD_some]

lemma coefficientRecord_coeffs (T : TM) (k : ℕ) (hk : k<11) :
    recCoeffs (coefficientRecord T k)=[(decode sourceContext T.v).getD k 0] := by
  let payload := Nat.land (Nat.add T.v sourceContext.hb) sourceContext.maskK
  let slot := Nat.land (Nat.shiftRight payload (Nat.mul 1024 k)) sourceContext.maskW
  have hmaskW : sourceContext.maskW=2^1024-1 := rfl
  have hmaskK : sourceContext.maskK=2^sourceContext.K-1 := rfl
  have hs : slot<2^1024 := by
    dsimp [slot]
    rw [hmaskW,Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have h := constantRecord_coeffs 1024 slot (by omega) (by omega) hs
  change recCoeffs (coefficientRecord T k)=[(slot:ℤ)-2^1023] at h
  rw [h]
  congr 1
  rw [decode_get sourceContext T k hk]
  change (slot:ℤ)-2^1023 =
    (((T.v+sourceContext.hb)%2^sourceContext.K/2^(1024*k)%2^1024:ℕ):ℤ)-2^1023
  congr 2
  dsimp [slot,payload]
  rw [hmaskW,hmaskK,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_eq_mod]

lemma coefficientRecord_eval (T : TM) (k : ℕ) (hk : k<11) (a : ℝ) :
    seval (recCoeffs (coefficientRecord T k)) a=
      (((decode sourceContext T.v).getD k 0:ℤ):ℝ) := by
  rw [coefficientRecord_coeffs T k hk]
  simp [ThomsonNegative.Structure.Packed.evalZ,ThomsonNegative.Structure.Packed.horner]

/-- One integer-polynomial identity validates all real height values at once. -/
theorem centerEquation_sound (numerator : ℕ → ℕ) (residual : ℕ → TM)
    (centerWord radix length width k : ℕ) (hk : k<11)
    (hcheck : (centerEquation numerator residual centerWord radix length width k).check=true)
    (a : ℝ) :
    seval (recCoeffs centerWord) a/(2:ℝ)^384=
      ∑ j : Fin 68, seval (recCoeffs (numerator j)) a*
        ((((decode sourceContext (residual j).v).getD k 0:ℤ):ℝ)/(2:ℝ)^384) := by
  have h := (centerEquation numerator residual centerWord radix length width k).sound hcheck a
  simp only [centerEquation] at h
  have hone : seval (recCoeffs 0x300201000) a=1 := by
    change seval [1] a=1
    simp [ThomsonNegative.Structure.Packed.evalZ,ThomsonNegative.Structure.Packed.horner]
  simp only [hone,mul_one] at h ⊢
  rw [← h,Finset.sum_div,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientRecord_eval _ _ hk]
  ring

#print axioms coefficientRecord_coeffs
#print axioms centerEquation_sound
end ThomsonNegative.Certificate.Correction
