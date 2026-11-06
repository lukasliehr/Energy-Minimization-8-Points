import ThomsonNegative.Certificate.Correction.RecordKernel
import ThomsonNegative.Certificate.FactorSound
import ThomsonNegative.Structure.Packed.PolyDecode

noncomputable section
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

lemma evalQ_differences (slots : List ℕ) (bias denominator : ℕ) (a : ℝ) :
    evalQ (slots.map (fun v => differenceArg (v,bias) denominator)) a=
    ThomsonNegative.Structure.Packed.evalZ
      (slots.map (fun (v : ℕ) => (v:ℤ)-(bias:ℤ))) a/(denominator:ℝ) := by
  induction slots with
  | nil => simp [evalQ,ThomsonNegative.Structure.Packed.evalZ,
      ThomsonNegative.Structure.Packed.horner]
  | cons s ss ih =>
    simp only [List.map_cons,evalQ,ThomsonNegative.Structure.Packed.evalZ,
      ThomsonNegative.Structure.Packed.horner_cons] at ih ⊢
    rw [ih]
    rw [differenceArg_val]
    simp only [pairReal,Int.cast_sub,Int.cast_natCast]
    ring

lemma recordArgs_eval (x d : ℕ) (a : ℝ) :
    evalQ (recordArgs x d) a=
      ThomsonNegative.Structure.Packed.evalZ
        (ThomsonNegative.Structure.Exact.recCoeffs x) a/(d:ℝ) := by
  unfold recordArgs
  have he : (List.range (Nat.land (Nat.shiftRight x 12) 255)).map
      (fun k => ThomsonNegative.Structure.Exact.fld (Nat.shiftRight x 32)
        (Nat.mul (Nat.land (Nat.shiftRight x 20) 4095) k)
        (Nat.land (Nat.shiftRight x 20) 4095)) =
      ThomsonNegative.Structure.Packed.digitsN
        (ThomsonNegative.Structure.Exact.hdrW x)
        (ThomsonNegative.Structure.Exact.hdrL x) (Nat.shiftRight x 32) := by
    unfold ThomsonNegative.Structure.Packed.digitsN
    apply List.map_congr_left
    intro k hk
    exact (ThomsonNegative.Structure.Exact.land_mask _ _).trans
      (by rw [ThomsonNegative.Structure.Exact.nat_shiftRight]; rfl)
  have hmap :
      ((List.range (Nat.land (Nat.shiftRight x 12) 255)).map
        (fun k => differenceArg
          (ThomsonNegative.Structure.Exact.fld (Nat.shiftRight x 32)
            (Nat.mul (Nat.land (Nat.shiftRight x 20) 4095) k)
            (Nat.land (Nat.shiftRight x 20) 4095),
           Nat.pow 2 (Nat.sub (Nat.land (Nat.shiftRight x 20) 4095) 1)) d)).reverse =
      (ThomsonNegative.Structure.Packed.digitsN
        (ThomsonNegative.Structure.Exact.hdrW x)
        (ThomsonNegative.Structure.Exact.hdrL x) (Nat.shiftRight x 32)).reverse.map
          (fun v => differenceArg (v,2^(ThomsonNegative.Structure.Exact.hdrW x-1)) d) := by
    rw [← he,List.map_reverse,List.map_map]
    rfl
  rw [hmap,evalQ_differences]
  simp only [ThomsonNegative.Structure.Exact.recCoeffs,Nat.cast_pow,Nat.cast_ofNat]

theorem recordTM_sound {N S B W : ℕ} (hg : Good N S B W)
    {A : TM} {a : ℝ → ℝ} (ha : Encl (mkCtx N S B W) A a)
    (x denominator : ℕ)
    (hok : (recordTM (mkCtx N S B W) A x denominator).ok=true) :
    Encl (mkCtx N S B W) (recordTM (mkCtx N S B W) A x denominator)
      (fun t => ThomsonNegative.Structure.Packed.evalZ
        (ThomsonNegative.Structure.Exact.recCoeffs x) (a t)/(denominator:ℝ)) := by
  exact (hornerRefresh_sound hg ha _ hok).congr
    (fun t _ => recordArgs_eval x denominator (a t))

#print axioms recordTM_sound
end ThomsonNegative.Certificate.Correction
