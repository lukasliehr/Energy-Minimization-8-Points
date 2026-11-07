import ThomsonNegative.Certificate.RFKernel
import ThomsonNegative.Compact.Packed.Comp

/-! One enclosure proof for every shifted rational basis/correction record. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

variable {N S B W : ℕ}

noncomputable def PolyData.eval (p : PolyData) (a : ℝ) : ℝ := evalQ (polyArgs p) a

noncomputable def RFData.eval (r : RFData) (a : ℝ) : ℝ :=
  r.numerator.eval a * qval r.unitInverse *
    (r.factors.map (fun p => (p.eval a)⁻¹)).prod

theorem rationalTM_sound (hg : Good N S B W) (a : Bool × ℕ × ℕ)
    (hok : (rationalTM (mkCtx N S B W) a).ok = true) :
    Encl (mkCtx N S B W) (rationalTM (mkCtx N S B W) a) (fun _ => qval a) :=
  constTM_sound hg _ _ _ _ (ratMag_err a) hok

theorem hornerRefresh_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) :
    ∀ L, (hornerRefresh (mkCtx N S B W) A L).ok = true →
      Encl (mkCtx N S B W) (hornerRefresh (mkCtx N S B W) A L)
        (fun t => evalQ L (a t))
  | [], _ => zero_sound.congr (fun t _ => by simp [evalQ])
  | p :: rest, hok => by
    have hp := add_ok hok
    have hm := mul_ok hp.1
    have hr := hornerRefresh_sound hg ha rest hm.1
    have h := refresh_sound hg (add_sound (mul_sound hg hr ha hp.1)
      (rationalTM_sound hg p hp.2) (show (add (mkCtx N S B W)
        (mul (mkCtx N S B W) (hornerRefresh (mkCtx N S B W) A rest) A)
        (rationalTM (mkCtx N S B W) p)).ok = true from hok))
    exact h.congr (fun t _ => by simp only [evalQ]; ring)

theorem polynomialTM_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (p : PolyData)
    (hok : (polynomialTM (mkCtx N S B W) A p).ok = true) :
    Encl (mkCtx N S B W) (polynomialTM (mkCtx N S B W) A p)
      (fun t => p.eval (a t)) := hornerRefresh_sound hg ha _ hok

theorem inverseFactors_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (fuel tolerance : ℕ) :
    ∀ (L : List PolyData) (acc : TM) (f : ℝ → ℝ),
      Encl (mkCtx N S B W) acc f →
      (inverseFactors (mkCtx N S B W) fuel tolerance A L acc).ok = true →
      Encl (mkCtx N S B W) (inverseFactors (mkCtx N S B W) fuel tolerance A L acc)
        (fun t => f t * (L.map (fun p => (p.eval (a t))⁻¹)).prod)
  | [], acc, f, hf, _ => hf.congr (fun t _ => by simp)
  | p :: rest, acc, f, hf, hok => by
    have hp : (refresh (mkCtx N S B W) (mul (mkCtx N S B W) acc
        (invN (mkCtx N S B W) fuel tolerance (polynomialTM (mkCtx N S B W) A p)))).ok = true := by
      -- Every factor step propagates its input's Boolean side conditions.
      have keep (L : List PolyData) (T : TM) :
          (inverseFactors (mkCtx N S B W) fuel tolerance A L T).ok = true → T.ok = true := by
        induction L generalizing T with
        | nil => exact id
        | cons u us ih =>
          intro h
          have hs := ih (refresh (mkCtx N S B W) (mul (mkCtx N S B W) T
            (invN (mkCtx N S B W) fuel tolerance (polynomialTM (mkCtx N S B W) A u)))) h
          exact (mul_ok hs).1
      exact keep rest _ hok
    have hm := mul_ok hp
    have hd : (polynomialTM (mkCtx N S B W) A p).ok = true := by
      exact (mul_ok (recip_ok hm.2).2).2
    have hi := invN_sound hg (polynomialTM_sound hg ha p hd) fuel tolerance hm.2
    have hstep := refresh_sound hg (mul_sound hg hf hi.2 hp)
    have h := inverseFactors_sound hg ha fuel tolerance rest _ _ hstep hok
    exact h.congr (fun t _ => by simp only [List.map_cons, List.prod_cons]; ring)

theorem rationalFunctionTM_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (fuel tolerance : ℕ) (r : RFData)
    (hok : (rationalFunctionTM (mkCtx N S B W) fuel tolerance A r).ok = true) :
    Encl (mkCtx N S B W) (rationalFunctionTM (mkCtx N S B W) fuel tolerance A r)
      (fun t => r.eval (a t)) := by
  have hm := mul_ok hok
  have hp := polynomialTM_sound hg ha r.numerator hm.1
  have hu : (rationalTM (mkCtx N S B W) r.unitInverse).ok = true := by
    have keep (L : List PolyData) (T : TM) :
        (inverseFactors (mkCtx N S B W) fuel tolerance A L T).ok = true → T.ok = true := by
      induction L generalizing T with
      | nil => exact id
      | cons u us ih =>
        intro h
        have hs := ih (refresh (mkCtx N S B W) (mul (mkCtx N S B W) T
          (invN (mkCtx N S B W) fuel tolerance (polynomialTM (mkCtx N S B W) A u)))) h
        exact (mul_ok hs).1
    exact keep _ _ hm.2
  have hi := inverseFactors_sound hg ha fuel tolerance r.factors _ _
    (rationalTM_sound hg r.unitInverse hu) hm.2
  have h := refresh_sound hg (mul_sound hg hp hi (show (mul (mkCtx N S B W)
    (polynomialTM (mkCtx N S B W) A r.numerator)
    (inverseFactors (mkCtx N S B W) fuel tolerance A r.factors
      (rationalTM (mkCtx N S B W) r.unitInverse))).ok = true from hok))
  exact h.congr (fun t _ => by simp only [RFData.eval]; ring)

#print axioms polynomialTM_sound
#print axioms rationalFunctionTM_sound

/-- Reuse the proved Taylor arithmetic as ordinary interval arithmetic.
This transfer keeps the same semantic function and the same parameter domain. -/
theorem collapseAt_sound (hg : Good N S B W) {N' B' W' : ℕ}
    (hg' : Good N' S B' W') {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (ng : Bool) (mag : ℕ)
    (hok : (collapseAt (mkCtx N S B W) (mkCtx N' S B' W') ng mag A).ok = true) :
    Encl (mkCtx N' S B' W')
      (collapseAt (mkCtx N S B W) (mkCtx N' S B' W') ng mag A) a := by
  let center : ℝ := (if ng then -(mag:ℝ) else mag)/2^S
  let delta := addC (mkCtx N S B W) (!ng) mag 0 A
  have hh : ((constTM (mkCtx N' S B' W') ng mag (rangeX (mkCtx N S B W) delta)).ok &&
      delta.ok)=true := hok
  simp only [Bool.and_eq_true] at hh
  have hf := hh
  have hd : Encl (mkCtx N S B W) delta (fun t => a t-center) := by
    have h := addC_sound ha (!ng) mag 0 (-center) (by
      dsimp [center]; cases ng <;> simp [neg_div]) hf.2 hg
    exact h.congr (fun t _ => by ring)
  have hc : Encl (mkCtx N' S B' W') (constTM (mkCtx N' S B' W') ng mag 0)
      (fun _ => center) := constTM_sound hg' ng mag 0 center (by simp [center]) hf.1
  have h := widen_sound (rangeX (mkCtx N S B W) delta) hc
    (g := a) (rangeX_sound hg hd)
  exact h.of_fields rfl rfl rfl rfl

#print axioms collapseAt_sound
end ThomsonNegative.Certificate
