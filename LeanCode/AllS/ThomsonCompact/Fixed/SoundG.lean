import ThomsonCompact.Fixed.SoundLeaf
import ThomsonCompact.Fixed.Lift
import Mathlib.Tactic.LinearCombination

/-!
# Soundness of the Γ/Q link (workstream F4)

`gLinkOk_sound`: if `gLinkOk T G = true` (and `1 ≤ T.R`), then

* the stored `Γ_k(B)` values of the table are the radix values of the `Γ` records `gamC G k`;
* `sQ(B) = s · Q(B)` for the `Q` record `qC G`;
* for every output `k < n`: `dq_k ≥ 1` and the polynomial identity (G)
  `λ_k Δc_k Γ_k(t) dz_k(t) δ_b(t)² = s dq_k Q(t)` for **all real** `t` (lifted with the per-output bound);
* coefficient bounds of `Γ` and `Q` (`CoefB`).
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-! ## The decoded data -/

/-- `Γ_k` (coefficients, lowest first). -/
def gamC (G : GTab) (k : Nat) : List ℤ := lookC (decPolyVecC G.gpc G.gpn 0) k
/-- `Q`. -/
def qC (G : GTab) : List ℤ := lookC (decPolyVecC G.qc G.qn 0) 0
/-- `dz_k` (through the denominator id of output `k`). -/
def dzC (G : GTab) (k : Nat) : List ℤ := lookC (decPolyVecC G.dzc G.dzn 0) (fld (G.inf k) 320 16)
/-- `δ_b` of the block of output `k`. -/
def blC (G : GTab) (k : Nat) : List ℤ := lookC (decPolyVecC G.blc G.bln 0) (fld (G.inf k) 336 16)
/-- `λ_k`, `dq_k`, `Δc_k`. -/
def lamG (G : GTab) (k : Nat) : Nat := fld (G.inf k) 0 128
def dqG (G : GTab) (k : Nat) : Nat := fld (G.inf k) 128 128
def dcG (G : GTab) (k : Nat) : Nat := fld (G.inf k) 256 64

/-! ## Generic list facts -/

theorem lookV_cons (i : Nat) (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat)) :
    lookV i (e :: es) = if e.1 = i then e.2 else lookV i es := by
  show Bool.rec (motive := fun _ => Bool × Nat) (lookV i es) e.2 (Nat.beq e.1 i) = _
  rw [beq_cases]

theorem lookV_sv : ∀ {lo : Nat} (l : List (Nat × Bool × Nat)), Inc lo l → ∀ i, sv (lookV i l) = lk l i
  | _, [], _, i => by simp [lookV, sv]
  | lo, e :: es, h, i => by
    rw [lookV_cons, lk_cons]
    by_cases he : e.1 = i
    · rw [if_pos he, if_pos he, lk_of_lt h.tail (by omega), add_zero]
    · rw [if_neg he, if_neg he, zero_add, lookV_sv es h.tail i]

theorem Inc.le_of_mem : ∀ {lo : Nat} {l : List (Nat × Bool × Nat)}, Inc lo l → ∀ x ∈ l, lo ≤ x.1
  | _, [], _, x, hx => by simp at hx
  | lo, e :: es, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.head
    · have := Inc.le_of_mem h.tail x hx; have := h.head; omega

theorem lk_mem : ∀ {lo : Nat} {l : List (Nat × Bool × Nat)}, Inc lo l → ∀ e ∈ l, lk l e.1 = sv e.2
  | _, [], _, e, he => by simp at he
  | lo, f :: fs, h, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact lk_head e fs h
    · have h1 := Inc.le_of_mem h.tail e he
      rw [lk_cons_ne f fs e.1 (by omega)]
      exact lk_mem h.tail e he

theorem listEq_eq : ∀ l l' : List (Nat × Bool × Nat), listEq l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listEq] at h
  | _ :: _, [], h => by simp [listEq] at h
  | e :: es, f :: fs, h => by
    have h' : (Nat.beq e.1 f.1 && Bool.rec (motive := fun _ => Bool) (not f.2.1) f.2.1 e.2.1 &&
        Nat.beq e.2.2 f.2.2 && listEq es fs) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    have e1 := Nat.eq_of_beq_eq_true h1
    have e3 := Nat.eq_of_beq_eq_true h3
    have e2 : e.2.1 = f.2.1 := by
      cases he : e.2.1 <;> cases hf : f.2.1 <;> simp_all
    rw [listEq_eq es fs h4]
    obtain ⟨a, b, c⟩ := e
    obtain ⟨a', b', c'⟩ := f
    simp only at e1 e2 e3
    rw [e1, e2, e3]

/-- A strictly increasing list of `hi - lo` indices in `[lo, hi)` hits every index. -/
theorem Inc.full : ∀ {lo hi : Nat} (l : List (Nat × Bool × Nat)), Inc lo l → (∀ e ∈ l, e.1 < hi) → lo ≤ hi →
    l.length + lo ≤ hi ∧ (l.length + lo = hi → ∀ k, lo ≤ k → k < hi → ∃ e ∈ l, e.1 = k)
  | lo, hi, [], _, _, hlo => ⟨by simp; omega, fun h k h1 h2 => by simp at h; omega⟩
  | lo, hi, e :: es, h, hb, hlo => by
    have hb' : ∀ x ∈ es, x.1 < hi := fun x hx => hb x (by simp [hx])
    have he : e.1 < hi := hb e (by simp)
    obtain ⟨i1, i2⟩ := Inc.full es h.tail hb' (by omega)
    refine ⟨by simp; have := h.head; omega, fun hl k hk1 hk2 => ?_⟩
    simp only [List.length_cons] at hl
    have hlo : e.1 = lo := by have := h.head; omega
    by_cases hk : k = lo
    · exact ⟨e, by simp, by omega⟩
    · obtain ⟨x, hx, hxk⟩ := i2 (by omega) k (by omega) hk2
      exact ⟨x, by simp [hx], hxk⟩

theorem l1_le_of_coefB {Lm wm : Nat} {c : List ℤ} (h : CoefB Lm wm c) : l1 c ≤ recBound Lm wm := by
  obtain ⟨h1, h2⟩ := h
  have hrb : recBound Lm wm = Lm * 2 ^ (wm - 1) := by
    simp only [recBound, nat_mul, nat_sub, nat_shiftLeft, one_mul]
  rw [hrb]
  have key : ∀ c : List ℤ, (∀ z ∈ c, |z| ≤ 2 ^ (wm - 1)) → l1 c ≤ c.length * 2 ^ (wm - 1) := by
    intro c
    induction c with
    | nil => simp
    | cons z c ih =>
      intro hz
      rw [l1_cons, List.length_cons]
      have h1 := hz z (by simp)
      have h2 := ih (fun y hy => hz y (by simp [hy]))
      have : z.natAbs ≤ 2 ^ (wm - 1) := by
        have : (z.natAbs : ℤ) ≤ 2 ^ (wm - 1) := by rw [Int.natCast_natAbs]; exact h1
        exact_mod_cast this
      nlinarith
  exact (key c h2).trans (Nat.mul_le_mul_right _ h1)

theorem l1_convL4 (a b c d : List ℤ) : l1 (convL (convL (convL a b) c) d) ≤ l1 a * l1 b * l1 c * l1 d := by
  have h1 := l1_convL (convL (convL a b) c) d
  have h2 := l1_convL (convL a b) c
  have h3 := l1_convL a b
  calc l1 (convL (convL (convL a b) c) d) ≤ l1 (convL (convL a b) c) * l1 d := h1
    _ ≤ (l1 (convL a b) * l1 c) * l1 d := Nat.mul_le_mul_right _ h2
    _ ≤ (l1 a * l1 b * l1 c) * l1 d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)

/-! ## The per-output identity -/

theorem gIdOk_cons (G : GTab) (kg kq bnd : Nat) (qv : Bool × Nat) (dz bl : List (Nat × Bool × Nat))
    (g : Nat × Bool × Nat) (gl : List (Nat × Bool × Nat)) (h : gIdOk G kg kq bnd qv dz bl (g :: gl) = true) :
    (xor qv.1 (xor g.2.1 (lookV (fld (G.inf g.1) 320 16) dz).1) = false ∧
      lamG G g.1 * dcG G g.1 * (g.2.2 * (lookV (fld (G.inf g.1) 320 16) dz).2) *
        ((lookV (fld (G.inf g.1) 336 16) bl).2 * (lookV (fld (G.inf g.1) 336 16) bl).2) =
        G.s * dqG G g.1 * qv.2) ∧
    1 ≤ dqG G g.1 ∧ 2 * (lamG G g.1 * dcG G g.1 * kg + G.s * dqG G g.1 * kq) < bnd ∧
    gIdOk G kg kq bnd qv dz bl gl = true := by
  have h' : ((Bool.rec (motive := fun _ => Bool)
      (Nat.beq (Nat.mul (Nat.mul (Nat.mul (fld (G.inf g.1) 0 128) (fld (G.inf g.1) 256 64))
          (Nat.mul g.2.2 (lookV (fld (G.inf g.1) 320 16) dz).2))
        (Nat.mul (lookV (fld (G.inf g.1) 336 16) bl).2 (lookV (fld (G.inf g.1) 336 16) bl).2))
        (Nat.mul (Nat.mul G.s (fld (G.inf g.1) 128 128)) qv.2))
      false (xor qv.1 (xor g.2.1 (lookV (fld (G.inf g.1) 320 16) dz).1)) &&
      Nat.ble 1 (fld (G.inf g.1) 128 128) &&
      Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (Nat.mul (fld (G.inf g.1) 0 128) (fld (G.inf g.1) 256 64)) kg)
        (Nat.mul (Nat.mul G.s (fld (G.inf g.1) 128 128)) kq))) bnd) &&
      gIdOk G kg kq bnd qv dz bl gl) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  refine ⟨?_, Nat.le_of_ble_eq_true h2, ?_, h4⟩
  · cases hx : xor qv.1 (xor g.2.1 (lookV (fld (G.inf g.1) 320 16) dz).1)
    · rw [hx] at h1
      exact ⟨rfl, Nat.eq_of_beq_eq_true h1⟩
    · rw [hx] at h1; exact (Bool.false_ne_true h1).elim
  · exact Nat.blt_eq.mp h3

theorem gIdOk_mem (G : GTab) (kg kq bnd : Nat) (qv : Bool × Nat) (dz bl : List (Nat × Bool × Nat)) :
    ∀ gl : List (Nat × Bool × Nat), gIdOk G kg kq bnd qv dz bl gl = true → ∀ g ∈ gl,
      (xor qv.1 (xor g.2.1 (lookV (fld (G.inf g.1) 320 16) dz).1) = false ∧
        lamG G g.1 * dcG G g.1 * (g.2.2 * (lookV (fld (G.inf g.1) 320 16) dz).2) *
          ((lookV (fld (G.inf g.1) 336 16) bl).2 * (lookV (fld (G.inf g.1) 336 16) bl).2) =
          G.s * dqG G g.1 * qv.2) ∧
      1 ≤ dqG G g.1 ∧ 2 * (lamG G g.1 * dcG G g.1 * kg + G.s * dqG G g.1 * kq) < bnd
  | [], _, g, hg => by simp at hg
  | g' :: gl, h, g, hg => by
    obtain ⟨a, b, c, d⟩ := gIdOk_cons G kg kq bnd qv dz bl g' gl h
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨a, b, c⟩
    · exact gIdOk_mem G kg kq bnd qv dz bl gl d g hg

/-- Signed form of one identity. -/
theorem sv_identity (lam dc s dq : Nat) (g d b q : Bool × Nat)
    (hs : xor q.1 (xor g.1 d.1) = false) (hm : lam * dc * (g.2 * d.2) * (b.2 * b.2) = s * dq * q.2) :
    (lam : ℤ) * dc * sv g * sv d * sv b ^ 2 = (s : ℤ) * dq * sv q := by
  have hm' : ((lam : ℤ) * dc * (g.2 * d.2) * (b.2 * b.2)) = (s : ℤ) * dq * q.2 := by exact_mod_cast hm
  obtain ⟨g1, g2⟩ := g
  obtain ⟨d1, d2⟩ := d
  obtain ⟨b1, b2⟩ := b
  obtain ⟨q1, q2⟩ := q
  simp only at hs hm' ⊢
  cases g1 <;> cases d1 <;> cases q1 <;> cases b1 <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at hs <;>
    simp only [sv, Bool.false_eq_true, ↓reduceIte] <;>
    first | linear_combination hm' | linear_combination (-1 : ℤ) * hm'

/-! ## The theorem -/

theorem gLinkOk_parts (T : Tab) (G : GTab) (h : gLinkOk T G = true) :
    1 ≤ polyVecOk G.LG G.wG T.n G.gpc G.gpn 0 1 ∧ 1 ≤ polyVecOk G.LQ G.wQ 1 G.qc G.qn 0 1 ∧
    1 ≤ polyVecOk G.LD G.wD 4096 G.dzc G.dzn 0 1 ∧ 1 ≤ polyVecOk G.LB G.wB 4096 G.blc G.bln 0 1 ∧
    decPolyVec T.R G.gpc G.gpn 0 = decValVec T.gc T.gn 0 ∧ (decPolyVec T.R G.gpc G.gpn 0).length = T.n ∧
    (lookV 0 (decPolyVec T.R G.qc G.qn 0)).1 = false ∧
    G.s * (lookV 0 (decPolyVec T.R G.qc G.qn 0)).2 = T.sq ∧
    gIdOk G (recBound G.LG G.wG * recBound G.LD G.wD * (recBound G.LB G.wB * recBound G.LB G.wB))
      (recBound G.LQ G.wQ) (2 ^ T.R) (lookV 0 (decPolyVec T.R G.qc G.qn 0))
      (decPolyVec T.R G.dzc G.dzn 0) (decPolyVec T.R G.blc G.bln 0) (decPolyVec T.R G.gpc G.gpn 0) = true := by
  have h' : (Nat.ble 1 (polyVecOk G.LG G.wG T.n G.gpc G.gpn 0 1) && Nat.ble 1 (polyVecOk G.LQ G.wQ 1 G.qc G.qn 0 1) &&
      Nat.ble 1 (polyVecOk G.LD G.wD 4096 G.dzc G.dzn 0 1) && Nat.ble 1 (polyVecOk G.LB G.wB 4096 G.blc G.bln 0 1) &&
      listEq (decPolyVec T.R G.gpc G.gpn 0) (decValVec T.gc T.gn 0) &&
      Nat.beq (List.length (decPolyVec T.R G.gpc G.gpn 0)) T.n &&
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.mul G.s (lookV 0 (decPolyVec T.R G.qc G.qn 0)).2) T.sq)
          (not (lookV 0 (decPolyVec T.R G.qc G.qn 0)).1) &&
        gIdOk G (Nat.mul (Nat.mul (recBound G.LG G.wG) (recBound G.LD G.wD))
            (Nat.mul (recBound G.LB G.wB) (recBound G.LB G.wB))) (recBound G.LQ G.wQ) (Nat.shiftLeft 1 T.R)
          (lookV 0 (decPolyVec T.R G.qc G.qn 0))
          (decPolyVec T.R G.dzc G.dzn 0) (decPolyVec T.R G.blc G.bln 0) (decPolyVec T.R G.gpc G.gpn 0))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7, h8⟩ := h'
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4,
    listEq_eq _ _ h5, Nat.eq_of_beq_eq_true h6, ?_, ?_, ?_⟩
  · cases hq : (lookV 0 (decPolyVec T.R G.qc G.qn 0)).1
    · rfl
    · rw [hq] at h7; exact (Bool.false_ne_true h7).elim
  · cases hq : (lookV 0 (decPolyVec T.R G.qc G.qn 0)).1
    · rw [hq] at h7; exact Nat.eq_of_beq_eq_true h7
    · rw [hq] at h7; exact (Bool.false_ne_true h7).elim
  · rw [show Nat.shiftLeft 1 T.R = 2 ^ T.R from Nat.one_shiftLeft _] at h8
    exact h8

/-- **Soundness of the Γ/Q link.** -/
theorem gLinkOk_sound (T : Tab) (G : GTab) (hR : 0 < T.R) (h : gLinkOk T G = true) :
    (∀ k, lk (decValVec T.gc T.gn 0) k = horner ((2 : ℤ) ^ T.R) (gamC G k)) ∧
    (T.sq : ℤ) = G.s * horner ((2 : ℤ) ^ T.R) (qC G) ∧
    (∀ k, CoefB G.LG G.wG (gamC G k)) ∧ CoefB G.LQ G.wQ (qC G) ∧
    ∀ k, k < T.n → 1 ≤ dqG G k ∧ ∀ t : ℝ,
      ((lamG G k * dcG G k : ℕ) : ℝ) * evalZ (gamC G k) t * evalZ (dzC G k) t * evalZ (blC G k) t ^ 2 =
        ((G.s * dqG G k : ℕ) : ℝ) * evalZ (qC G) t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := gLinkOk_parts T G h
  obtain ⟨g1, g2, g3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ p1
  obtain ⟨q1, _, q3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ p2
  obtain ⟨d1, _, d3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ p3
  obtain ⟨b1, _, b3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ p4
  have hG : ∀ k, lk (decPolyVec T.R G.gpc G.gpn 0) k = horner ((2 : ℤ) ^ T.R) (gamC G k) := fun k =>
    lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) g1 k
  have hQv : sv (lookV 0 (decPolyVec T.R G.qc G.qn 0)) = horner ((2 : ℤ) ^ T.R) (qC G) := by
    rw [lookV_sv _ q1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) q1 0
  have hQpos : (((lookV 0 (decPolyVec T.R G.qc G.qn 0)).2 : ℕ) : ℤ) = horner ((2 : ℤ) ^ T.R) (qC G) := by
    rw [← hQv]; simp [sv, p7]
  refine ⟨fun k => by rw [← p5]; exact hG k, ?_, fun k => lookC_mem ⟨by simp, by simp⟩ g3,
    lookC_mem ⟨by simp, by simp⟩ q3, fun k hk => ?_⟩
  · rw [← p8, ← hQpos]; push_cast; ring
  -- the Γ entry of output k
  have hfull := (Inc.full (decPolyVec T.R G.gpc G.gpn 0) g1 g2 (Nat.zero_le _)).2 (by rw [p6]; simp) k
    (Nat.zero_le _) hk
  obtain ⟨g, hg, hgk⟩ := hfull
  obtain ⟨⟨hs, hm⟩, hdq, hbd⟩ := gIdOk_mem G _ _ _ _ _ _ _ p9 g hg
  rw [hgk] at hs hm hdq hbd
  refine ⟨hdq, fun t => ?_⟩
  -- radix identity
  have hgv : sv g.2 = horner ((2 : ℤ) ^ T.R) (gamC G k) := by
    rw [← hG k, ← hgk]; exact (lk_mem g1 g hg).symm
  have hdv : sv (lookV (fld (G.inf k) 320 16) (decPolyVec T.R G.dzc G.dzn 0)) =
      horner ((2 : ℤ) ^ T.R) (dzC G k) := by
    rw [lookV_sv _ d1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) d1 _
  have hbv : sv (lookV (fld (G.inf k) 336 16) (decPolyVec T.R G.blc G.bln 0)) =
      horner ((2 : ℤ) ^ T.R) (blC G k) := by
    rw [lookV_sv _ b1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) b1 _
  have hrad := sv_identity _ _ _ _ _ _ _ _ hs hm
  rw [hgv, hdv, hbv, hQv] at hrad
  -- the polynomial `λΔc Γ dz δ² - s dq Q`
  have hcG : CoefB G.LG G.wG (gamC G k) := lookC_mem ⟨by simp, by simp⟩ g3
  have hcQ : CoefB G.LQ G.wQ (qC G) := lookC_mem ⟨by simp, by simp⟩ q3
  have hcD : CoefB G.LD G.wD (dzC G k) := lookC_mem ⟨by simp, by simp⟩ d3
  have hcB : CoefB G.LB G.wB (blC G k) := lookC_mem ⟨by simp, by simp⟩ b3
  have hP0 : horner ((2 ^ T.R : ℕ) : ℤ) (addL (scaleL ((lamG G k * dcG G k : ℕ) : ℤ)
      (convL (convL (convL (gamC G k) (dzC G k)) (blC G k)) (blC G k)))
      (scaleL (-((G.s * dqG G k : ℕ) : ℤ)) (qC G))) = 0 := by
    simp only [hornerZ_addL, hornerZ_scaleL, hornerZ_convL]
    push_cast
    linear_combination hrad
  have hl1 : l1 (addL (scaleL ((lamG G k * dcG G k : ℕ) : ℤ)
      (convL (convL (convL (gamC G k) (dzC G k)) (blC G k)) (blC G k)))
      (scaleL (-((G.s * dqG G k : ℕ) : ℤ)) (qC G))) ≤ lamG G k * dcG G k *
      (recBound G.LG G.wG * recBound G.LD G.wD * (recBound G.LB G.wB * recBound G.LB G.wB)) +
      G.s * dqG G k * recBound G.LQ G.wQ := by
    refine (l1_addL _ _).trans (Nat.add_le_add ?_ ?_)
    · rw [l1_scaleL, Int.natAbs_natCast]
      refine Nat.mul_le_mul_left _ ((l1_convL4 _ _ _ _).trans ?_)
      have e1 := l1_le_of_coefB hcG
      have e2 := l1_le_of_coefB hcD
      have e3 := l1_le_of_coefB hcB
      calc l1 (gamC G k) * l1 (dzC G k) * l1 (blC G k) * l1 (blC G k)
          ≤ recBound G.LG G.wG * recBound G.LD G.wD * recBound G.LB G.wB * recBound G.LB G.wB := by gcongr
        _ = _ := by ring
    · rw [l1_scaleL, Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ (l1_le_of_coefB hcQ)
  have hlift := lift (2 ^ T.R) (Nat.one_lt_two_pow (by omega)) _
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hl1) hbd) hP0 t
  simp only [evalZ_addL, evalZ_scaleL, evalZ_convL] at hlift
  push_cast at hlift ⊢
  linear_combination hlift

#print axioms gLinkOk_sound

end ThomsonCompact.Fixed
