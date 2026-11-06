import ThomsonCompact.Floor.B.SoundPV

/-!
# Soundness of the row leaf (F3b)

Semantic hypotheses:
* `RowSem nI r a0 σ uD H dl`: the re-expanded row `r` encloses the true entries `H m` (`m ∈ ms`, all `m < nI`) and
  the true denominator `dl` (= `λ d`) on `|u| ≤ 1` (`a = a0 + σ u`), with magnitude bounds on `|u| ≤ uD`
  (proved once per degree by the bridge leaves; `nI` = number of input coordinates of the degree);
* `ChanSem nI cb zl`: the channel vectors `chanAll … cvc` (at least `nI` of them) are the packed integer vectors `zl m`.

`rowOk_sound`: every control-channel checkpoint encloses `t ↦ 2^κC (Σ_m H_m(a(t)) z_m,ch) / dl(a(t))`
and the error claim `Ẽ_j` bounds the structured target errors and the box radii.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-! ## Row data in integer form -/

/-- re-expanded entry coefficient `ê_{idx,k}` -/
def RowT.ehat (r : RowT) (idx k : ℕ) : ℤ := (slot r.w (r.t.getD k 0) idx : ℤ) - 2 ^ (r.w - 1)

/-- entry index at position `idx` -/
def RowT.mAt (r : RowT) (idx : ℕ) : ℕ := r.msL.getD idx 0

/-- the coefficient list of the entry at position `idx` -/
def RowT.ecoef (r : RowT) (idx : ℕ) : List ℤ := (List.range r.L).map (r.ehat idx)

/-- signed value of a sign-magnitude pair -/
def sv (x : Bool × ℕ) : ℤ := if x.1 then -(x.2 : ℤ) else x.2

/-- re-expanded denominator coefficients `d̂_k` -/
def RowT.dcoef (r : RowT) : List ℤ := r.dhL.map sv

/-- **Row semantics** (per degree): entries and denominator of the re-expanded row enclose the true ones on
`|u| ≤ 1`, magnitude bounds on `|u| ≤ uD`, entries sorted. -/
structure RowSem (nI : ℕ) (r : RowT) (a0 σ uD : ℝ) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) : Prop where
  ent : ∀ idx < r.nms, ∀ u : ℝ, |u| ≤ 1 →
    |(2 : ℝ) ^ r.F * H (r.mAt idx) (a0 + σ * u) - evalZ (r.ecoef idx) u| ≤ (r.dE : ℝ) / 2
  den : ∀ u : ℝ, |u| ≤ 1 → |(2 : ℝ) ^ r.Fd * dl (a0 + σ * u) - evalZ r.dcoef u| ≤ (r.Ld : ℝ) / 2
  mag : ∀ idx < r.nms, ∀ u : ℝ, |u| ≤ uD → |(2 : ℝ) ^ r.F * H (r.mAt idx) (a0 + σ * u)| ≤ (r.magL.getD idx 0 : ℝ)
  len : r.msL.length = r.nms
  wpos : 1 ≤ r.w
  tlen : r.t.length = r.L
  Lpos : 1 ≤ r.L
  sorted : r.msL.Pairwise (· < ·)
  ltn : ∀ m ∈ r.msL, m < nI

/-- **Channel semantics** (per cell): the channel vectors `cvA` are packed integer vectors `zl m` of `nC` slots of
width `WC`, `|z| ≤ cmax`. -/
structure ChanSem (nI : ℕ) (cb : CellB) (cvA : List ℕ) (zl : ℕ → List ℤ) : Prop where
  len : ∀ m, (zl m).length = cb.nC
  bnd : ∀ m, ∀ x ∈ zl m, |x| ≤ (cb.cmax : ℤ)
  mod : ∀ m < cvA.length, (cvA.getD m 0 : ℤ) % 2 ^ cb.KC = horner (2 ^ cb.WC : ℤ) (zl m) % 2 ^ cb.KC
  cvl : nI ≤ cvA.length

/-! ## Selection of the row's channel vectors -/

theorem selectL_spec : ∀ (all ms : List ℕ) (m0 : ℕ), ms.Pairwise (· < ·) →
    (∀ m ∈ ms, m0 ≤ m ∧ m < m0 + all.length) →
    selectL all ms m0 = ms.map fun m => all.getD (m - m0) 0
  | [], ms, m0, _, h => by
    cases ms with
    | nil => rfl
    | cons m ms => have := h m (by simp); simp at this; omega
  | x :: all, ms, m0, hs, h => by
    cases ms with
    | nil => rfl
    | cons m ms =>
      show cond (Nat.beq m0 m) (x :: selectL all ms (Nat.succ m0)) (selectL all (m :: ms) (Nat.succ m0)) = _
      have hm := h m (by simp)
      have hs' := List.pairwise_cons.mp hs
      by_cases hmm : m0 = m
      · subst hmm
        rw [Nat.beq_refl, cond_true, List.map_cons, Nat.sub_self, List.getD_cons_zero]
        congr 1
        rw [selectL_spec all ms (Nat.succ m0) hs'.2 (fun y hy => by
          have := hs'.1 y hy; have := h y (List.mem_cons_of_mem _ hy); simp at this ⊢; omega)]
        apply List.map_congr_left
        intro y hy
        have := hs'.1 y hy
        rw [show y - m0 = (y - Nat.succ m0) + 1 by omega, List.getD_cons_succ]
      · have hne : Nat.beq m0 m = false := Bool.eq_false_iff.mpr (fun h => hmm (Nat.eq_of_beq_eq_true h))
        rw [hne, cond_false, selectL_spec all (m :: ms) (Nat.succ m0) hs (fun y hy => by
          have h1 := h y hy
          have h2 : m0 < y := by
            rcases List.mem_cons.mp hy with rfl | hy
            · omega
            · have := hs'.1 y hy; omega
          simp at h1 ⊢; omega)]
        apply List.map_congr_left
        intro y hy
        have h2 : m0 < y := by
          rcases List.mem_cons.mp hy with rfl | hy
          · have := h y (by simp); omega
          · have := hs'.1 y hy; have := h m (by simp); omega
        rw [show y - m0 = (y - Nat.succ m0) + 1 by omega, List.getD_cons_succ]

/-! ## The contraction modulo `2^KC` -/

theorem mod_helper (X Y M : ℤ) : (X + (M - Y % M)) % M = (X - Y) % M := by
  have hq := Int.mul_ediv_add_emod Y M
  rw [show X + (M - Y % M) = (X - Y) + M * (Y / M + 1) by linear_combination -hq, Int.add_mul_emod_self_left]

theorem contractK_mod (w KC : ℕ) (hw : 1 ≤ w) (cvs : List ℕ) (t : ℕ) :
    (contractK w KC cvs (lsum cvs) t : ℤ) % 2 ^ KC =
      ((List.zipWith (fun (s cv : ℕ) => ((s : ℤ) - 2 ^ (w - 1)) * (cv : ℤ)) (slotsL w cvs.length t) cvs).sum) %
        2 ^ KC := by
  have hl : lsum cvs = cvs.sum := by
    induction cvs with
    | nil => rfl
    | cons x l ih => show x + lsum l = _; rw [ih, List.sum_cons]
  have hd := dotOff_eq w cvs t 0
  have hz : ∀ (sl : List ℕ) (cv : List ℕ), sl.length = cv.length →
      ((List.zipWith (fun (s cv : ℕ) => ((s : ℤ) - 2 ^ (w - 1)) * (cv : ℤ)) sl cv).sum) =
        (((List.zipWith (· * ·) sl cv).sum : ℕ) : ℤ) - 2 ^ (w - 1) * ((cv.sum : ℕ) : ℤ) := by
    intro sl cv hlen
    induction sl generalizing cv with
    | nil => cases cv <;> simp at hlen ⊢
    | cons s sl ih =>
      cases cv with
      | nil => simp at hlen
      | cons c cv =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        rw [ih cv (by simpa using hlen)]
        push_cast; ring
  rw [hz _ _ (slotsL_length w _ t)]
  have hm : Nat.land (Nat.mul (Nat.pow 2 (Nat.sub w 1)) (lsum cvs)) (mask KC) = (2 ^ (w - 1) * cvs.sum) % 2 ^ KC := by
    show (2 ^ (w - 1) * lsum cvs) &&& mask KC = _
    rw [hl, mask_eq, Nat.and_two_pow_sub_one_eq_mod]
  have hle : (2 ^ (w - 1) * cvs.sum) % 2 ^ KC ≤ 2 ^ KC := (Nat.mod_lt _ (Nat.two_pow_pos _)).le
  show ((Nat.land (Nat.add (dotOff w (mask w) cvs t 0) (Nat.sub (Nat.pow 2 KC)
    (Nat.land (Nat.mul (Nat.pow 2 (Nat.sub w 1)) (lsum cvs)) (mask KC)))) (mask KC) : ℕ) : ℤ) % 2 ^ KC = _
  rw [hm]
  have e : ((Nat.land (Nat.add (dotOff w (mask w) cvs t 0) (Nat.sub (Nat.pow 2 KC)
      ((2 ^ (w - 1) * cvs.sum) % 2 ^ KC))) (mask KC) : ℕ) : ℤ) =
      ((dotOff w (mask w) cvs t 0 + (2 ^ KC - (2 ^ (w - 1) * cvs.sum) % 2 ^ KC) : ℕ) : ℤ) % 2 ^ KC := by
    rw [mask_eq KC]; exact toZ_mod_mask
  rw [e, Int.emod_emod, hd, Nat.zero_add]
  push_cast [Nat.cast_sub hle]
  exact mod_helper _ _ _

/-! ## The exact affine TM and its powers -/

variable {N S B W : ℕ}

theorem digitsN_pad {W : ℕ} (m : ℕ) (L : List ℕ) (hL : L.length ≤ m) (hd : ∀ d ∈ L, d < 2 ^ W) :
    digitsN W m (Nat.ofDigits (2 ^ W) L) = L ++ List.replicate (m - L.length) 0 := by
  have hW : 0 < 2 ^ W := Nat.two_pow_pos W
  have hd' : ∀ d ∈ L ++ List.replicate (m - L.length) 0, d < 2 ^ W := by
    intro d hdm
    rcases List.mem_append.mp hdm with h | h
    · exact hd d h
    · rw [List.eq_of_mem_replicate h]; exact hW
  have hlen : (L ++ List.replicate (m - L.length) 0).length = m := by simp; omega
  have hval : Nat.ofDigits (2 ^ W) (L ++ List.replicate (m - L.length) 0) = Nat.ofDigits (2 ^ W) L := by
    rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, mul_zero, add_zero]
  have := digitsN_ofDigits (W := W) _ hd'
  rw [hlen, hval] at this
  exact this

theorem zipWith_sub_zeros (k : ℕ) :
    List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) (List.replicate k 0) (List.replicate k 0) =
      List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.zipWith_cons_cons, ih]; simp

theorem tmAff_sound (hg : Good N S B W) (ng : Bool) (a0 a1 : ℕ) (h0 : a0 < 2 ^ W) (h1 : a1 < 2 ^ W)
    (hN : 1 ≤ N) (hok : (tmAff (mkCtx N S B W) ng a0 a1).ok = true) :
    Encl (mkCtx N S B W) (tmAff (mkCtx N S B W) ng a0 a1)
      (fun t => ((if ng then -(a0 : ℝ) else a0) + a1 * t) / 2 ^ S) := by
  have h := ofPQ_sound hg (Nat.add (cond ng 0 a0) (Nat.shiftLeft a1 W)) (cond ng a0 0) 0 hok
  refine h.congr (fun t _ => ?_)
  have hp0 : cond ng 0 a0 < 2 ^ W := by cases ng <;> simp [h0, Nat.two_pow_pos]
  have hq0 : cond ng a0 0 < 2 ^ W := by cases ng <;> simp [h0, Nat.two_pow_pos]
  have hPd : Nat.add (cond ng 0 a0) (Nat.shiftLeft a1 W) = Nat.ofDigits (2 ^ W) [cond ng 0 a0, a1] := by
    show cond ng 0 a0 + a1 <<< W = _
    simp [Nat.ofDigits_cons, Nat.shiftLeft_eq]; ring
  have hQd : cond ng a0 0 = Nat.ofDigits (2 ^ W) [cond ng a0 0] := by simp
  have hpq : pqCoeffs W (N + 1) (Nat.add (cond ng 0 a0) (Nat.shiftLeft a1 W)) (cond ng a0 0) =
      ((cond ng 0 a0 : ℤ) - (cond ng a0 0 : ℤ)) :: (a1 : ℤ) :: List.replicate (N - 1) 0 := by
    unfold pqCoeffs
    rw [hPd, digitsN_pad (N + 1) _ (by simp <;> omega) (by simp [hp0, h1])]
    conv_lhs => rw [hQd]
    rw [digitsN_pad (N + 1) _ (by simp <;> omega) (by simp [hq0])]
    simp only [List.length_cons, List.length_nil]
    rw [show N + 1 - (0 + 1 + 1) = N - 1 by omega, show N + 1 - (0 + 1) = (N - 1) + 1 by omega]
    simp only [List.cons_append, List.nil_append, List.replicate_succ, List.zipWith_cons_cons]
    rw [zipWith_sub_zeros]
    cases ng <;> simp
  show evalZ _ t / 2 ^ S = ((if ng then -(a0 : ℝ) else a0) + a1 * t) / 2 ^ S
  rw [hpq]
  congr 1
  simp only [evalZ, List.map_cons, horner_cons, List.map_replicate, Int.cast_zero]
  rw [horner_replicate_zero]
  cases ng <;> simp <;> ring

theorem upowL_getD (c : Ctx) (U : TM) : ∀ (n : ℕ) (P : TM) (k : ℕ), k < n →
    (upowL c U n P).getD k zeroTM = (fun A => mul c A U)^[k] P
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, P, 0, _ => rfl
  | n + 1, P, k + 1, hk => by
    show (upowL c U n (mul c P U)).getD k zeroTM = _
    rw [upowL_getD c U n _ k (by omega), Function.iterate_succ_apply]

theorem upowL_length (c : Ctx) (U : TM) : ∀ (n : ℕ) (P : TM), (upowL c U n P).length = n
  | 0, _ => rfl
  | n + 1, P => by show (P :: upowL c U n (mul c P U)).length = _; simp [upowL_length c U n]

theorem iter_ok (c : Ctx) (U : TM) : ∀ (k : ℕ) (A : TM), ((fun A => mul c A U)^[k] A).ok = true → A.ok = true
  | 0, A, h => h
  | k + 1, A, h => by
    rw [Function.iterate_succ_apply'] at h
    exact iter_ok c U k A (mul_ok h).1

theorem iter_encl (hg : Good N S B W) {U : TM} {u : ℝ → ℝ} (hU : Encl (mkCtx N S B W) U u) :
    ∀ (k : ℕ) (A : TM) (f : ℝ → ℝ), Encl (mkCtx N S B W) A f →
      ((fun A => mul (mkCtx N S B W) A U)^[k] A).ok = true →
      Encl (mkCtx N S B W) ((fun A => mul (mkCtx N S B W) A U)^[k] A) (fun t => f t * u t ^ k)
  | 0, A, f, hA, _ => by simpa using hA
  | k + 1, A, f, hA, h => by
    rw [Function.iterate_succ_apply'] at h ⊢
    have h1 := iter_encl hg hU k A f hA (mul_ok h).1
    exact (mul_sound hg h1 hU h).congr (fun t _ => by ring)

/-- the `ok` powers of `upow` enclose `u^k` -/
theorem upow_encl (hg : Good N S B W) {U : TM} {u : ℝ → ℝ} (hU : Encl (mkCtx N S B W) U u) (n k : ℕ) (hk : k ≤ n)
    (hok : ((upow (mkCtx N S B W) U n).getD k zeroTM).ok = true) :
    Encl (mkCtx N S B W) ((upow (mkCtx N S B W) U n).getD k zeroTM) (fun t => u t ^ k) := by
  unfold upow at hok ⊢
  rw [upowL_getD _ _ _ _ k (by omega)] at hok ⊢
  have h1 := iter_ok _ U k _ hok
  have h0 := constTM_sound hg false (mkCtx N S B W).twoS 0 1 (by simp) h1
  exact (iter_encl hg hU k _ _ h0 hok).congr (fun t _ => by ring)

end ThomsonCompact.Floor.B
