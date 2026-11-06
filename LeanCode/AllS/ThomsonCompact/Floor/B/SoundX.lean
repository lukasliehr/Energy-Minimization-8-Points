import ThomsonCompact.Floor.B.KernelX
import ThomsonCompact.Floor.B.SoundRow
import ThomsonCompact.Packed.Comp
import Blueprint.CAPContracts

/-!
# The two x-halves of a cell: soundness (F3f)

* `pieceHeight_sound`: `pieceHeight c A neg` encloses `y ↦ f((y ∓ 1)/2)` when `A` encloses `f`;
* `reexpOk_sound`: a passing re-expansion leaf gives, for every coordinate of its range and every `y`,
  `scalarEval (centres of the cell) ((y ∓ 1)/2) = scalarEval (centres of the half) y`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open Blueprint.CAP
open scoped BigOperators

/-! ## Taylor shift -/

theorem evalZ_addConst (a : ℤ) (Q : List ℤ) (y : ℝ) : evalZ (addConst a Q) y = a + evalZ Q y := by
  cases Q with
  | nil => simp [addConst, evalZ]
  | cons q Q =>
    simp only [addConst, evalZ, List.map_cons, horner_cons]
    rw [show Int.add a q = a + q from rfl]; push_cast; ring

/-- the sign `σ = ∓1` of a half -/
def sgnH (neg : Bool) : ℤ := if neg then -1 else 1

theorem cond_neg_eq (neg : Bool) (q : ℤ) : cond neg (Int.neg q) q = sgnH neg * q := by
  cases neg
  · show q = sgnH false * q
    simp [sgnH]
  · show -q = sgnH true * q
    simp [sgnH]

theorem evalZ_mulLinAux (neg : Bool) : ∀ (p : ℤ) (Q : List ℤ) (y : ℝ),
    evalZ (mulLin.mulLinAux neg p Q) y = p + (y + sgnH neg) * evalZ Q y
  | p, [], y => by simp [mulLin.mulLinAux, evalZ]
  | p, q :: Q, y => by
    have ih := evalZ_mulLinAux neg q Q y
    simp only [mulLin.mulLinAux, evalZ, List.map_cons, horner_cons] at ih ⊢
    rw [ih, show Int.add p (cond neg (Int.neg q) q) = p + cond neg (Int.neg q) q from rfl, cond_neg_eq]
    push_cast; ring

theorem evalZ_mulLin (neg : Bool) (Q : List ℤ) (y : ℝ) : evalZ (mulLin neg Q) y = (y + sgnH neg) * evalZ Q y := by
  cases Q with
  | nil => simp [mulLin, evalZ]
  | cons q Q =>
    have h := evalZ_mulLinAux neg q Q y
    simp only [mulLin, evalZ, List.map_cons, horner_cons] at h ⊢
    rw [h, cond_neg_eq]
    push_cast; ring

theorem evalZ_tshift (neg : Bool) : ∀ (cs : List ℤ) (y : ℝ), evalZ (tshift neg cs) y = evalZ cs (y + sgnH neg)
  | [], y => by simp [tshift, evalZ]
  | a :: cs, y => by
    rw [tshift, evalZ_addConst, evalZ_mulLin, evalZ_tshift neg cs y]
    simp only [evalZ, List.map_cons, horner_cons]

theorem evalZ_range_map : ∀ (n : ℕ) (f : ℕ → ℤ) (y : ℝ),
    evalZ ((List.range n).map f) y = ∑ k ∈ Finset.range n, (f k : ℝ) * y ^ k
  | 0, f, y => by simp [evalZ]
  | n + 1, f, y => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := evalZ_range_map n (f ∘ Nat.succ) y
    have e : evalZ (f 0 :: List.map (f ∘ Nat.succ) (List.range n)) y =
        (f 0 : ℝ) + y * evalZ ((List.range n).map (f ∘ Nat.succ)) y := by
      simp only [evalZ, List.map_cons, horner_cons]
    rw [e, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    apply Finset.sum_congr rfl; intro k _; ring

theorem centreInts_get (N wc cm j : ℕ) :
    (cond (smDec (slot wc cm j)).1 (Int.neg (Int.ofNat (Nat.mul (smDec (slot wc cm j)).2 (Nat.pow 2 (Nat.sub N j)))))
      (Int.ofNat (Nat.mul (smDec (slot wc cm j)).2 (Nat.pow 2 (Nat.sub N j)))) : ℤ) =
      sv (smDec (slot wc cm j)) * 2 ^ (N - j) := by
  unfold sv
  cases (smDec (slot wc cm j)).1
  · simp only [cond_false, Bool.false_eq_true, if_false, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq, Int.ofNat_eq_natCast]
    push_cast; ring
  · simp only [cond_true, if_true, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq, Int.ofNat_eq_natCast]
    show -(((smDec (slot wc cm j)).2 * 2 ^ (N - j) : ℕ) : ℤ) = _
    push_cast; ring

theorem pieceInts_get (wcP cmP k : ℕ) :
    (cond (smDec (slot wcP cmP k)).1 (Int.neg (Int.ofNat (smDec (slot wcP cmP k)).2)) (Int.ofNat (smDec (slot wcP cmP k)).2) : ℤ) =
      sv (smDec (slot wcP cmP k)) := by
  unfold sv
  cases (smDec (slot wcP cmP k)).1
  · simp only [cond_false, Bool.false_eq_true, if_false, Int.ofNat_eq_natCast]
  · simp only [cond_true, if_true, Int.ofNat_eq_natCast]
    rfl

theorem scalarEval_range {N : ℕ} (a : ℕ → ℝ) (x : ℝ) :
    scalarEval (fun k : Fin (N + 1) => a k.val) x = ∑ k ∈ Finset.range (N + 1), a k * x ^ k := by
  unfold scalarEval
  exact Fin.sum_univ_eq_sum_range (fun k => a k * x ^ k) (N + 1)

/-- **Re-expansion soundness**: the centre polynomial of coordinate `i0 + i` of the cell at `(y ∓ 1)/2` is the
half's centre polynomial at `y` (scales `2^-Sc` and `2^-(Sc+N)`). -/
theorem reexpOk_sound {N wc wcP : ℕ} {neg : Bool} {cm cmP : ℕ → ℕ} {i0 n : ℕ}
    (h : reexpOk N wc wcP neg cm cmP i0 n = true) (Sc : ℕ) (i : ℕ) (hi : i < n) (y : ℝ) :
    scalarEval (fun k : Fin (N + 1) => ((sv (smDec (slot wc (cm (i0 + i)) k)) : ℝ) / 2 ^ Sc))
        ((y + sgnH neg) / 2) =
      scalarEval (fun k : Fin (N + 1) => ((sv (smDec (slot wcP (cmP (i0 + i)) k)) : ℝ) / 2 ^ (Sc + N))) y := by
  unfold reexpOk at h
  rw [List.all_eq_true] at h
  have h1 := of_decide_eq_true (h i (List.mem_range.mpr hi))
  have h2 := congrArg (fun L => evalZ L y) h1
  simp only [evalZ_tshift] at h2
  unfold centreInts pieceInts at h2
  simp only [Nat.add_eq] at h2
  rw [evalZ_range_map, evalZ_range_map] at h2
  simp only [centreInts_get, pieceInts_get] at h2
  rw [scalarEval_range (fun k => ((sv (smDec (slot wc (cm (i0 + i)) k)) : ℝ) / 2 ^ Sc)),
    scalarEval_range (fun k => ((sv (smDec (slot wcP (cmP (i0 + i)) k)) : ℝ) / 2 ^ (Sc + N)))]
  have e2 : ∀ k ∈ Finset.range (N + 1), ((sv (smDec (slot wc (cm (i0 + i)) k)) : ℝ) / 2 ^ Sc) *
      ((y + sgnH neg) / 2) ^ k =
      (((sv (smDec (slot wc (cm (i0 + i)) k)) * 2 ^ (N - k) : ℤ) : ℝ) * (y + sgnH neg) ^ k) / 2 ^ (Sc + N) := by
    intro k hk
    have hk' : k ≤ N := by have := Finset.mem_range.mp hk; omega
    have e : (2 : ℝ) ^ (Sc + N) = 2 ^ Sc * 2 ^ (N - k) * 2 ^ k := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [e, div_pow]; push_cast; field_simp
  rw [Finset.sum_congr rfl e2, ← Finset.sum_div, h2, Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _
  ring

/-! ## Height TM of a half -/

variable {N S B W : ℕ}

theorem tmCoefsQ_eq (c : Ctx) (A : TM) (hc : c.maskK = 2 ^ c.K - 1) (hW : c.maskW = 2 ^ c.W - 1)
    (hhW : c.hW = 2 ^ (c.W - 1)) :
    tmCoefsQ c A = (decode c A.v).map fun z => (decide (z < 0), z.natAbs, c.twoS) := by
  unfold tmCoefsQ decode digitsN
  simp only [List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  have hd : Nat.land (Nat.shiftRight (Nat.land (Nat.add A.v c.hb) c.maskK) (Nat.mul c.W k)) c.maskW =
      (A.v + c.hb) % 2 ^ c.K / 2 ^ (c.W * k) % 2 ^ c.W := by
    show (((A.v + c.hb) &&& c.maskK) >>> (c.W * k)) &&& c.maskW = _
    rw [hc, hW, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  rw [hd, hhW]
  set d := (A.v + c.hb) % 2 ^ c.K / 2 ^ (c.W * k) % 2 ^ c.W
  have e1 : ((2 : ℤ) ^ (c.W - 1)) = ((2 ^ (c.W - 1) : ℕ) : ℤ) := by push_cast; ring
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · rw [e1]
    generalize 2 ^ (c.W - 1) = h
    rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
    omega
  · show d - 2 ^ (c.W - 1) + (2 ^ (c.W - 1) - d) = ((d : ℤ) - 2 ^ (c.W - 1)).natAbs
    rw [e1]
    generalize 2 ^ (c.W - 1) = h
    omega

theorem evalQ_map_int (S : ℕ) : ∀ (cs : List ℤ) (z : ℝ),
    evalQ (cs.map fun x => (decide (x < 0), x.natAbs, 2 ^ S)) z = evalZ cs z / 2 ^ S
  | [], z => by simp [evalQ, evalZ]
  | a :: cs, z => by
    rw [List.map_cons, evalQ, evalQ_map_int S cs z]
    simp only [evalZ, List.map_cons, horner_cons]
    unfold qval
    by_cases ha : a < 0
    · simp only [ha, decide_true, if_true]
      have : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast ha)]
      rw [this]; push_cast; ring
    · simp only [ha, decide_false, Bool.false_eq_true, if_false]
      have : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast not_lt.mp ha)]
      rw [this]; push_cast; ring

/-- **Height TM of a half**: `pieceHeight c A neg` encloses `y ↦ f((y + σ)/2)` (`σ = ∓1`). -/
theorem pieceHeight_sound (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f) (neg : Bool)
    (hN : 1 ≤ N) (hS : 1 ≤ S) (hU : (halfU (mkCtx N S B W) neg).ok = true)
    (hok : (pieceHeight (mkCtx N S B W) A neg).ok = true) :
    Encl (mkCtx N S B W) (pieceHeight (mkCtx N S B W) A neg) (fun y => f ((y + sgnH neg) / 2)) := by
  have hSW : S + 1 ≤ W := hg.SW
  have h0 : 2 ^ (S - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hG := tmAff_sound hg neg (Nat.pow 2 (Nat.sub S 1)) (Nat.pow 2 (Nat.sub S 1)) h0 h0 hN hU
  have hG' : Encl (mkCtx N S B W) (halfU (mkCtx N S B W) neg) (fun y => (y + sgnH neg) / 2) := by
    refine hG.congr (fun y _ => ?_)
    have e : ((2 : ℝ) ^ (S - 1)) / 2 ^ S = 1 / 2 := by
      obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
    show ((if neg then -((Nat.pow 2 (Nat.sub S 1) : ℕ) : ℝ) else ((Nat.pow 2 (Nat.sub S 1) : ℕ) : ℝ)) +
      ((Nat.pow 2 (Nat.sub S 1) : ℕ) : ℝ) * y) / 2 ^ S = _
    have e2 : ((Nat.pow 2 (Nat.sub S 1) : ℕ) : ℝ) = 2 ^ (S - 1) := by
      simp only [Nat.pow_eq, Nat.sub_eq]; push_cast; ring
    rw [e2]
    unfold sgnH
    cases neg
    · simp only [Bool.false_eq_true, if_false]; push_cast
      rw [add_div, mul_comm, mul_div_assoc, e]; ring
    · simp only [if_true]; push_cast
      rw [add_div, neg_div, mul_comm, mul_div_assoc, e]; ring
  have hok1 : (hornerQ (mkCtx N S B W) (halfU (mkCtx N S B W) neg) (tmCoefsQ (mkCtx N S B W) A)).ok = true := hok
  have hH := hornerQ_sound hg hG' _ hok1
  have hL : ∀ z, evalQ (tmCoefsQ (mkCtx N S B W) A) z = poly (mkCtx N S B W) A z := by
    intro z
    rw [tmCoefsQ_eq _ A rfl rfl rfl]
    exact evalQ_map_int S _ z
  refine widen_sound A.e (hH.congr (fun y _ => by rw [hL])) (fun y hy => ?_)
  have hy' : (y + sgnH neg) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨h1, h2⟩ := hy
    unfold sgnH; cases neg <;> simp <;> constructor <;> linarith
  have := Encl.export hg hA _ hy'
  simpa [err] using this

end ThomsonCompact.Floor.B
