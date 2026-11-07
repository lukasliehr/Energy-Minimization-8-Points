import ThomsonCompact.CoeffMap.Deg.PolySound
import ThomsonCompact.CoeffMap.Deg.Check
import ThomsonCompact.Packed.Digits

/-!
# Dense accumulators of the one-time checks (F2f)

The one-time checks read the coefficients of the class polynomials at the retained coordinates from dense
accumulators `(Σ⁺ c 2^(W r), Σ⁻ |c| 2^(W r), Σ |c|)` built by the fused functions `accSM`, `parAcc`, `evenAcc`,
`rscAcc`, `clsAcc` (`CoeffMap.Deg.Poly`, `Codec`). Here:

* `accSM_spec`, `parAcc_spec`, `evenAcc_spec`, `rscAcc_eq`, `clsAcc_eq`: every fused accumulator is the canonical
  accumulator `denseAcc` of the corresponding sparse polynomial (`spScale`, `spShift`, `par3`, `even3`, `rscZ`,
  `clsPoly`), exactly (triples are equal);
* `slot_denseAcc`: without overflow (`Σ |c| < 2^W`), slot `r < nc` of the positive minus the negative accumulator is
  the sum of the coefficients of the terms with `ridx t = r`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open scoped BigOperators

/-! ## Triples -/

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
theorem shr_eq (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

/-- Componentwise sum of accumulator triples. -/
def add3 (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

theorem add3_zero (a : ℕ × ℕ × ℕ) : add3 a (0, 0, 0) = a := by simp [add3]
theorem zero_add3 (a : ℕ × ℕ × ℕ) : add3 (0, 0, 0) a = a := by simp [add3]
theorem add3_assoc (a b c : ℕ × ℕ × ℕ) : add3 (add3 a b) c = add3 a (add3 b c) := by
  simp only [add3, Prod.mk.injEq]; omega
theorem add3_comm (a b : ℕ × ℕ × ℕ) : add3 a b = add3 b a := by
  simp only [add3, Prod.mk.injEq]; omega

/-- Contribution of one term: index `r`, sign `s`, magnitude `v`. -/
def ctr (nc W r : ℕ) (s : Bool) (v : ℕ) : ℕ × ℕ × ℕ :=
  if r < nc then (if s = true then (0, v * 2 ^ (W * r), v) else (v * 2 ^ (W * r), 0, v)) else (0, 0, 0)

theorem ctr_zero (nc W r : ℕ) (s : Bool) : ctr nc W r s 0 = (0, 0, 0) := by
  unfold ctr; split_ifs <;> simp

section Acc

variable (ridx : T3 → ℕ) (nc W : ℕ)

theorem denseAcc_nil : denseAcc ridx nc W [] = (0, 0, 0) := rfl

theorem denseAcc_cons (e : T3 × ℤ) (L : SP) :
    denseAcc ridx nc W (e :: L) = add3 (ctr nc W (ridx e.1) (decide (e.2 < 0)) e.2.natAbs) (denseAcc ridx nc W L) := by
  show (fun r => cond (Nat.blt r nc)
      (cond (decide (e.2 < 0)) ((denseAcc ridx nc W L).1,
        Nat.add (denseAcc ridx nc W L).2.1 (Nat.shiftLeft e.2.natAbs (Nat.mul W r)),
        Nat.add (denseAcc ridx nc W L).2.2 e.2.natAbs)
        (Nat.add (denseAcc ridx nc W L).1 (Nat.shiftLeft e.2.natAbs (Nat.mul W r)), (denseAcc ridx nc W L).2.1,
          Nat.add (denseAcc ridx nc W L).2.2 e.2.natAbs)) (denseAcc ridx nc W L)) (ridx e.1) = _
  dsimp only
  unfold ctr add3
  by_cases hr : ridx e.1 < nc
  · rw [show Nat.blt (ridx e.1) nc = true from Nat.blt_eq.mpr hr, cond_true, if_pos hr]
    cases hs : decide (e.2 < 0)
    · simp only [cond_false, Bool.false_eq_true, if_false, shl_eq, Nat.add_eq, Nat.mul_eq,
        Prod.mk.injEq]
      omega
    · simp only [cond_true, if_true, shl_eq, Nat.add_eq, Nat.mul_eq, Prod.mk.injEq]
      omega
  · rw [show Nat.blt (ridx e.1) nc = false from Bool.eq_false_iff.mpr (fun h => hr (Nat.blt_eq.mp h)), cond_false,
      if_neg hr]
    simp

theorem denseAcc_append : ∀ L M : SP,
    denseAcc ridx nc W (L ++ M) = add3 (denseAcc ridx nc W L) (denseAcc ridx nc W M)
  | [], M => by rw [List.nil_append, denseAcc_nil, zero_add3]
  | e :: L, M => by
    rw [List.cons_append, denseAcc_cons, denseAcc_cons, denseAcc_append L M, add3_assoc]

theorem denseAcc_flatMap {α : Type} (g : α → SP) : ∀ (L : List α) (acc : ℕ × ℕ × ℕ),
    add3 acc (denseAcc ridx nc W (L.flatMap g)) =
      L.foldl (fun a x => add3 a (denseAcc ridx nc W (g x))) acc
  | [], acc => by simp [denseAcc_nil, add3_zero]
  | x :: L, acc => by
    rw [List.flatMap_cons, denseAcc_append, ← add3_assoc, List.foldl_cons, denseAcc_flatMap g L]

/-- `accSM` from any initial accumulator. -/
theorem accSM_cons (neg : Bool) (c : ℕ) (m : T3) (f : T3 × Bool × ℕ) (Lsm : List (T3 × Bool × ℕ))
    (acc : ℕ × ℕ × ℕ) :
    accSM ridx nc W neg c m (f :: Lsm) acc =
      accSM ridx nc W neg c m Lsm (add3 acc (ctr nc W (ridx (tadd f.1 m)) (xor neg f.2.1) (c * f.2.2))) := by
  show accSM ridx nc W neg c m Lsm ((fun r v => cond (Nat.blt r nc)
      (cond (xor neg f.2.1) (acc.1, Nat.add acc.2.1 (Nat.shiftLeft v (Nat.mul W r)), Nat.add acc.2.2 v)
        (Nat.add acc.1 (Nat.shiftLeft v (Nat.mul W r)), acc.2.1, Nat.add acc.2.2 v)) acc)
      (ridx (tadd f.1 m)) (Nat.mul c f.2.2)) = _
  congr 1
  dsimp only
  unfold ctr add3
  by_cases hr : ridx (tadd f.1 m) < nc
  · rw [show Nat.blt (ridx (tadd f.1 m)) nc = true from Nat.blt_eq.mpr hr, cond_true, if_pos hr]
    cases hs : xor neg f.2.1
    · simp only [cond_false, Bool.false_eq_true, if_false, shl_eq, Nat.add_eq, Nat.mul_eq, Prod.mk.injEq]
      simp
    · simp only [cond_true, if_true, shl_eq, Nat.add_eq, Nat.mul_eq, Prod.mk.injEq]
      simp
  · rw [show Nat.blt (ridx (tadd f.1 m)) nc = false from Bool.eq_false_iff.mpr (fun h => hr (Nat.blt_eq.mp h)),
      cond_false, if_neg hr]
    simp

/-- Sign-magnitude form of a signed term list (sign free for zero terms). -/
def SMrep (L : SP) (Lsm : List (T3 × Bool × ℕ)) : Prop :=
  List.Forall₂ (fun e f => e.1 = f.1 ∧ e.2.natAbs = f.2.2 ∧ (e.2 ≠ 0 → decide (e.2 < 0) = f.2.1)) L Lsm

theorem smOf_rep (L : SP) : SMrep L (smOf L) := by
  unfold SMrep smOf
  induction L with
  | nil => exact List.Forall₂.nil
  | cons e L ih => exact List.Forall₂.cons ⟨rfl, rfl, fun _ => rfl⟩ ih

/-- `±1` -/
def sgnZ (neg : Bool) : ℤ := if neg = true then -1 else 1

theorem ctr_match (neg : Bool) (c : ℕ) (r : ℕ) (z : ℤ) (s : Bool) (v : ℕ) (hv : z.natAbs = v)
    (hs : z ≠ 0 → decide (z < 0) = s) :
    ctr nc W r (xor neg s) (c * v) = ctr nc W r (decide (sgnZ neg * c * z < 0)) (sgnZ neg * c * z).natAbs := by
  by_cases hc : c = 0
  · subst hc; simp [ctr_zero]
  by_cases hz : z = 0
  · subst hz; subst hv; simp [ctr_zero]
  have habs : (sgnZ neg * c * z).natAbs = c * v := by
    rw [Int.natAbs_mul, Int.natAbs_mul, hv]
    unfold sgnZ; split_ifs <;> simp
  have hsign : decide (sgnZ neg * c * z < 0) = xor neg s := by
    rw [← hs hz]
    have hc' : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
    rcases lt_or_gt_of_ne hz with h | h <;> cases neg
    · rw [show sgnZ false = 1 from rfl, decide_eq_true (by nlinarith : (1 : ℤ) * c * z < 0), decide_eq_true h]; rfl
    · rw [show sgnZ true = -1 from rfl, decide_eq_false (by nlinarith : ¬ ((-1 : ℤ) * c * z < 0)),
        decide_eq_true h]; rfl
    · rw [show sgnZ false = 1 from rfl, decide_eq_false (by nlinarith : ¬ ((1 : ℤ) * c * z < 0)),
        decide_eq_false (not_lt.mpr h.le)]; rfl
    · rw [show sgnZ true = -1 from rfl, decide_eq_true (by nlinarith : (-1 : ℤ) * c * z < 0),
        decide_eq_false (not_lt.mpr h.le)]; rfl
  rw [habs, hsign]

/-- **The fused term accumulation is the canonical one** (`±c ·` the terms shifted by `m`). -/
theorem accSM_spec (neg : Bool) (c : ℕ) (m : T3) : ∀ (L : SP) (Lsm : List (T3 × Bool × ℕ)) (acc : ℕ × ℕ × ℕ),
    SMrep L Lsm → accSM ridx nc W neg c m Lsm acc =
      add3 acc (denseAcc ridx nc W (spScale (sgnZ neg * c) (spShift m L)))
  | [], [], acc, List.Forall₂.nil => by
    show acc = _
    rw [show spScale (sgnZ neg * c) (spShift m []) = [] from rfl, denseAcc_nil, add3_zero]
  | e :: L, f :: Lsm, acc, List.Forall₂.cons hef hL => by
    rw [accSM_cons, accSM_spec neg c m L Lsm _ hL]
    show _ = add3 acc (denseAcc ridx nc W ((tadd e.1 m, sgnZ neg * c * e.2) :: spScale (sgnZ neg * c) (spShift m L)))
    rw [denseAcc_cons, ← add3_assoc]
    congr 2
    obtain ⟨h1, h2, h3⟩ := hef
    rw [h1, ctr_match nc W neg c _ e.2 f.2.1 f.2.2 h2 h3]

end Acc

/-! ## Power sums and parity coordinates -/

theorem listAt_map_smOf (P : List SP) (i : ℕ) : listAt [] (P.map smOf) i = smOf (listAt [] P i) := by
  rw [listAt_eq, listAt_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[i]? <;> rfl

theorem spScale_spScale (a b : ℤ) (L : SP) : spScale a (spScale b L) = spScale (a * b) L := by
  unfold spScale; rw [List.map_map]; apply List.map_congr_left; intro e _; simp [mul_assoc]

theorem spScale_one (L : SP) : spScale 1 L = L := by
  unfold spScale; simp

theorem spScale_append (a : ℤ) (L M : SP) : spScale a (L ++ M) = spScale a L ++ spScale a M := by
  unfold spScale; rw [List.map_append]

theorem spScale_flatMap {α : Type} (a : ℤ) (g : α → SP) (L : List α) :
    spScale a (L.flatMap g) = L.flatMap (fun x => spScale a (g x)) := by
  unfold spScale; rw [List.map_flatMap]

theorem sgnZ_xor (neg b : Bool) : sgnZ (xor neg b) = sgnZ neg * sgnZ b := by
  cases neg <;> cases b <;> simp [sgnZ]

theorem sgn_parity (l : ℕ) : sgnZ (Nat.beq (Nat.land l 1) 1) = cond (Nat.beq (Nat.land l 1) 0) (1 : ℤ) (-1) := by
  have hl : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [hl, h]; rfl
  · rw [hl, h]; rfl

/-- **`parAcc` accumulates `±c · par3`**. -/
theorem parAcc_spec (ridx : T3 → ℕ) (nc W : ℕ) (P PP : List SP) (neg : Bool) (c i j k : ℕ) (acc : ℕ × ℕ × ℕ) :
    parAcc ridx nc W (P.map smOf) (PP.map smOf) neg c i j k acc =
      add3 acc (denseAcc ridx nc W (spScale (sgnZ neg * c) (par3 P PP i j k))) := by
  unfold parAcc par3
  rw [spScale_flatMap, denseAcc_flatMap]
  congr 1
  funext a l
  rw [listAt_map_smOf, listAt_map_smOf]
  have key : ∀ (L : SP) (sh : T3), accSM ridx nc W (xor neg (Nat.beq (Nat.land l 1) 1)) (Nat.mul c (chooseI j l)) sh
      (smOf L) a = add3 a (denseAcc ridx nc W (spScale (sgnZ neg * c)
        (spScale (cond (Nat.beq (Nat.land l 1) 0) (1 : ℤ) (-1) * Int.ofNat (chooseI j l)) (spShift sh L)))) := by
    intro L sh
    rw [accSM_spec ridx nc W _ _ sh L (smOf L) a (smOf_rep L), spScale_spScale]
    congr 3
    rw [sgnZ_xor, sgn_parity]
    push_cast [Nat.mul_eq, Int.ofNat_eq_natCast]
    ring
  by_cases hkl : Nat.ble k (Nat.add i l) = true
  · simp only [hkl, cond_true]
    exact key _ _
  · simp only [Bool.not_eq_true] at hkl
    simp only [hkl, cond_false]
    exact key _ _

theorem evenAcc_spec (ridx : T3 → ℕ) (nc W : ℕ) (P PP : List SP) (neg : Bool) (c : ℕ) (t : T3) (acc : ℕ × ℕ × ℕ) :
    evenAcc ridx nc W (P.map smOf) (PP.map smOf) neg c t acc =
      add3 acc (denseAcc ridx nc W (spScale (sgnZ neg * c) (even3 P PP t))) := by
  unfold evenAcc even3
  rw [parAcc_spec, parAcc_spec, add3_assoc, spScale_append, denseAcc_append, spScale_spScale]
  congr 4
  cases neg <;> simp [sgnZ]

/-! ## Raw scalar coordinates and class polynomials -/

theorem rscAcc_eq (ridx : T3 → ℕ) (nc W : ℕ) (P PP : List SP) (f : ℕ) (det lq rq : Bool) (t : T3) :
    rscAcc ridx nc W (P.map smOf) (PP.map smOf) f det lq rq t = denseAcc ridx nc W (rscZ P PP f det lq rq t) := by
  have h0 : ∀ L : SP, accSM ridx nc W false 1 t (smOf L) (0, 0, 0) = denseAcc ridx nc W (spShift t L) := by
    intro L
    rw [accSM_spec ridx nc W false 1 t L (smOf L) _ (smOf_rep L), zero_add3]
    congr 1
    simp [sgnZ, spScale_one]
  unfold rscAcc rscZ
  rcases Nat.lt_or_ge f 5 with hf | hf
  · interval_cases f
    · simp only [show Nat.beq 0 0 = true from rfl, cond_true]; exact h0 _
    · simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, cond_true, cond_false]
      exact h0 _
    · simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
        show Nat.beq 2 2 = true from rfl, cond_true, cond_false]
      exact h0 _
    · simp only [show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
        show Nat.beq 3 2 = false from rfl, show Nat.beq 3 3 = true from rfl, cond_true, cond_false]
      rw [evenAcc_spec, zero_add3]
      congr 1
      simp [sgnZ, spScale_one]
    · simp only [show Nat.beq 4 0 = false from rfl, show Nat.beq 4 1 = false from rfl,
        show Nat.beq 4 2 = false from rfl, show Nat.beq 4 3 = false from rfl, show Nat.beq 4 4 = true from rfl,
        cond_true, cond_false]
      rw [evenAcc_spec, evenAcc_spec, zero_add3]
      unfold odd3
      rw [denseAcc_append]
      congr 2
      simp [sgnZ, spScale_one]
  · have hb : ∀ v, v ≤ 4 → Nat.beq f v = false := fun v hv =>
      Bool.eq_false_iff.mpr (fun h => by have := Nat.eq_of_beq_eq_true h; omega)
    simp only [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num),
      cond_false]
    rfl

namespace DegD

variable (L : DegD)

theorem cond_sm (b : Bool) (m : ℕ) : (cond b (-(Int.ofNat m)) (Int.ofNat m)).natAbs = m ∧
    (cond b (-(Int.ofNat m)) (Int.ofNat m) ≠ 0 → decide (cond b (-(Int.ofNat m)) (Int.ofNat m) < 0) = b) := by
  cases b
  · simp only [cond_false]
    refine ⟨rfl, fun _ => ?_⟩
    simp
  · simp only [cond_true]
    refine ⟨by simp, fun h => ?_⟩
    have hm : m ≠ 0 := fun h0 => h (by subst h0; rfl)
    have : -(Int.ofNat m) < 0 := by simp; omega
    exact decide_eq_true this

theorem momSM_rep (b x : ℕ) : SMrep (L.momTerms b x) (L.momSM b x) := by
  unfold SMrep DegD.momTerms DegD.momSM
  dsimp only
  generalize sRun (L.momC b) 64 8 _ _ = ys
  induction ys with
  | nil => exact List.Forall₂.nil
  | cons y ys ih =>
    exact List.Forall₂.cons ⟨rfl, cond_sm (Nat.beq (Nat.land (Nat.shiftRight y 16) 1) 1) (Nat.shiftRight y 17)⟩ ih

/-- **The class accumulators of the one-time checks are the canonical accumulators of the class polynomials.** -/
theorem clsAcc_eq (P PP : List SP) (W b x : ℕ) :
    L.clsAcc (P.map smOf) (PP.map smOf) W b x = denseAcc L.ridx L.nc W (L.clsPoly P PP b x) := by
  unfold DegD.clsAcc DegD.clsPoly
  cases hb : Nat.blt b L.dH
  · simp only [cond_false]
    exact rscAcc_eq _ _ _ _ _ _ _ _ _ _
  · simp only [cond_true]
    rw [accSM_spec L.ridx L.nc W false 1 (0, 0, 0) _ _ _ (L.momSM_rep b x), zero_add3]
    congr 1
    unfold spScale spShift
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (L.momTerms b x)]
    apply List.map_congr_left
    intro e _
    simp [sgnZ, tadd]

end DegD

/-! ## Slots of the accumulators -/

theorem slotAt_eq' (w x i : ℕ) : slotAt w x i = x / 2 ^ (w * i) % 2 ^ w := by
  show (x >>> (w * i)) &&& (1 <<< w - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]

/-- Positive / negative digit of the terms at index `r`. -/
def posAt (ridx : T3 → ℕ) (L : SP) (r : ℕ) : ℕ :=
  (L.map fun e => if ridx e.1 = r ∧ ¬ e.2 < 0 then e.2.natAbs else 0).sum

def negAt (ridx : T3 → ℕ) (L : SP) (r : ℕ) : ℕ :=
  (L.map fun e => if ridx e.1 = r ∧ e.2 < 0 then e.2.natAbs else 0).sum

/-- Sum of `|c|` over the retained terms. -/
def absR (ridx : T3 → ℕ) (nc : ℕ) (L : SP) : ℕ :=
  (L.map fun e => if ridx e.1 < nc then e.2.natAbs else 0).sum

section Slots

variable (ridx : T3 → ℕ) (nc W : ℕ)

theorem sum_single (a v n W : ℕ) (c : Prop) [Decidable c] :
    ∑ r ∈ Finset.range n, (if a = r ∧ c then v else 0) * 2 ^ (W * r) = if a < n ∧ c then v * 2 ^ (W * a) else 0 := by
  by_cases hc : c
  · simp only [hc, and_true]
    by_cases ha : a < n
    · rw [if_pos ha, Finset.sum_eq_single a (fun r _ hr => by rw [if_neg (Ne.symm hr), zero_mul])
        (fun h => absurd (Finset.mem_range.mpr ha) h), if_pos rfl]
    · rw [if_neg ha]
      apply Finset.sum_eq_zero
      intro r hr
      rw [if_neg (fun (h : a = r) => ha (h ▸ Finset.mem_range.mp hr)), zero_mul]
  · simp [hc]

theorem denseAcc_fields : ∀ L : SP,
    (denseAcc ridx nc W L).1 = ∑ r ∈ Finset.range nc, posAt ridx L r * 2 ^ (W * r) ∧
    (denseAcc ridx nc W L).2.1 = ∑ r ∈ Finset.range nc, negAt ridx L r * 2 ^ (W * r) ∧
    (denseAcc ridx nc W L).2.2 = absR ridx nc L
  | [] => by simp [denseAcc_nil, posAt, negAt, absR]
  | e :: L => by
    obtain ⟨h1, h2, h3⟩ := denseAcc_fields L
    have e1 : ∑ r ∈ Finset.range nc, posAt ridx (e :: L) r * 2 ^ (W * r) =
        (if ridx e.1 < nc ∧ ¬ e.2 < 0 then e.2.natAbs * 2 ^ (W * ridx e.1) else 0) +
          ∑ r ∈ Finset.range nc, posAt ridx L r * 2 ^ (W * r) := by
      simp only [posAt, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [sum_single]
    have e2 : ∑ r ∈ Finset.range nc, negAt ridx (e :: L) r * 2 ^ (W * r) =
        (if ridx e.1 < nc ∧ e.2 < 0 then e.2.natAbs * 2 ^ (W * ridx e.1) else 0) +
          ∑ r ∈ Finset.range nc, negAt ridx L r * 2 ^ (W * r) := by
      simp only [negAt, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [sum_single]
    have e3 : absR ridx nc (e :: L) = (if ridx e.1 < nc then e.2.natAbs else 0) + absR ridx nc L := by
      simp [absR]
    rw [e1, e2, e3, ← h1, ← h2, ← h3, denseAcc_cons]
    unfold add3 ctr
    by_cases hr : ridx e.1 < nc <;> by_cases hs : e.2 < 0 <;> simp [hr, hs]

theorem posAt_le (L : SP) (r : ℕ) (hr : r < nc) : posAt ridx L r ≤ absR ridx nc L := by
  unfold posAt absR
  apply List.sum_le_sum
  intro e _
  by_cases h1 : ridx e.1 = r ∧ ¬ e.2 < 0
  · rw [if_pos h1, if_pos (h1.1 ▸ hr)]
  · rw [if_neg h1]; exact Nat.zero_le _

theorem negAt_le (L : SP) (r : ℕ) (hr : r < nc) : negAt ridx L r ≤ absR ridx nc L := by
  unfold negAt absR
  apply List.sum_le_sum
  intro e _
  by_cases h1 : ridx e.1 = r ∧ e.2 < 0
  · rw [if_pos h1, if_pos (h1.1 ▸ hr)]
  · rw [if_neg h1]; exact Nat.zero_le _

theorem sum_digits_eq (p : ℕ → ℕ) : ∀ n, ∑ r ∈ Finset.range n, p r * 2 ^ (W * r) =
    Nat.ofDigits (2 ^ W) ((List.range n).map p)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_digits_eq p n, List.range_succ, List.map_append, Nat.ofDigits_append]
    simp [pow_mul, mul_comm]

theorem slot_digits (hW : 0 < W) (p : ℕ → ℕ) (n r : ℕ) (hp : ∀ r, r < n → p r < 2 ^ W) (hr : r < n) :
    slotAt W (∑ r ∈ Finset.range n, p r * 2 ^ (W * r)) r = p r := by
  have hdig : ∀ d ∈ (List.range n).map p, d < 2 ^ W := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    exact hp i (List.mem_range.mp hi)
  rw [slotAt_eq', sum_digits_eq W p n, (ofDigits_take_drop hW _ hdig r).2]
  have hlen : r < ((List.range n).map p).length := by simp [hr]
  rw [List.drop_eq_getElem_cons hlen, Nat.ofDigits_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hdig _ (List.getElem_mem hlen))]
  simp

theorem sum_map_sub_int {α : Type*} (f g : α → ℤ) : ∀ L : List α,
    (L.map f).sum - (L.map g).sum = (L.map fun x => f x - g x).sum
  | [] => by simp
  | x :: L => by simp only [List.map_cons, List.sum_cons]; rw [← sum_map_sub_int f g L]; ring

/-- **Slot extraction**: without overflow, slot `r < nc` of the positive minus the negative accumulator is the sum of
the coefficients of the terms with `ridx t = r`. -/
theorem slot_denseAcc (hW : 0 < W) (L : SP) (hL : (denseAcc ridx nc W L).2.2 < 2 ^ W) (r : ℕ) (hr : r < nc) :
    (slotAt W (denseAcc ridx nc W L).1 r : ℤ) - slotAt W (denseAcc ridx nc W L).2.1 r =
      (L.map fun e => if ridx e.1 = r then e.2 else 0).sum := by
  obtain ⟨h1, h2, h3⟩ := denseAcc_fields ridx nc W L
  rw [h3] at hL
  rw [h1, h2, slot_digits W hW _ nc r (fun r' hr' => lt_of_le_of_lt (posAt_le ridx nc L r' hr') hL) hr,
    slot_digits W hW _ nc r (fun r' hr' => lt_of_le_of_lt (negAt_le ridx nc L r' hr') hL) hr]
  unfold posAt negAt
  push_cast
  rw [List.map_map, List.map_map, sum_map_sub_int]
  congr 1
  apply List.map_congr_left
  intro e _
  by_cases he : ridx e.1 = r
  · by_cases hs : e.2 < 0
    · simp [he, hs, abs_of_neg hs]
    · simp [he, hs, abs_of_nonneg (not_lt.mp hs)]
  · simp [he]

end Slots

#print axioms DegD.clsAcc_eq
#print axioms slot_denseAcc

end ThomsonCompact.CoeffMap.Deg
