import ThomsonCompact.Fixed.SoundG

/-!
# Soundness of the N link (workstream F4)

`colLinkOk_sound`: if the N link of output `k` passes, the stored column `N_k(B)` is, at every retained row
`i < n`, the radix value of the **canonical polynomial**

  `ncomp L b r c mult (rtag i) = Σ_{u ∈ κ_{b,r}} Σ_{v ∈ κ_{b,c}} mult · zsum(b, u, v, rtag i) · κ_u κ_v`

(`zsum`: the raw-tensor coefficients of block `b` at the tag code), given that `rtag` is injective on `[0, n)`
and no `rtag i` is flagged non-retained. `ncomp_l1`: its ℓ1 bound from the κ header bounds.

Proof: the accumulation is a fold of single contributions (`accList`); every contribution lands in the entries
with its code (`vsum`) or is flagged non-retained; `colOk` pairs the stored entries with the accumulators.
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-! ## Lists -/

theorem sum_flatMap_map {α β : Type*} (f : α → List β) (g : β → ℤ) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum
  | [] => by simp
  | x :: l => by simp [List.flatMap_cons, sum_flatMap_map f g l]

/-! ## Accumulators -/

abbrev Acc := List (Nat × Nat × Nat)

/-- Value of an accumulator entry `(code, p, q)`. -/
def ival3 (a : Nat × Nat × Nat) : ℤ := (a.2.1 : ℤ) - a.2.2

/-- Sum of the values of all entries with code `c`. -/
def vsum (acc : Acc) (c : Nat) : ℤ := (acc.map fun a => if a.1 = c then ival3 a else 0).sum

theorem vsum_cons (a : Nat × Nat × Nat) (acc : Acc) (c : Nat) :
    vsum (a :: acc) c = (if a.1 = c then ival3 a else 0) + vsum acc c := by
  simp [vsum]

theorem accAdd_nil (c : Nat) (σ : Bool) (m : Nat) : accAdd c σ m [] = none := rfl

theorem accAdd_cons (c : Nat) (σ : Bool) (m : Nat) (e : Nat × Nat × Nat) (es : Acc) :
    accAdd c σ m (e :: es) = if e.1 = c then
      some (Bool.rec (motive := fun _ => Nat × Nat × Nat) (e.1, Nat.add e.2.1 m, e.2.2) (e.1, e.2.1, Nat.add e.2.2 m) σ
        :: es)
      else (accAdd c σ m es).map (e :: ·) := by
  show Bool.rec (motive := fun _ => Option Acc)
    (Option.rec (motive := fun _ => Option Acc) none (fun l => some (e :: l)) (accAdd c σ m es)) _
    (Nat.beq e.1 c) = _
  rw [beq_cases]
  split_ifs
  · rfl
  · cases accAdd c σ m es <;> rfl

theorem ival3_upd (σ : Bool) (m : Nat) (e : Nat × Nat × Nat) :
    ival3 (Bool.rec (motive := fun _ => Nat × Nat × Nat) (e.1, Nat.add e.2.1 m, e.2.2) (e.1, e.2.1, Nat.add e.2.2 m) σ)
      = ival3 e + sv (σ, m) := by
  cases σ <;> simp [ival3, sv, nat_add] <;> ring

theorem accAdd_spec (c : Nat) (σ : Bool) (m : Nat) : ∀ (acc acc' : Acc), accAdd c σ m acc = some acc' →
    acc'.map (·.1) = acc.map (·.1) ∧ c ∈ acc.map (·.1) ∧
      ∀ c', vsum acc' c' = vsum acc c' + if c' = c then sv (σ, m) else 0
  | [], _, h => by rw [accAdd_nil] at h; exact absurd h (by simp)
  | e :: es, acc', h => by
    rw [accAdd_cons] at h
    by_cases he : e.1 = c
    · rw [if_pos he] at h
      cases h
      refine ⟨by cases σ <;> rfl, by simp [he], fun c' => ?_⟩
      have hc : (Bool.rec (motive := fun _ => Nat × Nat × Nat) (e.1, Nat.add e.2.1 m, e.2.2)
          (e.1, e.2.1, Nat.add e.2.2 m) σ).1 = e.1 := by cases σ <;> rfl
      rw [vsum_cons, vsum_cons, hc, ival3_upd]
      by_cases h' : e.1 = c'
      · rw [if_pos h', if_pos h', if_pos (h'.symm.trans he)]; ring
      · rw [if_neg h', if_neg h', if_neg (fun hh => h' (he.trans hh.symm))]; ring
    · rw [if_neg he] at h
      cases hr : accAdd c σ m es with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some l =>
        rw [hr] at h
        cases h
        obtain ⟨i1, i2, i3⟩ := accAdd_spec c σ m es l hr
        refine ⟨by simp [i1], by simp [i2], fun c' => ?_⟩
        rw [vsum_cons, vsum_cons, i3]
        ring

theorem accAdd_none (c : Nat) (σ : Bool) (m : Nat) : ∀ acc : Acc, accAdd c σ m acc = none → c ∉ acc.map (·.1)
  | [], _ => by simp
  | e :: es, h => by
    rw [accAdd_cons] at h
    by_cases he : e.1 = c
    · rw [if_pos he] at h; exact absurd h (by simp)
    · rw [if_neg he] at h
      cases hr : accAdd c σ m es with
      | none =>
        have := accAdd_none c σ m es hr
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨fun hh => he hh.symm, this⟩
      | some l => rw [hr] at h; exact absurd h (by simp)

/-- One contribution: added to its code, or skipped if flagged non-retained. -/
noncomputable def accStep (D : Nat) (x : Nat × Bool × Nat) (acc : Acc) : Option Acc :=
  Option.rec (motive := fun _ => Option Acc) (Bool.rec (motive := fun _ => Option Acc) none (some acc)
    (notRetained D x.1)) some (accAdd x.1 x.2.1 x.2.2 acc)

/-- A fold of contributions. -/
noncomputable def accList (D : Nat) : List (Nat × Bool × Nat) → Acc → Option Acc
  | [], acc => some acc
  | x :: xs, acc => (accStep D x acc).bind (accList D xs)

theorem accList_append (D : Nat) : ∀ (xs ys : List (Nat × Bool × Nat)) (acc : Acc),
    accList D (xs ++ ys) acc = (accList D xs acc).bind (accList D ys)
  | [], ys, acc => rfl
  | x :: xs, ys, acc => by
    simp only [List.cons_append, accList]
    cases accStep D x acc with
    | none => rfl
    | some a => exact accList_append D xs ys a

theorem accTerms_eq (D mult : Nat) (s1 : Bool) (m1 : Nat) : ∀ (ts : List (Nat × Bool × Nat)) (acc : Acc),
    accTerms D mult s1 m1 ts acc =
      accList D (ts.map fun t => (t.1, xor s1 t.2.1, Nat.mul (Nat.mul mult t.2.2) m1)) acc
  | [], acc => rfl
  | t :: ts, acc => by
    show Option.rec (motive := fun _ => Option Acc)
      (Bool.rec (motive := fun _ => Option Acc) none (accTerms D mult s1 m1 ts acc) (notRetained D t.1))
      (fun acc' => accTerms D mult s1 m1 ts acc') (accAdd t.1 (xor s1 t.2.1) (Nat.mul (Nat.mul mult t.2.2) m1) acc) =
      (accStep D (t.1, xor s1 t.2.1, Nat.mul (Nat.mul mult t.2.2) m1) acc).bind (accList D _)
    unfold accStep
    cases accAdd t.1 (xor s1 t.2.1) (Nat.mul (Nat.mul mult t.2.2) m1) acc with
    | none =>
      cases notRetained D t.1
      · rfl
      · exact accTerms_eq D mult s1 m1 ts acc
    | some a => exact accTerms_eq D mult s1 m1 ts a

/-- The contributions of the raw pairs `(u, v)` of the κ columns `kr × kcl`. -/
noncomputable def contribs (L : LTab) (mult b : Nat) (kr kcl : List (Nat × Bool × Nat)) : List (Nat × Bool × Nat) :=
  kr.flatMap fun u => kcl.flatMap fun v => (zterms L.rt L.zt b u.1 v.1).map fun t =>
    (t.1, xor (xor u.2.1 v.2.1) t.2.1, Nat.mul (Nat.mul mult t.2.2) (Nat.mul u.2.2 v.2.2))

theorem accV_eq (L : LTab) (mult b u : Nat) (s1 : Bool) (m1 : Nat) : ∀ (kcl : List (Nat × Bool × Nat)) (acc : Acc),
    accV L mult b u s1 m1 kcl acc = accList L.D (kcl.flatMap fun v => (zterms L.rt L.zt b u v.1).map fun t =>
      (t.1, xor (xor s1 v.2.1) t.2.1, Nat.mul (Nat.mul mult t.2.2) (Nat.mul m1 v.2.2))) acc
  | [], acc => rfl
  | v :: kcl, acc => by
    show Option.rec (motive := fun _ => Option Acc) none (fun a => accV L mult b u s1 m1 kcl a)
      (accTerms L.D mult (xor s1 v.2.1) (Nat.mul m1 v.2.2) (zterms L.rt L.zt b u v.1) acc) = _
    rw [List.flatMap_cons, accList_append, accTerms_eq]
    cases accList L.D _ acc with
    | none => rfl
    | some a => exact accV_eq L mult b u s1 m1 kcl a

theorem accU_eq (L : LTab) (mult b : Nat) (kcl : List (Nat × Bool × Nat)) : ∀ (kr : List (Nat × Bool × Nat)) (acc : Acc),
    accU L mult b kcl kr acc = accList L.D (contribs L mult b kr kcl) acc
  | [], acc => rfl
  | u :: kr, acc => by
    show Option.rec (motive := fun _ => Option Acc) none (fun a => accU L mult b kcl kr a) (accV L mult b u.1 u.2.1 u.2.2 kcl acc) = _
    rw [contribs, List.flatMap_cons, accList_append, accV_eq]
    cases accList L.D _ acc with
    | none => rfl
    | some a => exact accU_eq L mult b kcl kr a

theorem accList_spec (D : Nat) : ∀ (xs : List (Nat × Bool × Nat)) (acc acc' : Acc), accList D xs acc = some acc' →
    acc'.map (·.1) = acc.map (·.1) ∧
      (∀ c, c ∈ acc.map (·.1) → vsum acc' c = vsum acc c + (xs.map fun x => if x.1 = c then sv x.2 else 0).sum) ∧
      ∀ x ∈ xs, x.1 ∉ acc.map (·.1) → notRetained D x.1 = true
  | [], acc, acc', h => by
    cases h
    exact ⟨rfl, fun c _ => by simp, fun x hx => by simp at hx⟩
  | x :: xs, acc, acc', h => by
    simp only [accList] at h
    unfold accStep at h
    cases ha : accAdd x.1 x.2.1 x.2.2 acc with
    | none =>
      rw [ha] at h
      have hn := accAdd_none _ _ _ acc ha
      cases hr : notRetained D x.1
      · rw [hr] at h; exact absurd h (by simp)
      · rw [hr] at h
        obtain ⟨i1, i2, i3⟩ := accList_spec D xs acc acc' h
        refine ⟨i1, fun c hc => ?_, fun y hy hy' => ?_⟩
        · rw [i2 c hc, List.map_cons, List.sum_cons, if_neg (fun he => hn (by rw [he]; exact hc))]
          ring
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hr
          · exact i3 y hy hy'
    | some a =>
      rw [ha] at h
      obtain ⟨a1, a2, a3⟩ := accAdd_spec _ _ _ acc a ha
      obtain ⟨i1, i2, i3⟩ := accList_spec D xs a acc' h
      refine ⟨i1.trans a1, fun c hc => ?_, fun y hy hy' => ?_⟩
      · rw [i2 c (a1 ▸ hc), a3 c, List.map_cons, List.sum_cons]
        by_cases hxc : x.1 = c
        · rw [if_pos hxc.symm, if_pos hxc]; ring
        · rw [if_neg (fun h => hxc h.symm), if_neg hxc]; ring
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd a2 hy'
        · exact i3 y hy (a1 ▸ hy')

theorem colOk_spec : ∀ (l : List (Nat × Bool × Nat)) (acc : Acc), colOk l acc = true →
    List.Forall₂ (fun e a => sv e.2 = ival3 a) l acc
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp [colOk] at h
  | _ :: _, [], h => by simp [colOk] at h
  | e :: es, a :: as, h => by
    have h' : (Bool.rec (motive := fun _ => Bool) (Nat.beq a.2.1 (Nat.add a.2.2 e.2.2))
        (Nat.beq a.2.2 (Nat.add a.2.1 e.2.2)) e.2.1 && colOk es as) = true := h
    rw [Bool.and_eq_true] at h'
    refine List.Forall₂.cons ?_ (colOk_spec es as h'.2)
    have h1 := h'.1
    cases hs : e.2.1
    · rw [hs] at h1
      have := Nat.eq_of_beq_eq_true h1
      simp only [sv, hs, Bool.false_eq_true, ↓reduceIte, ival3, this, nat_add]
      push_cast; ring
    · rw [hs] at h1
      have := Nat.eq_of_beq_eq_true h1
      simp only [sv, hs, ↓reduceIte, ival3, this, nat_add]
      push_cast; ring

theorem acc0_eq (L : LTab) : ∀ l : List (Nat × Bool × Nat), acc0 L l = l.map fun e => (L.rtag e.1, 0, 0)
  | [] => rfl
  | e :: es => by
    show (L.rtag e.1, 0, 0) :: acc0 L es = _
    rw [acc0_eq L es, List.map_cons]

theorem vsum_forall₂ (rtag : Nat → Nat) : ∀ (l : List (Nat × Bool × Nat)) (acc : Acc),
    List.Forall₂ (fun e a => sv e.2 = ival3 a) l acc → acc.map (·.1) = l.map (fun e => rtag e.1) → ∀ c,
      vsum acc c = (l.map fun e => if rtag e.1 = c then sv e.2 else 0).sum
  | [], [], _, _, c => by simp [vsum]
  | e :: es, a :: as, List.Forall₂.cons h1 h2, hc, c => by
    simp only [List.map_cons, List.cons.injEq] at hc
    rw [vsum_cons, vsum_forall₂ rtag es as h2 hc.2 c, List.map_cons, List.sum_cons, hc.1, h1]

theorem vsum_zero (rtag : Nat → Nat) : ∀ (l : List (Nat × Bool × Nat)) (c : Nat),
    vsum (l.map fun e => (rtag e.1, 0, 0)) c = 0
  | [], c => by simp [vsum]
  | e :: l, c => by
    rw [List.map_cons, vsum_cons, vsum_zero rtag l c]
    simp [ival3]

/-! ## The column theorem -/

/-- Output fields. -/
def oBlk (L : LTab) (k : Nat) : Nat := Nat.land (L.oinfo k) 255
def oRow (L : LTab) (k : Nat) : Nat := Nat.land (Nat.shiftRight (L.oinfo k) 8) 255
def oCol (L : LTab) (k : Nat) : Nat := Nat.land (Nat.shiftRight (L.oinfo k) 16) 255
def oMult (L : LTab) (k : Nat) : Nat := Nat.land (Nat.shiftRight (L.oinfo k) 24) 255

/-- Decoded κ column `(b, r)` (radix values) and its coefficient lists. -/
noncomputable def kapV (R : Nat) (L : LTab) (b r : Nat) : List (Nat × Bool × Nat) := decPolyVec R (L.kc b r) (L.kn b r) 0
def kapC (L : LTab) (b r : Nat) : List (Nat × List ℤ) := decPolyVecC (L.kc b r) (L.kn b r) 0

theorem colLinkOk_contribs (T : Tab) (L : LTab) (k : Nat) (h : colLinkOk T L k = true)
    (hrtag : ∀ i j, i < T.n → j < T.n → L.rtag i = L.rtag j → i = j)
    (hnr : ∀ i, i < T.n → notRetained L.D (L.rtag i) = false) (hidx : ∀ e ∈ ncol T k, e.1 < T.n) :
    ∀ i, i < T.n → lk (ncol T k) i = ((contribs L (oMult L k) (oBlk L k) (kapV T.R L (oBlk L k) (oRow L k))
      (kapV T.R L (oBlk L k) (oCol L k))).map fun x => if x.1 = L.rtag i then sv x.2 else 0).sum := by
  intro i hi
  have h' : Option.rec (motive := fun _ => Bool) false (fun a => colOk (ncolT T k) a)
      (accU L (oMult L k) (oBlk L k) (kapV T.R L (oBlk L k) (oCol L k)) (kapV T.R L (oBlk L k) (oRow L k))
        (acc0 L (ncolT T k))) = true := h
  rw [accU_eq] at h'
  cases hacc : accList L.D (contribs L (oMult L k) (oBlk L k) (kapV T.R L (oBlk L k) (oRow L k))
      (kapV T.R L (oBlk L k) (oCol L k))) (acc0 L (ncolT T k)) with
  | none => rw [hacc] at h'; exact absurd h' (by simp)
  | some acc =>
    rw [hacc] at h'
    have hco := colOk_spec _ _ h'
    obtain ⟨s1, s2, s3⟩ := accList_spec L.D _ _ _ hacc
    rw [acc0_eq] at s1 s2 s3
    have hcodes : acc.map (·.1) = (ncol T k).map (fun e => L.rtag e.1) := by
      rw [s1, List.map_map]; rfl
    have hv := vsum_forall₂ L.rtag (ncol T k) acc hco hcodes
    -- the stored side
    have hlk : lk (ncol T k) i = ((ncol T k).map fun e => if L.rtag e.1 = L.rtag i then sv e.2 else 0).sum := by
      unfold lk
      congr 1
      apply List.map_congr_left
      intro e he
      by_cases hei : e.1 = i
      · rw [if_pos hei, if_pos (by rw [hei])]
      · rw [if_neg hei, if_neg (fun hh => hei (hrtag _ _ (hidx e he) hi hh))]
    by_cases hin : L.rtag i ∈ ((ncol T k).map fun e => (L.rtag e.1, 0, 0)).map (·.1)
    · have := s2 (L.rtag i) hin
      rw [vsum_zero L.rtag, zero_add, hv] at this
      rw [hlk, this]
    · -- no stored row has code `rtag i`, and no contribution either
      have h0 : lk (ncol T k) i = 0 := by
        rw [hlk]
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        rw [if_neg]
        intro hh
        apply hin
        simp only [List.map_map, List.mem_map]
        exact ⟨e, he, hh⟩
      rw [h0]
      symm
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      rw [if_neg]
      intro hxi
      have := s3 x hx (hxi ▸ hin)
      rw [hxi, hnr i hi] at this
      exact Bool.false_ne_true this

/-! ## The canonical polynomial -/

/-- Raw-tensor coefficient sum of block `b` at the raw pair `(u, v)` for the tag code `c`. -/
noncomputable def zsum (L : LTab) (b u v c : Nat) : ℤ := ((zterms L.rt L.zt b u v).map fun t => if t.1 = c then sv t.2 else 0).sum

/-- **Canonical N polynomial** of output `(b, r, c, mult)` at tag code `code`. -/
noncomputable def ncomp (L : LTab) (b r c mult code : Nat) : List ℤ :=
  sumL ((kapC L b r).map fun u => sumL ((kapC L b c).map fun v =>
    scaleL ((mult : ℤ) * zsum L b u.1 v.1 code) (convL u.2 v.2)))

theorem contribs_sum (L : LTab) (mult b : Nat) (kr kcl : List (Nat × Bool × Nat)) (code : Nat) :
    ((contribs L mult b kr kcl).map fun x => if x.1 = code then sv x.2 else 0).sum =
      (kr.map fun u => (kcl.map fun v => (mult : ℤ) * zsum L b u.1 v.1 code * (sv u.2 * sv v.2)).sum).sum := by
  unfold contribs
  rw [sum_flatMap_map]
  congr 1; apply List.map_congr_left; intro u _
  rw [sum_flatMap_map]
  congr 1; apply List.map_congr_left; intro v _
  rw [List.map_map, zsum, ← List.sum_map_mul_left, ← List.sum_map_mul_right]
  congr 1; apply List.map_congr_left; intro t _
  simp only [Function.comp]
  by_cases ht : t.1 = code
  · rw [if_pos ht, if_pos ht]
    rw [show Nat.mul (Nat.mul mult t.2.2) (Nat.mul u.2.2 v.2.2) = mult * ((u.2.2 * v.2.2) * t.2.2) by
      simp only [nat_mul]; ring]
    rw [show xor (xor u.2.1 v.2.1) t.2.1 = xor (xor u.2.1 v.2.1) t.2.1 from rfl]
    have e1 : sv (xor (xor u.2.1 v.2.1) t.2.1, mult * ((u.2.2 * v.2.2) * t.2.2)) =
        (mult : ℤ) * (sv (xor u.2.1 v.2.1, u.2.2 * v.2.2) * sv t.2) := by
      cases h : xor (xor u.2.1 v.2.1) t.2.1 <;> cases h2 : xor u.2.1 v.2.1 <;> cases h3 : t.2.1 <;>
        simp_all [sv] <;> push_cast <;> ring
    rw [e1, sv_xor]
    ring
  · rw [if_neg ht, if_neg ht]; ring

theorem list_map_horner {R : ℕ} (l : List (Nat × Bool × Nat)) (lc : List (Nat × List ℤ))
    (hmap : l.map (fun e => (e.1, sv e.2)) = lc.map (fun e => (e.1, horner ((2 : ℤ) ^ R) e.2))) (F : Nat → ℤ → ℤ) :
    (l.map fun u => F u.1 (sv u.2)).sum = (lc.map fun u => F u.1 (horner ((2 : ℤ) ^ R) u.2)).sum := by
  have h := congrArg (fun m => (m.map fun p : Nat × ℤ => F p.1 p.2).sum) hmap
  simp only [List.map_map] at h
  exact h

theorem horner_ncomp (R : ℕ) (hR : 0 < R) (L : LTab) (b r c mult code : Nat) :
    horner ((2 : ℤ) ^ R) (ncomp L b r c mult code) =
      ((kapV R L b r).map fun u => ((kapV R L b c).map fun v =>
        (mult : ℤ) * zsum L b u.1 v.1 code * (sv u.2 * sv v.2)).sum).sum := by
  unfold ncomp
  rw [hornerZ_sumL, List.map_map]
  rw [list_map_horner (R := R) (kapV R L b r) (kapC L b r) (decPolyVec_sv R hR _ _ _)
    (fun u x => ((kapV R L b c).map fun v => (mult : ℤ) * zsum L b u v.1 code * (x * sv v.2)).sum)]
  congr 1; apply List.map_congr_left; intro u _
  simp only [Function.comp, hornerZ_sumL, List.map_map]
  rw [list_map_horner (R := R) (kapV R L b c) (kapC L b c) (decPolyVec_sv R hR _ _ _)
    (fun v y => (mult : ℤ) * zsum L b u.1 v code * (horner ((2 : ℤ) ^ R) u.2 * y))]
  congr 1; apply List.map_congr_left; intro v _
  simp only [Function.comp, hornerZ_scaleL, hornerZ_convL]
  try ring

/-- **Soundness of the N link** of output `k`. -/
theorem colLinkOk_sound (T : Tab) (L : LTab) (k : Nat) (hR : 0 < T.R) (h : colLinkOk T L k = true)
    (hrtag : ∀ i j, i < T.n → j < T.n → L.rtag i = L.rtag j → i = j)
    (hnr : ∀ i, i < T.n → notRetained L.D (L.rtag i) = false) (hidx : ∀ e ∈ ncol T k, e.1 < T.n) :
    ∀ i, i < T.n → lk (ncol T k) i =
      horner ((2 : ℤ) ^ T.R) (ncomp L (oBlk L k) (oRow L k) (oCol L k) (oMult L k) (L.rtag i)) := by
  intro i hi
  rw [colLinkOk_contribs T L k h hrtag hnr hidx i hi, contribs_sum, horner_ncomp T.R hR]

/-! ## The ℓ1 bound -/

/-- `zterms` in explicit form. -/
theorem zterms_eq (rt : Nat → Nat → Nat) (zt : Nat → Nat → Nat → Nat) (b u v : Nat) :
    zterms rt zt b u v =
      if b = 3 then
        (if Nat.land (Nat.shiftRight (rt b u) 15) (Nat.shiftRight (rt b v) 15) = 1 then
          [(Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 4, false, 4),
           (Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 34, true, 24),
           (Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 64, false, 36)]
        else if Nat.lor (Nat.shiftRight (rt b u) 15) (Nat.shiftRight (rt b v) 15) = 1 then
          [(Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 3, false, 12),
           (Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 33, true, 54),
           (Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 1024, false, 162)]
        else
          [(Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 2, false, 36),
           (Nat.add (Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767)) 32, true, 108)])
      else if b = 2 then [(Nat.add (Nat.land (rt b u) 32767) (Nat.land (rt b v) 32767), false, 1)]
      else
        Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
          (fun _ ih x => (Nat.land x 32767, Nat.beq (Nat.land (Nat.shiftRight x 15) 1) 1,
              Nat.land (Nat.shiftRight x 16) 65535) :: ih (Nat.shiftRight x 32))
          (Nat.land (zt b u v) 255) (Nat.shiftRight (zt b u v) 8) := by
  unfold zterms
  simp only [beq_cases]

theorem zdec_bound : ∀ (n x : Nat),
    ((Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
      (fun _ ih x => (Nat.land x 32767, Nat.beq (Nat.land (Nat.shiftRight x 15) 1) 1,
          Nat.land (Nat.shiftRight x 16) 65535) :: ih (Nat.shiftRight x 32)) n x).map fun t => t.2.2).sum ≤ n * 65535
  | 0, _ => by simp
  | n + 1, x => by
    have ih := zdec_bound n (Nat.shiftRight x 32)
    have h1 : Nat.land (Nat.shiftRight x 16) 65535 ≤ 65535 := Nat.and_le_right
    simp only [List.map_cons, List.sum_cons]
    calc _ ≤ 65535 + n * 65535 := Nat.add_le_add h1 ih
      _ = (n + 1) * 65535 := by ring

/-- `Σ |z|` of the terms of one raw pair. -/
theorem zterms_abs (rt : Nat → Nat → Nat) (zt : Nat → Nat → Nat → Nat) (b u v : Nat) :
    ((zterms rt zt b u v).map fun t => t.2.2).sum ≤ 255 * 65535 := by
  rw [zterms_eq]
  split_ifs
  · simp
  · simp
  · simp
  · simp
  · exact (zdec_bound _ _).trans (Nat.mul_le_mul_right _ Nat.and_le_right)

theorem natAbs_zsum_le (L : LTab) (b u v code : Nat) : (zsum L b u v code).natAbs ≤ 255 * 65535 := by
  refine le_trans ?_ (zterms_abs L.rt L.zt b u v)
  unfold zsum
  generalize zterms L.rt L.zt b u v = ts
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add ?_ ih)
    split_ifs
    · simp [sv]; split_ifs <;> simp
    · simp

theorem l1_sumL_map {α : Type*} (f : α → List ℤ) (B : ℕ) : ∀ l : List α, (∀ x ∈ l, l1 (f x) ≤ B) →
    l1 (sumL (l.map f)) ≤ l.length * B
  | [], _ => by simp [sumL]
  | x :: l, h => by
    simp only [List.map_cons, sumL, List.length_cons]
    refine (l1_addL _ _).trans ?_
    have h1 := h x (by simp)
    have h2 := l1_sumL_map f B l (fun y hy => h y (by simp [hy]))
    nlinarith

/-- **ℓ1 bound of the canonical polynomial** from the κ header bounds. -/
theorem ncomp_l1 (L : LTab) (b r c mult code KB : Nat) (hm : mult ≤ 255)
    (hr : ∀ u ∈ kapC L b r, l1 u.2 ≤ KB) (hc : ∀ v ∈ kapC L b c, l1 v.2 ≤ KB) :
    l1 (ncomp L b r c mult code) ≤ (kapC L b r).length * ((kapC L b c).length * (255 * (255 * 65535) * (KB * KB))) := by
  unfold ncomp
  apply l1_sumL_map
  intro u hu
  apply l1_sumL_map
  intro v hv
  rw [l1_scaleL, Int.natAbs_mul, Int.natAbs_natCast]
  have e1 := natAbs_zsum_le L b u.1 v.1 code
  have e2 := l1_convL u.2 v.2
  have e3 := hr u hu
  have e4 := hc v hv
  calc mult * (zsum L b u.1 v.1 code).natAbs * l1 (convL u.2 v.2)
      ≤ 255 * (255 * 65535) * (l1 u.2 * l1 v.2) := by gcongr
    _ ≤ 255 * (255 * 65535) * (KB * KB) := by gcongr

#print axioms colLinkOk_sound
#print axioms ncomp_l1

end ThomsonCompact.Fixed
