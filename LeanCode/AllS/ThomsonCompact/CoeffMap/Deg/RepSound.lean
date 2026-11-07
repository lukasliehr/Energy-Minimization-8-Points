import ThomsonCompact.CoeffMap.Deg.CheckSound

/-!
# Representation: the pieces of a block sum to the raw-tensor contraction (F2f)

For a block `b` whose one-time checks pass (tags, classes, groups, coefficient lists) and any owner partition
(`partsOk`), at every retained coordinate `r` and for every symmetric `P` on `[0, n)²` (`n = rdim b`):

  `Σ_{g < nGrp b} Σ_{h < np b} pieceF sd P b g (plo h) (plo (h+1)) (eTab (32 b + g))[r] = Σ_{u,v < n} Cc u v · P u v`

with `Cc u v = rawIntegerLookup (clsPoly b (pairKey b (min u v) (max u v))) (rtag r) / bden b` (`rep_sum`). Steps:
`eRow_sum` (the coefficient list represents the class coefficients), `parts_sum` (owner parts), `grp_sum`, `cls_sum`
(classes partition the pairs; every pair carries its class key), `sym_sum` (symmetric double sum).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open scoped BigOperators

/-! ## Owner parts -/

theorem count_parts (plo : ℕ → ℕ) (x : ℕ) : ∀ K, (∀ h, h < K → plo h ≤ plo (h + 1)) →
    ∑ h ∈ Finset.range K, (if plo h ≤ x ∧ x < plo (h + 1) then (1 : ℝ) else 0) =
      if plo 0 ≤ x ∧ x < plo K then 1 else 0
  | 0, _ => by simp
  | K + 1, hm => by
    rw [Finset.sum_range_succ, count_parts plo x K (fun h hh => hm h (by omega))]
    have h1 : plo 0 ≤ plo K := by
      clear count_parts
      induction K with
      | zero => exact le_rfl
      | succ K ih => exact (ih (fun h hh => hm h (by omega))).trans (hm K (by omega))
    have h2 := hm K (by omega)
    by_cases ha : plo 0 ≤ x ∧ x < plo K
    · rw [if_pos ha, if_neg (by omega), if_pos ⟨ha.1, by omega⟩]; ring
    · rw [if_neg ha]
      by_cases hb : plo K ≤ x ∧ x < plo (K + 1)
      · rw [if_pos hb, if_pos ⟨by omega, hb.2⟩]; ring
      · rw [if_neg hb, if_neg (by omega)]; ring

theorem filter_sum_parts {α : Type*} (own : α → ℕ) (plo : ℕ → ℕ) (K : ℕ) (hm : ∀ h, h < K → plo h ≤ plo (h + 1))
    (f : α → ℝ) : ∀ (ps : List α), (∀ p ∈ ps, plo 0 ≤ own p ∧ own p < plo K) →
    ∑ h ∈ Finset.range K, ((ps.filter fun p => Nat.ble (plo h) (own p) && Nat.blt (own p) (plo (h + 1))).map f).sum =
      (ps.map f).sum
  | [], _ => by simp
  | p :: ps, hp => by
    have ih := filter_sum_parts own plo K hm f ps (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    have hsplit : ∀ h, (((p :: ps).filter fun p => Nat.ble (plo h) (own p) && Nat.blt (own p) (plo (h + 1))).map f).sum
        = (if plo h ≤ own p ∧ own p < plo (h + 1) then (1 : ℝ) else 0) * f p +
          ((ps.filter fun p => Nat.ble (plo h) (own p) && Nat.blt (own p) (plo (h + 1))).map f).sum := by
      intro h
      rw [List.filter_cons]
      by_cases hc : plo h ≤ own p ∧ own p < plo (h + 1)
      · rw [if_pos (by simp [Nat.ble_eq, Nat.blt_eq, hc.1, hc.2]), if_pos hc, List.map_cons, List.sum_cons, one_mul]
      · rw [if_neg (by simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact hc), if_neg hc, zero_mul,
          zero_add]
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, ih, List.map_cons, List.sum_cons]
    rw [count_parts plo (own p) K hm, if_pos (hp p (List.mem_cons_self ..)), one_mul]

namespace DegD

variable (L : DegD)

theorem clsPairs_lt (b k : ℕ) : ∀ p ∈ L.clsPairs b k, p.1 < 256 ∧ p.2 < 256 := by
  intro p hp
  unfold DegD.clsPairs at hp
  dsimp only at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  have hx16 : x < 2 ^ 16 := by
    unfold sRun at hx
    generalize Nat.sub _ _ = cnt at hx
    generalize sAt (L.pOffC b) 16 10 k = i0 at hx
    clear hp
    induction cnt generalizing i0 with
    | zero => exact absurd hx (List.not_mem_nil)
    | succ cnt ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · unfold sAt; rw [slotAt_eq']; exact Nat.mod_lt _ (by positivity)
      · exact ih _ hx
  constructor
  · show Nat.land x 255 < 256
    rw [show Nat.land x 255 = x % 256 from Nat.and_two_pow_sub_one_eq_mod x 8]
    exact Nat.mod_lt _ (by norm_num)
  · show Nat.shiftRight x 8 < 256
    rw [shr_eq]
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by norm_num at hx ⊢; omega)

/-- **Owner parts**: the parts of a class sum to the class. -/
theorem parts_sum (sd : SumD) (b k : ℕ) (hb : b < Nat.add L.dH 8) (hpo : L.partsOk sd = true)
    (P : ℕ → ℕ → ℝ) :
    ∑ h ∈ Finset.range (sd.np b), qSumF P (L.clsPart sd b k (sd.plo b h) (sd.plo b (h + 1))) =
      qSumF P (L.clsPairs b k) := by
  obtain ⟨h0, hN, hm⟩ := partsOk_spec L sd hpo b hb
  unfold qSumF DegD.clsPart SumD.inPart
  refine filter_sum_parts (fun p : ℕ × ℕ => sd.own b p.1 p.2) (sd.plo b) (sd.np b) hm _ _ (fun p hp => ?_)
  have hp' := L.clsPairs_lt b k p hp
  refine ⟨by rw [h0]; exact Nat.zero_le _, lt_of_lt_of_le ?_ hN⟩
  unfold SumD.own
  cases Nat.beq (Nat.land (Nat.shiftRight (sd.dm b) p.2) 1) 1
  · cases Nat.beq (Nat.land (Nat.shiftRight (sd.dm b) p.1) 1) 1
    · show 256 + p.1 < 512; omega
    · show p.1 < 512; omega
  · show p.2 < 512; omega

/-! ## The coefficient of a class at a coordinate -/

/-- The integer coefficient of the class polynomial with key `x` at the tag of coordinate `r`. -/
noncomputable def kcoef (b x r : ℕ) : ℤ := rawIntegerLookup (L.clsPoly (psTab L.nPS) (ppsTab L.nPS) b x) (L.rtag r)

/-- The checked facts of block `b` used by the representation. -/
structure BlockChecks (b : ℕ) : Prop where
  tag : L.tagOk = true
  cls : L.clsOk b = true
  grp : L.grpOk b = true
  e : ∀ g, g < L.nGrp b → ∀ r, r < L.nc →
    ∃ r0 r1, r0 ≤ r ∧ r < r1 ∧ L.eOkC b g r0 r1 = true

/-- The coefficient list of a passing group is the class coefficient list. -/
theorem eTab_eq (b g r : ℕ) (hc : L.BlockChecks b) (hg : g < L.nGrp b) (hr : r < L.nc) :
    (L.eTab (32 * b + g)).getD r [] =
      eRow 32 r (L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g) (L.glo b g) ∧
    ∀ i, i < L.glo b (g + 1) - L.glo b g →
      vCoef 32 r ((L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g).getD i (0, 0, 0)) =
        L.kcoef b (L.clsKey b (L.glo b g + i)) r := by
  obtain ⟨r0, r1, h0, h1, hok⟩ := hc.e g hg r hr
  obtain ⟨hE, hV⟩ := L.eOk_spec _ _ 32 b g r0 r1 hok r h0 h1 hr
  refine ⟨hE, fun i hi => ?_⟩
  rw [L.vTab_getD _ _ 32 b g i hi, L.clsAcc_eq]
  have hmem : L.clsAcc ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b (L.clsKey b (L.glo b g + i)) ∈
      L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g := by
    rw [← L.vTab_getD _ _ 32 b g i hi, List.getD_eq_getElem _ _ (by rw [L.vTab_length]; exact hi)]
    exact List.getElem_mem _
  have hb := hV _ hmem
  rw [L.clsAcc_eq] at hb
  unfold vCoef kcoef
  rw [slot_denseAcc L.ridx L.nc 32 (by norm_num) _ hb r hr, L.lookup_ridx hc.tag _ r hr]

end DegD

/-! ## Symmetric double sums -/

theorem sym_sum (G : ℕ → ℕ → ℝ) : ∀ n, (∀ u v, u < n → v < n → G u v = G v u) →
    ∑ u ∈ Finset.range n, ∑ v ∈ Finset.range n, G u v =
      ∑ v ∈ Finset.range n, ∑ u ∈ Finset.range (v + 1), (if u = v then (1 : ℝ) else 2) * G u v
  | 0, _ => by simp
  | n + 1, hG => by
    have ih := sym_sum G n (fun u v hu hv => hG u v (by omega) (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun v => ∑ u ∈ Finset.range (v + 1), _)]
    simp_rw [Finset.sum_range_succ (fun v => G _ v)]
    rw [Finset.sum_add_distrib, ih]
    rw [Finset.sum_range_succ (fun u => (if u = n then (1 : ℝ) else 2) * G u n), if_pos rfl, one_mul]
    have h2 : ∑ u ∈ Finset.range n, (if u = n then (1 : ℝ) else 2) * G u n = ∑ u ∈ Finset.range n, 2 * G u n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [if_neg (by have := Finset.mem_range.mp hu; omega)]
    have h3 : ∑ v ∈ Finset.range n, G n v = ∑ u ∈ Finset.range n, G u n := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hG n u (by omega) (by have := Finset.mem_range.mp hu; omega)
    rw [h2, h3, ← Finset.mul_sum]
    ring

theorem triPairs_sum (F : ℕ × ℕ → ℝ) (n : ℕ) :
    ((DegD.triPairs n).map F).sum = ∑ v ∈ Finset.range n, ∑ u ∈ Finset.range (v + 1), F (u, v) := by
  unfold DegD.triPairs
  rw [DegD.sum_map_flatMap', list_sum_range]
  apply Finset.sum_congr rfl
  intro v _
  rw [List.map_map, list_sum_range]
  rfl

/-! ## The representation theorem -/

namespace DegD

variable (L : DegD)

/-- The raw-tensor coefficient of the pair `(u, v)` at coordinate `r` (symmetric). -/
noncomputable def Cc (b r u v : ℕ) : ℝ := (L.kcoef b (L.pairKey b (min u v) (max u v)) r : ℝ) / L.bden b

theorem qLen_ge (b g : ℕ) : L.glo b (g + 1) - L.glo b g ≤ L.qLen b g := by
  unfold qLen
  rw [show Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g) = L.glo b (g + 1) - L.glo b g from rfl, shr_eq]
  show _ ≤ 16 * ((L.glo b (g + 1) - L.glo b g) / 2 ^ 4 + 1)
  have := Nat.div_add_mod (L.glo b (g + 1) - L.glo b g) 16
  have := Nat.mod_lt (L.glo b (g + 1) - L.glo b g) (show 16 > 0 by norm_num)
  norm_num
  omega

/-- One piece at a coordinate: the class coefficients times the owner-restricted class sums. -/
theorem pieceF_eq (sd : SumD) (P : ℕ → ℕ → ℝ) (b g lo hi r : ℕ) (hc : L.BlockChecks b) (hg : g < L.nGrp b)
    (hr : r < L.nc) :
    L.pieceF sd P b g lo hi ((L.eTab (32 * b + g)).getD r []) =
      ∑ i ∈ Finset.range (L.glo b (g + 1) - L.glo b g),
        (L.kcoef b (L.clsKey b (L.glo b g + i)) r : ℝ) / L.bden b * qSumF P (L.clsPart sd b (L.glo b g + i) lo hi) := by
  obtain ⟨hE, hV⟩ := L.eTab_eq b g r hc hg hr
  unfold DegD.pieceF
  rw [hE]
  have key := eRow_sum 32 r (L.bden b) (fun k => L.qTabF sd P b g lo hi (Nat.sub k (L.glo b g)))
    (L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g) (L.glo b g)
  have hl := L.vTab_length ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g
  rw [hl] at key
  have e1 : ((eRow 32 r (L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g) (L.glo b g)).map
      fun e => (if L.qTabE sd b g lo hi (Nat.sub e.1 (L.glo b g)) = true then 0 else
        qval (e.2.1, e.2.2, L.bden b)) * L.qTabF sd P b g lo hi (Nat.sub e.1 (L.glo b g))) =
      (eRow 32 r (L.vTab ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g) (L.glo b g)).map
      fun e => qval (e.2.1, e.2.2, L.bden b) * L.qTabF sd P b g lo hi (Nat.sub e.1 (L.glo b g)) := by
    apply List.map_congr_left
    intro e _
    by_cases h : L.qTabE sd b g lo hi (Nat.sub e.1 (L.glo b g)) = true
    · rw [if_pos h, L.qTabF_zero sd P b g lo hi _ h]; simp
    · rw [if_neg h]
  rw [e1, key]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hql := L.qLen_ge b g
  rw [hV i hi']
  congr 1
  rw [show Nat.sub (L.glo b g + i) (L.glo b g) = i by show L.glo b g + i - L.glo b g = i; omega]
  unfold DegD.qTabF
  rw [if_pos (by omega)]
  rfl

/-- **Representation theorem.** -/
theorem rep_sum (sd : SumD) (b r : ℕ) (hb : b < Nat.add L.dH 8) (hc : L.BlockChecks b) (hpo : L.partsOk sd = true)
    (hr : r < L.nc) (P : ℕ → ℕ → ℝ) (hP : ∀ u v, u < L.rdim b → v < L.rdim b → P u v = P v u) :
    ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        L.pieceF sd P b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r []) =
      ∑ u ∈ Finset.range (L.rdim b), ∑ v ∈ Finset.range (L.rdim b), L.Cc b r u v * P u v := by
  have hcf := L.clsOk_spec b hc.cls
  -- pieces → classes
  have step1 : ∀ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
      L.pieceF sd P b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r []) =
      ∑ i ∈ Finset.range (L.glo b (g + 1) - L.glo b g),
        (L.kcoef b (L.clsKey b (L.glo b g + i)) r : ℝ) / L.bden b * qSumF P (L.clsPairs b (L.glo b g + i)) := by
    intro g hg
    simp_rw [L.pieceF_eq sd P b g _ _ r hc (Finset.mem_range.mp hg) hr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, L.parts_sum sd b _ hb hpo P]
  rw [Finset.sum_congr rfl step1, L.grp_sum b hc.grp
    (fun k => (L.kcoef b (L.clsKey b k) r : ℝ) / L.bden b * qSumF P (L.clsPairs b k))]
  -- classes → pairs
  have step2 : ∀ k ∈ Finset.range (L.nCls b), (L.kcoef b (L.clsKey b k) r : ℝ) / L.bden b * qSumF P (L.clsPairs b k)
      = ((L.clsPairs b k).map fun p => (if p.1 = p.2 then (1 : ℝ) else 2) * (L.Cc b r p.1 p.2 * P p.1 p.2)).sum := by
    intro k hk
    unfold qSumF
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro p hp
    obtain ⟨hle, -, hkey⟩ := hcf.pairs k (Finset.mem_range.mp hk) p hp
    unfold Cc
    rw [min_eq_left hle, max_eq_right hle, hkey]
    ring
  rw [Finset.sum_congr rfl step2, L.cls_sum b hcf, triPairs_sum]
  -- pairs → the symmetric double sum
  rw [sym_sum (fun u v => L.Cc b r u v * P u v) (L.rdim b) (fun u v hu hv => by
    unfold Cc; rw [min_comm, max_comm, hP u v hu hv])]

#print axioms rep_sum

end DegD

end ThomsonCompact.CoeffMap.Deg
