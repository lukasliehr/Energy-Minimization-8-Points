import ThomsonNegative.Compact.Target.SourceData

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed ThomsonNegative.Geometry
variable {N S B W : ℕ}

theorem sourceOrder_getD (i : Fin 4) :
    ([0,2,1,3] : List ℕ).getD i.val 0=(sourcePermutation i).val := by
  fin_cases i
  · change 0=(sourcePermutation 0).val; rw [sourcePermutation_zero]; rfl
  · change 2=(sourcePermutation 1).val; rw [sourcePermutation_one]; rfl
  · change 1=(sourcePermutation 2).val; rw [sourcePermutation_two]; rfl
  · change 3=(sourcePermutation 3).val; rw [sourcePermutation_three]; rfl

theorem grid4_getD {α : Type*} (f : ℕ → ℕ → α) (d : α) (h l : ℕ) (hh : h<4) (hl : l<4) :
    (((List.range 4).map (fun i => (List.range 4).map (f i))).getD h []).getD l d=f h l := by
  rw [getD_eq_get ((List.range 4).map (fun i => (List.range 4).map (f i))) h [] (by simpa using hh)]
  simp only [List.getElem_map,List.getElem_range]
  rw [getD_eq_get ((List.range 4).map (f h)) l d (by simpa using hl)]
  simp only [List.getElem_map,List.getElem_range]

theorem labels_length : labels.length=8 := rfl
theorem labels_getD (i : ℕ) (hi : i<8) : labels.getD i 0=i/2 := by
  interval_cases i <;> rfl

theorem newtonCoeffs_length (c : Ctx) (Vs Hs Gs : List (List TM)) (ls : List ℕ) :
    ∀ (r k : ℕ) (col : List TM), (newtonCoeffs c Vs Hs Gs ls r k col).length=r
  | 0,_,_ => rfl
  | r+1,k,col => by simp only [newtonCoeffs,List.length_cons,newtonCoeffs_length]

theorem invN_eok (hg : Good N S B W) {D : TM} {d : ℝ → ℝ}
    (hD : EOK (mkCtx N S B W) D d) (k tol : ℕ)
    (hok : (invN (mkCtx N S B W) k tol D).ok=true) :
    (∀ t ∈ Set.Icc (-1:ℝ) 1, d t≠0) ∧
      Encl (mkCtx N S B W) (invN (mkCtx N S B W) k tol D) (fun t => (d t)⁻¹) := by
  have hdok := (mul_ok (recip_ok hok).2).2
  exact invN_sound hg (hD hdok) k tol hok

/-- Generic assembly for the exact executable eight-condition confluent table.
The whole-cell semantic polynomial uses the supplied endpoint-safe jets. -/
theorem hermiteCoefficients_eok (hg : Good N S B W) (hS : 1≤S)
    (par : Parameters) (nodes : List TM) (jets : List JetPair) (q a : ℝ → ℝ)
    (ha : ∀ t ∈ Set.Icc (-1:ℝ) 1, a t ∈ Set.Ioo (5/16:ℝ) (1/3))
    (hX : ∀ l<4, EOK (mkCtx N S B W) (nodes.getD l zeroTM) (fun t => sourceContactNat (a t) l))
    (hJ : ∀ i : Fin 4,
      EOK (mkCtx N S B W) (jets.getD i.val zeroPair).value (fun t => rawValue (q t) (a t) i) ∧
      EOK (mkCtx N S B W) (jets.getD i.val zeroPair).slope (fun t => rawSlope (q t) (a t) i)) :
    (hermiteCoefficients (mkCtx N S B W) par nodes jets).length=8 ∧
      ∀ i<8, EOK (mkCtx N S B W) ((hermiteCoefficients (mkCtx N S B W) par nodes jets).getD i zeroTM)
        (fun t => (semanticPolynomial (q t) (a t)).coeff i) := by
  let c := mkCtx N S B W
  let Vs := ([0,2,1,3] : List ℕ).map (fun i => [(jets.getD i zeroPair).value,half c (jets.getD i zeroPair).slope])
  let Hs := (List.range 4).map (fun h => (List.range 4).map (fun l => radd c (nodes.getD h zeroTM) (neg c (nodes.getD l zeroTM))))
  let Gs := (List.range 4).map (fun h => (List.range 4).map (fun l =>
    if Nat.beq h l then zeroTM else invN c par.newtonFuel par.tolerance ((Hs.getD h []).getD l zeroTM)))
  let xs := fun t l => sourceContactNat (a t) l
  let zE := fun t => doubleNode (sourceContact (a t))
  let J := fun t => suppliedJet (q t) (a t)
  have hVs (l : ℕ) (hl : l<4) : Vs.getD l []=
      [(jets.getD (sourcePermutation ⟨l,hl⟩).val zeroPair).value,
        half c (jets.getD (sourcePermutation ⟨l,hl⟩).val zeroPair).slope] := by
    rw [getD_map_lt _ _ _ 0 [] (by simpa using hl)]
    rw [sourceOrder_getD ⟨l,hl⟩]
  have hV (l k : ℕ) (hl : l<4) (hk : k<2) :
      EOK c ((Vs.getD l []).getD k zeroTM) (fun t => J t k (xs t l)/(k.factorial:ℝ)) := by
    rw [hVs l hl]
    have hz (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) := sourceContact_injective (a t) (ha t ht)
    interval_cases k
    · apply (hJ (sourcePermutation ⟨l,hl⟩)).1.congr
      intro t ht
      simp only [J,xs,sourceContactNat,dif_pos hl,suppliedJet_at _ _ (hz t ht),jetEntry,ite_true,
        Nat.factorial_zero,Nat.cast_one,div_one,sourceValue]
    · apply (half_eok hg hS (hJ (sourcePermutation ⟨l,hl⟩)).2).congr
      intro t ht
      simp only [J,xs,sourceContactNat,dif_pos hl,suppliedJet_at _ _ (hz t ht),jetEntry,
        Nat.one_ne_zero,ite_false,ite_true,Nat.factorial_one,Nat.cast_one,div_one,sourceSlope]
  have hHs (h l : ℕ) (hh : h<4) (hl : l<4) :
      (Hs.getD h []).getD l zeroTM=radd c (nodes.getD h zeroTM) (neg c (nodes.getD l zeroTM)) :=
    grid4_getD _ _ h l hh hl
  have hH (h l : ℕ) (hh : h<4) (hl : l<4) :
      EOK c ((Hs.getD h []).getD l zeroTM) (fun t => xs t h-xs t l) := by
    rw [hHs h l hh hl]
    exact (radd_eok hg (hX h hh) (neg_eok (hX l hl) rfl)).congr (fun t _ => by ring)
  have hGs (h l : ℕ) (hh : h<4) (hl : l<4) (hne : h≠l) :
      (Gs.getD h []).getD l zeroTM=invN c par.newtonFuel par.tolerance ((Hs.getD h []).getD l zeroTM) := by
    rw [grid4_getD _ _ h l hh hl]
    have he : ¬Nat.beq h l=true := fun he => hne (Nat.eq_of_beq_eq_true he)
    simp [he]
  have hG (h l : ℕ) (hh : h<4) (hl : l<4) (hne : h≠l)
      (hok : ((Gs.getD h []).getD l zeroTM).ok=true) :
      (∀ t ∈ Set.Icc (-1:ℝ) 1, xs t h-xs t l≠0) ∧
        Encl c ((Gs.getD h []).getD l zeroTM) (fun t => (xs t h-xs t l)⁻¹) := by
    rw [hGs h l hh hl hne] at hok ⊢
    exact invN_eok hg (hH h l hh hl) par.newtonFuel par.tolerance hok
  have H : TabCtx c Vs Hs Gs labels zE xs J (fun _ => 2) := by
    refine ⟨?_,?_,?_,?_,?_,hV,?_,hG⟩
    · intro i hi
      rw [labels_length] at hi
      rw [labels_getD i hi]
      omega
    · intro t ht i hi
      rw [labels_length] at hi
      interval_cases i <;> rfl
    · intro t ht h l hh hl he
      simp only [xs,sourceContactNat,dif_pos hh,dif_pos hl] at he
      exact congrArg Fin.val (sourceContact_injective (a t) (ha t ht) he)
    · intro i j hij hj he
      rw [labels_length] at hj
      rw [labels_getD i (by omega),labels_getD j hj] at he
      omega
    · intro i hi; norm_num
    · intro h l hh hl hne; exact hH h l hh hl
  let col := labels.map (fun l => (Vs.getD l []).getD 0 zeroTM)
  let cs := newtonCoeffs c Vs Hs Gs labels 8 0 col
  have hcolLen : col.length=labels.length := List.length_map _
  have hcol : ∀ i<col.length, EOK c (col.getD i zeroTM)
      (fun t => confluentTable (zE t) (J t) 0 i) := by
    intro i hi
    have hi' : i<labels.length := by simpa [hcolLen] using hi
    rw [getD_map_lt _ _ _ 0 zeroTM hi']
    exact (hV (labels.getD i 0) 0 (H.lab_lt i hi') (by norm_num)).congr (fun t ht => by
      rw [confluentTable,H.hz t ht i hi']; norm_num)
  have hcs := newtonCoeffs_sound hg H 8 0 col (by rw [hcolLen]; omega) (by rw [labels_length]) hcol
  have hcsLen : cs.length=labels.length := by rw [newtonCoeffs_length,labels_length]
  have HH := hornerN_sound hg H hX (fun t ht => by simp [xs,sourceContactNat]) cs hcsLen
    (fun i hi => (hcs i (by simpa [labels_length] using hi)).congr (fun t _ => by rw [Nat.zero_add]))
    8 (by rw [labels_length])
  rw [labels_length,Nat.sub_self,List.drop_zero,List.drop_zero] at HH
  exact ⟨HH.1,fun i hi => (HH.2.1 i hi).congr (fun t _ => rfl)⟩

#print axioms hermiteCoefficients_eok
end ThomsonNegative.Compact.Target
