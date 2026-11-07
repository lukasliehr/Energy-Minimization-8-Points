import ThomsonNegative.Compact.Target.JetsSound

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

theorem inverse_sqrt_two_eq : (Real.sqrt 2)⁻¹=(Real.sqrt 2)/2 := by
  have hs : Real.sqrt (2:ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  field_simp [hs]
  nlinarith

theorem contactX_eq_arguments (a : ℝ) :
    contactX a = ![(1+a)/2,a,(1-a)*(2+Real.sqrt 2)/4,(1-a)*(2-Real.sqrt 2)/4] := by
  funext i
  fin_cases i <;> dsimp [contactX,lowC,lowD] <;> simp only [inverse_sqrt_two_eq] <;> ring

theorem contactX_lipschitz (a b : ℝ) (i : Fin 4) : |contactX a i-contactX b i| ≤ |a-b| := by
  have h := contact_argument_lipschitz a b
  rw [contactX_eq_arguments,contactX_eq_arguments]
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem auxSeries_eq_normalized (q x : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hx : x ∈ Set.Ico (0:ℝ) 1) : auxSeries q x=normalizedAux q x := by
  exact (normalizedAux_hasSum q x hq (by rw [abs_of_nonneg hx.1]; exact hx.2)).tsum_eq

theorem slopeSeries_eq_auxSlope (q x : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hx : x ∈ Set.Ico (0:ℝ) 1) : slopeSeries q x=auxSlope q x :=
  (auxSlope_eq_slopeSeries q x hq.1.ne' (by rw [abs_of_nonneg hx.1]; exact hx.2)).symm

theorem rawJets_interior (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) (i : Fin 4) :
    rawValue q a i=normalizedAux q (contactX a i) ∧
      rawSlope q a i=auxSlope q (contactX a i) := by
  obtain ⟨hb,hc,hd⟩ := low_arguments_domain a ha
  have hH := auxSeries_eq_normalized q (1/2) hq (by norm_num)
  have hJ := slopeSeries_eq_auxSlope q (1/2) hq (by norm_num)
  have hB := auxSeries_eq_normalized q a hq ⟨hb.1,by linarith [hb.2]⟩
  have hS := slopeSeries_eq_auxSlope q a hq ⟨hb.1,by linarith [hb.2]⟩
  have hC := auxSeries_eq_normalized q (lowC a) hq ⟨hc.1,by linarith [hc.2]⟩
  have hT := slopeSeries_eq_auxSlope q (lowC a) hq ⟨hc.1,by linarith [hc.2]⟩
  have hD := auxSeries_eq_normalized q (lowD a) hq ⟨hd.1,by linarith [hd.2]⟩
  have hU := slopeSeries_eq_auxSlope q (lowD a) hq ⟨hd.1,by linarith [hd.2]⟩
  fin_cases i
  · constructor
    · change auxSeries q (1/2)+(a/2)*slopeSeries q (1/2)+
        ((q*slopeSeries q (1/2)+1)/2)*auxSeries q a=normalizedAux q ((1+a)/2)
      rw [hH,hJ,hB,normalizedAux_half_recenter q a hq (by linarith [hb.2])]
      ring
    · change slopeSeries q (1/2)+(q*slopeSeries q (1/2)+1)*slopeSeries q a=auxSlope q ((1+a)/2)
      rw [hJ,hS,auxSlope_half_recenter q a hq.1.ne' (by linarith [hb.2])]
      ring
  · exact ⟨hB,hS⟩
  · constructor
    · change auxSeries q (1/2)+(lowC a/2)*slopeSeries q (1/2)+
        ((q*slopeSeries q (1/2)+1)/2)*auxSeries q (lowC a)=normalizedAux q ((1+lowC a)/2)
      rw [hH,hJ,hC,normalizedAux_half_recenter q (lowC a) hq (by linarith [hc.2])]
      ring
    · change slopeSeries q (1/2)+(q*slopeSeries q (1/2)+1)*slopeSeries q (lowC a)=auxSlope q ((1+lowC a)/2)
      rw [hJ,hT,auxSlope_half_recenter q (lowC a) hq.1.ne' (by linarith [hc.2])]
      ring
  · exact ⟨hD,hU⟩

theorem rawValue_lipschitz (q a b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) (hb : b ∈ Set.Icc (5/16:ℝ) (1/3)) (i : Fin 4) :
    |rawValue q a i-rawValue q b i| ≤ 2*|a-b| := by
  rw [(rawJets_interior q a hq ha i).1,(rawJets_interior q b hq hb i).1]
  exact (normalizedAux_lipschitz q _ _ hq (contactX_domain a ha i) (contactX_domain b hb i)).trans
    (mul_le_mul_of_nonneg_left (contactX_lipschitz a b i) (by norm_num))

theorem rawSlope_lipschitz (q a b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) (hb : b ∈ Set.Icc (5/16:ℝ) (1/3)) (i : Fin 4) :
    |rawSlope q a i-rawSlope q b i| ≤ 9*|a-b| := by
  rw [(rawJets_interior q a hq ha i).2,(rawJets_interior q b hq hb i).2]
  exact (auxSlope_lipschitz q _ _ ⟨hq.1,hq.2.le⟩ (contactX_domain a ha i) (contactX_domain b hb i)).trans
    (mul_le_mul_of_nonneg_left (contactX_lipschitz a b i) (by norm_num))

theorem cachedValue_sound {q p : ℝ → ℝ} {V : TM} (ε : ℕ)
    (hV : Encl (mkCtx N S B W) V (fun t => rawValue (q t) (p t) i))
    (hp : ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3))
    (he : ∀ t ∈ Set.Icc (-1:ℝ) 1, |extendedHeight q p t-p t| ≤ (ε:ℝ)/2^S) :
    Encl (mkCtx N S B W) (widen V (2*ε))
      (fun t => rawValue (q t) (extendedHeight q p t) i) := by
  apply widen_sound _ hV
  intro t ht
  by_cases hq : 0<q t ∧ q t<1
  · have h := rawValue_lipschitz (q t) _ _ hq
      ⟨(extendedHeight_range q p hp t ht).1.le,(extendedHeight_range q p hp t ht).2.le⟩
      ⟨(hp t ht).1.le,(hp t ht).2.le⟩ i
    calc
      _ ≤ 2*|extendedHeight q p t-p t| := h
      _ ≤ 2*((ε:ℝ)/2^S) := mul_le_mul_of_nonneg_left (he t ht) (by norm_num)
      _ = _ := by simp only [mk_S]; push_cast; ring
  · simp only [extendedHeight,if_neg hq,sub_self,abs_zero,mk_S]
    positivity

theorem cachedSlope_sound {q p : ℝ → ℝ} {V : TM} (ε : ℕ)
    (hV : Encl (mkCtx N S B W) V (fun t => rawSlope (q t) (p t) i))
    (hp : ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3))
    (he : ∀ t ∈ Set.Icc (-1:ℝ) 1, |extendedHeight q p t-p t| ≤ (ε:ℝ)/2^S) :
    Encl (mkCtx N S B W) (widen V (9*ε))
      (fun t => rawSlope (q t) (extendedHeight q p t) i) := by
  apply widen_sound _ hV
  intro t ht
  by_cases hq : 0<q t ∧ q t<1
  · have h := rawSlope_lipschitz (q t) _ _ hq
      ⟨(extendedHeight_range q p hp t ht).1.le,(extendedHeight_range q p hp t ht).2.le⟩
      ⟨(hp t ht).1.le,(hp t ht).2.le⟩ i
    calc
      _ ≤ 9*|extendedHeight q p t-p t| := h
      _ ≤ 9*((ε:ℝ)/2^S) := mul_le_mul_of_nonneg_left (he t ht) (by norm_num)
      _ = _ := by simp only [mk_S]; push_cast; ring
  · simp only [extendedHeight,if_neg hq,sub_self,abs_zero,mk_S]
    positivity

def rawRoot (q a : ℝ) : ℝ :=
  16*(rawSlope q a 0+rawSlope q a 1-((Real.sqrt 2)⁻¹+1)*rawSlope q a 2-
    (1-(Real.sqrt 2)⁻¹)*rawSlope q a 3)

theorem rawRoot_interior (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) : rawRoot q a=seriesRoot q a := by
  unfold rawRoot
  rw [(rawJets_interior q a hq ha 0).2,(rawJets_interior q a hq ha 1).2,
    (rawJets_interior q a hq ha 2).2,(rawJets_interior q a hq ha 3).2]
  rw [contactX_eq_arguments]
  change 16*(auxSlope q ((1+a)/2)+auxSlope q a-
    ((Real.sqrt 2)⁻¹+1)*auxSlope q ((1-a)*(2+Real.sqrt 2)/4)-
    (1-(Real.sqrt 2)⁻¹)*auxSlope q ((1-a)*(2-Real.sqrt 2)/4))=seriesRoot q a
  rw [inverse_sqrt_two_eq]
  unfold seriesRoot
  ring

theorem rootFromJets_eok (hg : Good N S B W) {IR : TM} {q a : ℝ → ℝ}
    (hIR : EOK (mkCtx N S B W) IR (fun _ => (Real.sqrt 2)⁻¹))
    (jets : List JetPair)
    (hjets : ∀ i : Fin 4, EOK (mkCtx N S B W) (jets.getD i.val zeroPair).slope
      (fun t => rawSlope (q t) (a t) i)) :
    EOK (mkCtx N S B W) (rootFromJets (mkCtx N S B W) IR jets)
      (fun t => rawRoot (q t) (a t)) := by
  have hPlus := refresh_eok hg (addC_eok hg hIR false (2^S) 0 1 (by simp))
  have hMinus := oneSub_eok hg hIR
  have hZ := radd_eok hg (hjets 0) (hjets 1)
  have hZ := radd_eok hg hZ (neg_eok (rmul_eok hg hPlus (hjets 2)) rfl)
  have hZ := radd_eok hg hZ (neg_eok (rmul_eok hg hMinus (hjets 3)) rfl)
  have hs : |(16:ℝ)-((16*2^S:ℕ):ℝ)/2^S| ≤ (0:ℝ)/2^S := by
    push_cast; simp
  apply (refresh_eok hg (smul_eok hg hZ false (16*2^S) 0 16 (by simpa using hs))).congr
  intro t _
  unfold rawRoot
  ring

#print axioms rawJets_interior
#print axioms cachedValue_sound
#print axioms cachedSlope_sound
#print axioms rootFromJets_eok
end ThomsonNegative.Compact.Target
