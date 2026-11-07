import ThomsonNegative.Compact.Target.RootSound

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

def lowC (a : ℝ) : ℝ := (1-a)*((Real.sqrt 2)⁻¹+1)-1
def lowD (a : ℝ) : ℝ := (1-a)*(1-(Real.sqrt 2)⁻¹)/2
def contactX (a : ℝ) : Fin 4 → ℝ :=
  ![(1+a)/2,a,(1+lowC a)/2,lowD a]

def rawValue (q a : ℝ) : Fin 4 → ℝ :=
  let H := auxSeries q (1/2)
  let J := slopeSeries q (1/2)
  let B := auxSeries q a
  let C := auxSeries q (lowC a)
  let D := auxSeries q (lowD a)
  let W := q*J+1
  ![H+(a/2)*J+(W/2)*B,B,H+(lowC a/2)*J+(W/2)*C,D]

def rawSlope (q a : ℝ) : Fin 4 → ℝ :=
  let J := slopeSeries q (1/2)
  let S := slopeSeries q a
  let T := slopeSeries q (lowC a)
  let U := slopeSeries q (lowD a)
  let W := q*J+1
  ![J+W*S,S,J+W*T,U]

theorem inverse_sqrt_two_bounds : (2:ℝ)/3 ≤ (Real.sqrt 2)⁻¹ ∧ (Real.sqrt 2)⁻¹ ≤ (3:ℝ)/4 := by
  have hs : (0:ℝ)<Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [inv_eq_one_div]
  constructor
  · apply (le_div_iff₀ hs).2; nlinarith
  · apply (div_le_iff₀ hs).2; nlinarith

theorem low_arguments_domain (a : ℝ) (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) :
    a ∈ Set.Icc (0:ℝ) (1/3) ∧ lowC a ∈ Set.Icc (0:ℝ) (17/64) ∧
      lowD a ∈ Set.Icc (0:ℝ) (1/8) := by
  obtain ⟨hr0,hr1⟩ := inverse_sqrt_two_bounds
  have h1 : (2:ℝ)/3 ≤ 1-a := by linarith [ha.2]
  have h2 : 1-a ≤ (11:ℝ)/16 := by linarith [ha.1]
  have hc0 := mul_le_mul h1 (show (5:ℝ)/3 ≤ (Real.sqrt 2)⁻¹+1 by linarith)
    (by norm_num : (0:ℝ)≤5/3) (by linarith : 0≤1-a)
  have hc1 := mul_le_mul h2 (show (Real.sqrt 2)⁻¹+1 ≤ (7:ℝ)/4 by linarith)
    (by linarith : 0≤(Real.sqrt 2)⁻¹+1) (by norm_num : (0:ℝ)≤11/16)
  have hd0 : 0 ≤ (1-a)*(1-(Real.sqrt 2)⁻¹) := mul_nonneg (by linarith) (by linarith)
  have hd1 := mul_le_mul h2 (show 1-(Real.sqrt 2)⁻¹ ≤ (1:ℝ)/3 by linarith)
    (by linarith : 0≤1-(Real.sqrt 2)⁻¹) (by norm_num : (0:ℝ)≤11/16)
  refine ⟨⟨by linarith [ha.1],ha.2⟩,?_,?_⟩
  · unfold lowC; constructor <;> nlinarith
  · unfold lowD; constructor <;> nlinarith

theorem contactX_domain (a : ℝ) (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) (i : Fin 4) :
    contactX a i ∈ Set.Icc (0:ℝ) (2/3) := by
  obtain ⟨hb,hc,hd⟩ := low_arguments_domain a ha
  fin_cases i
  · change (1+a)/2 ∈ Set.Icc (0:ℝ) (2/3)
    constructor <;> linarith [hb.1,hb.2]
  · change a ∈ Set.Icc (0:ℝ) (2/3)
    constructor <;> linarith [hb.1,hb.2]
  · change (1+lowC a)/2 ∈ Set.Icc (0:ℝ) (2/3)
    constructor <;> linarith [hc.1,hc.2]
  · change lowD a ∈ Set.Icc (0:ℝ) (2/3)
    constructor <;> linarith [hd.1,hd.2]

theorem const_eok (hg : Good N S B W) (ng : Bool) (mag err : ℕ) (z : ℝ)
    (hz : |z-(if ng then -(mag:ℝ) else mag)/2^S| ≤ (err:ℝ)/2^S) :
    EOK (mkCtx N S B W) (constTM (mkCtx N S B W) ng mag err) (fun _ => z) :=
  fun hok => constTM_sound hg ng mag err z hz hok

theorem proposedJets_eok (hg : Good N S B W) (hS : 1≤S) {Q P IR : TM} {q a : ℝ → ℝ}
    (hQ : EOK (mkCtx N S B W) Q q) (hP : EOK (mkCtx N S B W) P a)
    (hIR : EOK (mkCtx N S B W) IR (fun _ => (Real.sqrt 2)⁻¹))
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (ha : ∀ t ∈ Set.Icc (-1:ℝ) 1, a t ∈ Set.Icc (5/16:ℝ) (1/3))
    (p : Parameters) (i : Fin 4) :
    EOK (mkCtx N S B W) ((proposedJets (mkCtx N S B W) Q P IR p).getD i.val zeroPair).value
      (fun t => rawValue (q t) (a t) i) ∧
    EOK (mkCtx N S B W) ((proposedJets (mkCtx N S B W) Q P IR p).getD i.val zeroPair).slope
      (fun t => rawSlope (q t) (a t) i) := by
  let c := mkCtx N S B W
  let oneMinus := refresh c (addC c false c.twoS 0 (neg c P))
  let plus := refresh c (addC c false c.twoS 0 IR)
  let minus := refresh c (addC c false c.twoS 0 (neg c IR))
  let yc := refresh c (addC c true c.twoS 0 (rmul c oneMinus plus))
  let xd := half c (rmul c oneMinus minus)
  have hOne : EOK c oneMinus (fun t => 1-a t) := oneSub_eok hg hP
  have hPlus : EOK c plus (fun _ => (Real.sqrt 2)⁻¹+1) :=
    refresh_eok hg (addC_eok hg hIR false (2^S) 0 1 (by simp))
  have hMinus : EOK c minus (fun _ => 1-(Real.sqrt 2)⁻¹) := oneSub_eok hg hIR
  have hYC : EOK c yc (fun t => lowC (a t)) := by
    apply (refresh_eok hg (addC_eok hg (rmul_eok hg hOne hPlus) true (2^S) 0 (-1) (by simp))).congr
    intro t _; dsimp [lowC]; ring
  have hXD : EOK c xd (fun t => lowD (a t)) := half_eok hg hS (rmul_eok hg hOne hMinus)
  have hHalf : EOK c (constTM c false (2^(S-1)) 0) (fun _ => (1:ℝ)/2) := by
    apply const_eok hg false (2^(S-1)) 0 (1/2)
    simpa using (show |(1:ℝ)/2-((2^(S-1):ℕ):ℝ)/2^S| ≤ (0:ℝ)/2^S by rw [half_scalar hS]; simp)
  have HJ := positivePair_eok hg hQ hHalf p.anchorTerms 1 2 (by omega) hq (fun t ht => by norm_num)
  have BS := positivePair_eok hg hQ hP p.heightTerms 1 3 (by omega) hq
    (fun t ht => by simpa using (low_arguments_domain (a t) (ha t ht)).1)
  have CT := positivePair_eok hg hQ hYC p.reducedCTerms 17 64 (by omega) hq
    (fun t ht => by simpa using (low_arguments_domain (a t) (ha t ht)).2.1)
  have DU := positivePair_eok hg hQ hXD p.reducedDTerms 1 8 (by omega) hq
    (fun t ht => by simpa using (low_arguments_domain (a t) (ha t ht)).2.2)
  have hW := addC_eok hg (rmul_eok hg hQ HJ.2) false (2^S) 0 1 (by simp)
  have hVA := radd_eok hg (radd_eok hg HJ.1 (rmul_eok hg (half_eok hg hS hP) HJ.2))
    (rmul_eok hg (half_eok hg hS hW) BS.1)
  have hSA := radd_eok hg HJ.2 (rmul_eok hg hW BS.2)
  have hVC := radd_eok hg (radd_eok hg HJ.1 (rmul_eok hg (half_eok hg hS hYC) HJ.2))
    (rmul_eok hg (half_eok hg hS hW) CT.1)
  have hSC := radd_eok hg HJ.2 (rmul_eok hg hW CT.2)
  fin_cases i
  · exact ⟨hVA,hSA⟩
  · exact BS
  · exact ⟨hVC,hSC⟩
  · exact DU

#print axioms proposedJets_eok
end ThomsonNegative.Compact.Target
