import ThomsonNegative.Compact.Target.BuildRootSound
import ThomsonNegative.Geometry.Contacts
import ThomsonNegative.Geometry.ConfluentCongr

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

def sourcePermutation : Equiv.Perm (Fin 4) := Equiv.swap 1 2
@[simp] theorem sourcePermutation_zero : sourcePermutation 0=0 := by decide
@[simp] theorem sourcePermutation_one : sourcePermutation 1=2 := by decide
@[simp] theorem sourcePermutation_two : sourcePermutation 2=1 := by decide
@[simp] theorem sourcePermutation_three : sourcePermutation 3=3 := by decide
def sourceContact (a : ℝ) : Fin 4 → ℝ := ![a,lowC a,2*a-1,2*lowD a-1]
def sourceContactNat (a : ℝ) (l : ℕ) : ℝ := if h : l<4 then sourceContact a ⟨l,h⟩ else -1
def sourceValue (q a : ℝ) (i : Fin 4) : ℝ := rawValue q a (sourcePermutation i)
def sourceSlope (q a : ℝ) (i : Fin 4) : ℝ := rawSlope q a (sourcePermutation i)/2

theorem sourceContact_eq_contacts (a : ℝ) :
    sourceContact a=Geometry.contacts a ∘ sourcePermutation := by
  funext i
  fin_cases i
  · change a=Geometry.contacts a (sourcePermutation 0)
    rw [sourcePermutation_zero]; rfl
  · change lowC a=Geometry.contacts a (sourcePermutation 1)
    rw [sourcePermutation_one]
    change lowC a = -a+(1-a)/Real.sqrt 2
    unfold lowC; rw [div_eq_mul_inv]; ring
  · change 2*a-1=Geometry.contacts a (sourcePermutation 2)
    rw [sourcePermutation_two]; rfl
  · change 2*lowD a-1=Geometry.contacts a (sourcePermutation 3)
    rw [sourcePermutation_three]
    change 2*lowD a-1= -a-(1-a)/Real.sqrt 2
    unfold lowD; rw [div_eq_mul_inv]; ring

theorem sourceContactX (a : ℝ) (i : Fin 4) :
    contactX a (sourcePermutation i)=(1+sourceContact a i)/2 := by
  fin_cases i
  · change contactX a (sourcePermutation 0)=(1+sourceContact a 0)/2
    rw [sourcePermutation_zero]; rfl
  · change contactX a (sourcePermutation 1)=(1+sourceContact a 1)/2
    rw [sourcePermutation_one]; rfl
  · change contactX a (sourcePermutation 2)=(1+sourceContact a 2)/2
    rw [sourcePermutation_two]
    change a=(1+(2*a-1))/2; ring
  · change contactX a (sourcePermutation 3)=(1+sourceContact a 3)/2
    rw [sourcePermutation_three]
    change lowD a=(1+(2*lowD a-1))/2; ring

theorem narrow_physical (a : ℝ) (ha : a ∈ Set.Ioo (5/16:ℝ) (1/3)) : Geometry.physical a := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hb : Real.sqrt (2:ℝ)<3/2 := by nlinarith
  have hi : Geometry.aInf < (5:ℝ)/16 := by
    unfold Geometry.aInf limitingHeight
    linarith
  exact ⟨hi.trans ha.1,ha.2⟩

theorem sourceContact_injective (a : ℝ) (ha : a ∈ Set.Ioo (5/16:ℝ) (1/3)) :
    Function.Injective (sourceContact a) := by
  rw [sourceContact_eq_contacts]
  exact (Geometry.contacts_injective a (narrow_physical a ha)).comp sourcePermutation.injective

def jetEntry (k : ℕ) (v s : ℝ) : ℝ := if k=0 then v else if k=1 then s else 0
def suppliedJet (q a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if x=sourceContact a 0 then jetEntry k (sourceValue q a 0) (sourceSlope q a 0)
  else if x=sourceContact a 1 then jetEntry k (sourceValue q a 1) (sourceSlope q a 1)
  else if x=sourceContact a 2 then jetEntry k (sourceValue q a 2) (sourceSlope q a 2)
  else jetEntry k (sourceValue q a 3) (sourceSlope q a 3)

theorem suppliedJet_at (q a : ℝ) (hz : Function.Injective (sourceContact a)) (i : Fin 4) (k : ℕ) :
    suppliedJet q a k (sourceContact a i)=jetEntry k (sourceValue q a i) (sourceSlope q a i) := by
  fin_cases i <;> simp [suppliedJet,hz.eq_iff]

theorem suppliedJet_interior (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Ioo (5/16:ℝ) (1/3)) (i : Fin 4) (k : ℕ) (hk : k<2) :
    suppliedJet q a k (sourceContact a i)=Analytic.auxiliaryTJet q k (sourceContact a i) := by
  rw [suppliedJet_at q a (sourceContact_injective a ha)]
  have h := rawJets_interior q a hq ⟨ha.1.le,ha.2.le⟩ (sourcePermutation i)
  rw [sourceContactX] at h
  interval_cases k
  · simpa [jetEntry,sourceValue,Analytic.auxiliaryTJet,Analytic.auxiliaryJet,Analytic.auxiliaryT] using h.1
  · simpa [jetEntry,sourceSlope,Analytic.auxiliaryTJet,Analytic.auxiliaryJet,div_eq_mul_inv,mul_comm]
      using congrArg (fun x : ℝ => x/2) h.2

/-- Whole-cell semantic polynomial, with arbitrary but consistent endpoint
jets. On the requested open q interval it is exactly the analytic H7. -/
def semanticPolynomial (q a : ℝ) : Polynomial ℝ :=
  Geometry.sourceNewtonHorner (Geometry.doubleNode (sourceContact a))
    (fun i => Geometry.confluentTable (Geometry.doubleNode (sourceContact a)) (suppliedJet q a) i 0) 8 0

theorem semanticPolynomial_interior (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Ioo (5/16:ℝ) (1/3)) :
    semanticPolynomial q a=Geometry.hermiteH7 q (sourceContact a) := by
  have hz := sourceContact_injective a ha
  unfold semanticPolynomial
  rw [Geometry.sourceNewtonHorner_double_congr (sourceContact a) hz (suppliedJet q a)
    (Analytic.auxiliaryTJet q) (suppliedJet_interior q a hq ha)]
  exact Geometry.sourceNewtonHorner_hermiteH7 q (sourceContact a) hz

theorem sourceNodes_eok (hg : Good N S B W) {IR A : TM} {a : ℝ → ℝ}
    (hIR : EOK (mkCtx N S B W) IR (fun _ => (Real.sqrt 2)⁻¹))
    (hA : EOK (mkCtx N S B W) A a) (l : ℕ) (hl : l<4) :
    EOK (mkCtx N S B W) ((sourceNodes (mkCtx N S B W) IR A).getD l zeroTM)
      (fun t => sourceContactNat (a t) l) := by
  have hOne := addC_eok hg (neg_eok hA rfl) false (2^S) 0 1 (by simp)
  have hW := rmul_eok hg hIR hOne
  have h0 := refresh_eok hg hA
  have h1 := radd_eok hg (neg_eok hA rfl) hW
  have h2 := refresh_eok hg (addC_eok hg (add_eok hA hA rfl) true (2^S) 0 (-1) (by simp))
  have h3 := refresh_eok hg (neg_eok (add_eok hA hW rfl) rfl)
  interval_cases l
  · exact h0.congr (fun t _ => rfl)
  · apply h1.congr
    intro t _; dsimp [sourceContactNat,sourceContact,lowC]; ring
  · apply h2.congr
    intro t _; dsimp [sourceContactNat,sourceContact]; ring
  · apply h3.congr
    intro t _; dsimp [sourceContactNat,sourceContact,lowD]; ring

#print axioms semanticPolynomial_interior
#print axioms sourceNodes_eok
end ThomsonNegative.Compact.Target
