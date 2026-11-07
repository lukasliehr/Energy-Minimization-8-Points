import ThomsonNegative.Structure.Factored.HighIdentities
import ThomsonNegative.Structure.Factored.LowSystem
import ThomsonNegative.Structure.Coordinates

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Factored
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed

def lowIndex (i : Fin 51) : Fin 68 := ⟨i.val,by omega⟩
def midIndex (i : Fin 14) : Fin 68 := ⟨51+i.val,by omega⟩
def topIndex (i : Fin 3) : Fin 68 := ⟨65+i.val,by omega⟩

def lowRows : ChartSpace →ₗ[ℝ] (Fin 51 → ℝ) where
  toFun x i := x (lowIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def midRows : ChartSpace →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun x i := x (midIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def topRows : ChartSpace →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x (topIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def padLow : (Fin 51 → ℝ) →ₗ[ℝ] ChartSpace where
  toFun x i := if h : i.val<51 then x ⟨i.val,h⟩ else 0
  map_add' _ _ := by funext i; dsimp; split <;> simp_all
  map_smul' _ _ := by funext i; dsimp; split <;> simp_all

lemma index_cases (i : Fin 68) :
    (∃j,lowIndex j=i) ∨ (∃j,midIndex j=i) ∨ (∃j,topIndex j=i) := by
  by_cases h : i.val<51
  · exact Or.inl ⟨⟨i.val,h⟩,rfl⟩
  · by_cases hh : i.val<65
    · exact Or.inr (Or.inl ⟨⟨i.val-51,by omega⟩,Fin.ext (by simp [midIndex];omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨i.val-65,by omega⟩,Fin.ext (by simp [topIndex];omega)⟩)

lemma padLow_eq_of_zero (x : ChartSpace) (hm : midRows x=0) (ht : topRows x=0) :
    padLow (lowRows x)=x := by
  funext i
  rcases index_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
  · simp [padLow,lowRows,lowIndex,j.isLt]
  · have h := congrFun hm j
    change x (midIndex j)=0 at h
    change (if h : 51+j.val<51 then _ else 0)=_
    rw [dif_neg (by omega)]
    exact h.symm
  · have h := congrFun ht j
    change x (topIndex j)=0 at h
    change (if h : 65+j.val<51 then _ else 0)=_
    rw [dif_neg (by omega)]
    exact h.symm

theorem H3_top_words : ∀ i j : Fin 3,
    HighData.H3.numerator (65+i.val) j.val=
      if i=j then HighData.H3.denominator else zeroRecord := by decide +kernel

theorem H14_mid_words : ∀ i j : Fin 14,
    HighData.H14.numerator (51+i.val) j.val=
      if i=j then HighData.H14.denominator else zeroRecord := by decide +kernel

theorem H14_top_words : ∀ (i : Fin 3) (j : Fin 14),
    HighData.H14.numerator (65+i.val) j.val=zeroRecord := by decide +kernel

theorem LP_upper_words : ∀ (i : Fin 17) (j : Fin 15),
    HighData.LP.numerator (51+i.val) j.val=zeroRecord := by decide +kernel

theorem LS_upper_words : ∀ (i : Fin 17) (j : Fin 36),
    HighData.LS.numerator (51+i.val) j.val=zeroRecord := by decide +kernel

theorem H3_top (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : Fin 3 → ℝ) :
    topRows ((HighData.H3.eval a).mulVec x)=x := by
  have hn := H3_regular a ha hb
  funext i
  change (∑ j, (HighData.H3.eval a) (topIndex i) j * x j)=x i
  have hh (j : Fin 3) : (HighData.H3.eval a) (topIndex i) j=if i=j then 1 else 0 := by
    simp only [EncodedMatrix.eval,topIndex,H3_top_words]
    split <;> simp_all [zeroRecord_decode,evalZ,horner,EncodedMatrix.RegularAt]
  simp [hh]

theorem H14_mid (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : Fin 14 → ℝ) :
    midRows ((HighData.H14.eval a).mulVec x)=x := by
  have hn := H14_regular a ha hb
  funext i
  change (∑ j, (HighData.H14.eval a) (midIndex i) j * x j)=x i
  have hh (j : Fin 14) : (HighData.H14.eval a) (midIndex i) j=if i=j then 1 else 0 := by
    simp only [EncodedMatrix.eval,midIndex,H14_mid_words]
    split <;> simp_all [zeroRecord_decode,evalZ,horner,EncodedMatrix.RegularAt]
  simp [hh]

theorem H14_top (a : ℝ) (x : Fin 14 → ℝ) :
    topRows ((HighData.H14.eval a).mulVec x)=0 := by
  funext i
  change (∑ j, (HighData.H14.eval a) (topIndex i) j * x j)=0
  simp [EncodedMatrix.eval,topIndex,H14_top_words,zeroRecord_decode,evalZ,horner]

theorem LP_eval (a : ℝ) (x : Fin 15 → ℝ) :
    (HighData.LP.eval a).mulVec x=padLow ((Data.P.eval a).mulVec x) := by
  funext i
  by_cases h : i.val<51
  · simp only [padLow,LinearMap.coe_mk,AddHom.coe_mk,dif_pos h]
    rfl
  · have hi : i.val=51+(i.val-51) := by omega
    have hzero (j : Fin 15) : HighData.LP.numerator i.val j.val=zeroRecord := by
      rw [hi]
      exact LP_upper_words ⟨i.val-51,by omega⟩ j
    simp [Matrix.mulVec,dotProduct,EncodedMatrix.eval,hzero,padLow,h,
      zeroRecord_decode,evalZ,horner]

theorem LS_eval (a : ℝ) (x : Fin 36 → ℝ) :
    (HighData.LS.eval a).mulVec x=padLow ((Data.S.eval a).mulVec x) := by
  funext i
  by_cases h : i.val<51
  · simp only [padLow,LinearMap.coe_mk,AddHom.coe_mk,dif_pos h]
    rfl
  · have hi : i.val=51+(i.val-51) := by omega
    have hzero (j : Fin 36) : HighData.LS.numerator i.val j.val=zeroRecord := by
      rw [hi]
      exact LS_upper_words ⟨i.val-51,by omega⟩ j
    simp [Matrix.mulVec,dotProduct,EncodedMatrix.eval,hzero,padLow,h,
      zeroRecord_decode,evalZ,horner]

def solve3 (a : ℝ) : ChartSpace →ₗ[ℝ] (Fin 3 → ℝ) := topRows

def residual3 (a : ℝ) : ChartSpace →ₗ[ℝ] ChartSpace :=
  LinearMap.id-(Matrix.toLin' (HighData.H3.eval a)).comp (solve3 a)

def solve14 (a : ℝ) : ChartSpace →ₗ[ℝ] (Fin 14 → ℝ) := midRows.comp (residual3 a)

def residual14 (a : ℝ) : ChartSpace →ₗ[ℝ] ChartSpace :=
  residual3 a-(Matrix.toLin' (HighData.H14.eval a)).comp (solve14 a)

def solve15 (a : ℝ) : ChartSpace →ₗ[ℝ] (Fin 15 → ℝ) :=
  (Matrix.toLin' (Data.MI.eval a)).comp
    ((Matrix.toLin' (Data.J.eval a)).comp (lowRows.comp (residual14 a)))

def solve36 (a : ℝ) : ChartSpace →ₗ[ℝ] (Fin 36 → ℝ) :=
  (Matrix.toLin' (Data.SI.eval a)).comp
    (scalarRows.comp (lowRows.comp (residual14 a)-
      (Matrix.toLin' (Data.P.eval a)).comp (solve15 a)))

/-- The exact 3+14+15+36 repair, without any numerical inversion. -/
def operatorRepair (a : ℝ) : ChartSpace →ₗ[ℝ] (Fin 68 → ℝ) :=
  (Matrix.toLin' (HighData.K3.eval a)).comp (solve3 a)+
  (Matrix.toLin' (HighData.K14.eval a)).comp (solve14 a)+
  (Matrix.toLin' (HighData.K15.eval a)).comp (solve15 a)+
  (Matrix.toLin' (HighData.K36.eval a)).comp (solve36 a)

theorem residual3_top (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : ChartSpace) :
    topRows (residual3 a x)=0 := by
  change topRows (x-(HighData.H3.eval a).mulVec (topRows x))=0
  rw [map_sub,H3_top a ha hb,sub_self]

theorem residual14_mid (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : ChartSpace) :
    midRows (residual14 a x)=0 := by
  change midRows (residual3 a x-(HighData.H14.eval a).mulVec (midRows (residual3 a x)))=0
  rw [map_sub,H14_mid a ha hb,sub_self]

theorem residual14_top (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (x : ChartSpace) :
    topRows (residual14 a x)=0 := by
  change topRows (residual3 a x-(HighData.H14.eval a).mulVec (solve14 a x))=0
  rw [map_sub,residual3_top a ha hb,H14_top,sub_zero]

theorem operatorRepair_right_inverse (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (x : ChartSpace) : (HighData.A.eval a).mulVec (operatorRepair a x)=x := by
  have hl := lowStage_recovery a ha hb (lowRows (residual14 a x))
  change (Data.P.eval a).mulVec (solve15 a x)+
    (Data.S.eval a).mulVec (solve36 a x)=lowRows (residual14 a x) at hl
  have hlift := congrArg padLow hl
  rw [map_add,← LP_eval,← LS_eval,
    padLow_eq_of_zero _ (residual14_mid a ha hb x) (residual14_top a ha hb x)] at hlift
  change (HighData.A.eval a).mulVec
    (((HighData.K3.eval a).mulVec (solve3 a x)+
    (HighData.K14.eval a).mulVec (solve14 a x)+
    (HighData.K15.eval a).mulVec (solve15 a x))+
    (HighData.K36.eval a).mulVec (solve36 a x))=x
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec,
    high3_identity a ha hb,high14_identity a ha hb,insert15_identity a ha hb,insert36_identity a ha hb]
  simp only [add_assoc]
  rw [hlift]
  change (HighData.H3.eval a).mulVec (solve3 a x)+
    ((HighData.H14.eval a).mulVec (solve14 a x)+
      (x-(HighData.H3.eval a).mulVec (solve3 a x)-
        (HighData.H14.eval a).mulVec (solve14 a x)))=x
  abel

#print axioms operatorRepair_right_inverse
end ThomsonNegative.Structure.Factored
