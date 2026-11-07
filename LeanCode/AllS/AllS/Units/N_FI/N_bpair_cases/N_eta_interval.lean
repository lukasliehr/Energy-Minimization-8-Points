import AllS.Units.N_F.N_contact_order

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def bpairU (a : ℝ) : ℝ := -3*(contacts a 0+contacts a 2)*(contacts a 0-contacts a 2)^2
def bpairV (a : ℝ) : ℝ := -3*(contacts a 0+contacts a 3)*(contacts a 0-contacts a 3)^2
def bpairW (a : ℝ) : ℝ := 12*a*(1-a)^2
def bpairEta (a : ℝ) : ℝ := -bpairU a/bpairW a

theorem bpair_UVW_identities (a : ℝ) :
    bpairU a+bpairV a=bpairW a ∧
    bpairW a= -3*(contacts a 2+contacts a 3)*(contacts a 2-contacts a 3)^2 ∧
    bpairW a=6*a*(contacts a 2-contacts a 3)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  dsimp [bpairU,bpairV,bpairW,contacts]
  simp only [div_eq_mul_inv,hinv]
  refine ⟨?_,?_,?_⟩
  · linear_combination 6*a*(a-1)^2*hs
  · linear_combination -6*a*(a-1)^2*hs
  · linear_combination -6*a*(a-1)^2*hs

theorem bpair_UW_signs (a : ℝ) (ha : physical a) : bpairU a < 0 ∧ 0 < bpairW a := by
  obtain ⟨_,_,_,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  constructor
  · unfold bpairU
    have hp : 0 < contacts a 0+contacts a 2 := by linarith
    have hd : 0 < (contacts a 0-contacts a 2)^2 := sq_pos_of_pos (sub_pos.mpr hCA)
    nlinarith [mul_pos hp hd]
  · unfold bpairW
    positivity

theorem bpair_cases_eta_interval (a : ℝ) (ha : physical a) :
    bpairEta a=(contacts a 0+contacts a 2)/(2*a)*
      ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 ∧
    0 < bpairEta a ∧ bpairEta a < 1 := by
  obtain ⟨_,hDB,hB,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hCD : 0 < contacts a 2-contacts a 3 := by linarith
  have heq : bpairEta a=(contacts a 0+contacts a 2)/(2*a)*
      ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 := by
    rw [bpairEta,(bpair_UVW_identities a).2.2]
    dsimp [bpairU]
    field_simp
    ring
  have hfirst0 : 0 < (contacts a 0+contacts a 2)/(2*a) := div_pos (by linarith) (by positivity)
  have hfirst1 : (contacts a 0+contacts a 2)/(2*a) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*a)).mpr
    change a+contacts a 2 < 2*a
    change contacts a 2 < a at hCA
    linarith
  have hratio0 : 0 < (contacts a 0-contacts a 2)/(contacts a 2-contacts a 3) :=
    div_pos (sub_pos.mpr hCA) hCD
  have hCDlo : 1-a < contacts a 2-contacts a 3 := by
    have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
    have hn : √(2:ℝ) ≠ 0 := by positivity
    have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
    have hslo : 1 < √(2:ℝ) := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
    have hp := mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hslo)
    change 1-a < (-a+(1-a)/√2)-(-a-(1-a)/√2)
    simp only [div_eq_mul_inv,hinv]
    nlinarith
  have hratio1 : (contacts a 0-contacts a 2)/(contacts a 2-contacts a 3) < 1 := by
    apply (div_lt_one hCD).mpr
    change a-contacts a 2 < contacts a 2-contacts a 3
    linarith [ha.2]
  have hsquare : ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 < 1 := by nlinarith
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    exact mul_pos hfirst0 (sq_pos_of_pos hratio0)
  · rw [heq]
    nlinarith [mul_pos (sub_pos.mpr hfirst1) (sq_pos_of_pos hratio0)]

#check bpair_cases_eta_interval
#print axioms bpair_cases_eta_interval
end Blueprint.Thomson.Finite
