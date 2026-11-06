import AllS.Units.N_FI.N_exclude_six.N_type_coordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def sixTypes : Fin 6 → Fin 3 × Fin 3 := ![(0,1),(1,0),(0,2),(2,0),(1,2),(2,1)]
def sixU (a : ℝ) (k : Fin 6) : ℝ := bContacts a (sixTypes k).1
def sixV (a : ℝ) (k : Fin 6) : ℝ := bContacts a (sixTypes k).2
def bpairP (a : ℝ) : ℝ := (contacts a 0+contacts a 2)/(2*√a)
def sixFirst (a : ℝ) (k : Fin 6) : ℝ := (sixU a k+sixV a k)/(2*√a)
def sixSecond (a : ℝ) (k : Fin 6) : ℝ := (sixU a k-sixV a k)/(2*√(1-a))
def SixTypeNorms (a : ℝ) (xi : Fin 6 → ℝ) : Prop :=
  ∀ k, (sixFirst a k)^2+(sixSecond a k)^2+(xi k)^2=1

theorem bpairP_square (a : ℝ) (ha0 : 0 < a) : (bpairP a)^2=(1-a)^2/(8*a) := by
  have hs := Real.sq_sqrt ha0.le
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsum : contacts a 0+contacts a 2=(1-a)/√2 := by dsimp [contacts]; ring
  rw [bpairP,div_pow,hsum,div_pow,mul_pow,hs,hs2]
  ring

theorem bpairP_square_gap (a : ℝ) (ha : physical a) :
    a-(bpairP a)^2=(7*a^2+2*a-1)/(8*a) ∧ (bpairP a)^2 < a := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hpos := (contact_order_packing_bounds a ha.1 ha.2).2
  have he : a-(bpairP a)^2=(7*a^2+2*a-1)/(8*a) := by
    rw [bpairP_square a ha0]
    field_simp
    ring
  exact ⟨he,by have hp : 0 < (7*a^2+2*a-1)/(8*a) := div_pos hpos (by positivity); linarith⟩

theorem sixFirst_entries (a : ℝ) (ha0 : 0 < a) :
    sixFirst a= ![bpairP a,bpairP a,-bpairP a,-bpairP a,-√a,-√a] := by
  have hs := Real.sq_sqrt ha0.le
  have hn : √a ≠ 0 := (Real.sqrt_pos.mpr ha0).ne'
  have hCD : ((-a+(1-a)/√2)+(-a-(1-a)/√2))/(2*√a)= -√a := by
    calc
      _ = (-2*a)/(2*√a) := by congr 1; ring
      _ = _ := by field_simp; nlinarith
  funext k
  fin_cases k
  all_goals dsimp [sixFirst,sixU,sixV,sixTypes,bContacts,bContactIndex,bpairP,contacts]
  all_goals ring_nf
  all_goals field_simp
  all_goals nlinarith

theorem exclude_six_linear_tensor_reduction (a : ℝ) (ha : physical a) (xi : Fin 6 → ℝ)
    (hcent : (∑ k, xi k)=0) (hmixed : (∑ k, (sixFirst a k)^2*xi k)=0) :
    xi 4+xi 5=0 ∧ (xi 0+xi 1)+(xi 2+xi 3)=0 := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hgap := (bpairP_square_gap a ha).2
  have hs := Real.sq_sqrt ha0.le
  rw [sixFirst_entries a ha0] at hmixed
  rw [Fin.sum_univ_six] at hcent hmixed
  change (bpairP a)^2*xi 0+(bpairP a)^2*xi 1+(-bpairP a)^2*xi 2+
    (-bpairP a)^2*xi 3+(-√a)^2*xi 4+(-√a)^2*xi 5=0 at hmixed
  rw [neg_sq,neg_sq,hs] at hmixed
  have hprod : (a-(bpairP a)^2)*(xi 4+xi 5)=0 := by
    linear_combination hmixed-(bpairP a)^2*hcent
  have hz := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hgap.ne')
  exact ⟨hz,by linarith⟩

#check exclude_six_linear_tensor_reduction
#print axioms exclude_six_linear_tensor_reduction
end Blueprint.Thomson.Finite
