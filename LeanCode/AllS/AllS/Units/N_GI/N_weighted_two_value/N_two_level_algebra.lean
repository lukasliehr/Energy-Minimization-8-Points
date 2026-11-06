import AllS.Units.N_GI.N_weighted_two_value.N_at_most_two

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def weightedLevelMass {n : ℕ} (w x : Fin n → ℝ) (l : ℝ) : ℝ :=
  ∑ i, if x i=l then w i else 0

def weightedNegativeMass {n : ℕ} (w x : Fin n → ℝ) : ℝ := ∑ i, if x i<0 then w i else 0

def twoValueExp (W v z : ℝ) : ℝ :=
  z*exp (-v*√((W-z)/(W*z)))+(W-z)*exp (v*√(z/(W*(W-z))))

theorem sum_of_two_levels {n : ℕ} (w x : Fin n → ℝ) (l h : ℝ)
    (hh : l ≠ h) (hx : ∀ i, x i=l ∨ x i=h) (f : ℝ → ℝ) :
    (∑ i,w i*f (x i))=weightedLevelMass w x l*f l+
      ((∑ i,w i)-weightedLevelMass w x l)*f h := by
  simp only [weightedLevelMass,sub_mul,Finset.sum_mul,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases hx i with hi|hi
  · simp [hi]
  · simp [hi,Ne.symm hh]

theorem level_masses_positive {n : ℕ} (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (il ih : Fin n) (hh : x il ≠ x ih) :
    0 < weightedLevelMass w x (x il) ∧
    0 < (∑ i,w i)-weightedLevelMass w x (x il) := by
  have hn (i : Fin n) : 0 ≤ if x i=x il then w i else 0 := by split_ifs; exact (hw i).le; norm_num
  have hlo := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hn i)
    (Finset.mem_univ il)
  simp only [if_pos rfl] at hlo
  have hcomp : (∑ i,w i)-weightedLevelMass w x (x il)=
      ∑ i,if x i=x il then 0 else w i := by
    unfold weightedLevelMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring
  have hnn (i : Fin n) : 0 ≤ if x i=x il then 0 else w i := by split_ifs; norm_num; exact (hw i).le
  have hhi := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hnn i)
    (Finset.mem_univ ih)
  simp only [if_neg (Ne.symm hh)] at hhi
  exact ⟨lt_of_lt_of_le (hw il) hlo,by rw [hcomp]; exact lt_of_lt_of_le (hw ih) hhi⟩

theorem two_level_values (W z v l h : ℝ) (hz : 0 < z) (hk : 0 < W-z)
    (hv : 0 < v) (hlh : l < h) (hm : z*l+(W-z)*h=0)
    (hq : z*l^2+(W-z)*h^2=v^2) :
    l < 0 ∧ 0 < h ∧ l=-v*√((W-z)/(W*z)) ∧ h=v*√(z/(W*(W-z))) := by
  have hW : 0 < W := by linarith
  have hl : l < 0 := by
    have hp := mul_pos hk (sub_pos.mpr hlh)
    have hw : W*l < 0 := by nlinarith
    exact neg_of_mul_neg_right hw hW.le
  have hh : 0 < h := by
    have hp := mul_pos hz (sub_pos.mpr hlh)
    have hw : 0 < W*h := by nlinarith
    exact pos_of_mul_pos_right hw hW.le
  have hlsq : l^2=v^2*((W-z)/(W*z)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (by positivity)).mpr
    linear_combination (W-z)*hq-((W-z)*h-z*l)*hm
  have hhsq : h^2=v^2*(z/(W*(W-z))) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (by positivity)).mpr
    linear_combination z*hq-(z*l-(W-z)*h)*hm
  have hradl : 0 ≤ (W-z)/(W*z) := by positivity
  have hradh : 0 ≤ z/(W*(W-z)) := by positivity
  have hsl := Real.sq_sqrt hradl
  have hsh := Real.sq_sqrt hradh
  have hnsl := Real.sqrt_nonneg ((W-z)/(W*z))
  have hnsh := Real.sqrt_nonneg (z/(W*(W-z)))
  refine ⟨hl,hh,?_,?_⟩
  · have he : (v*√((W-z)/(W*z)))^2=l^2 := by rw [mul_pow,hsl,hlsq]
    have hp : 0 ≤ v*√((W-z)/(W*z)) := by positivity
    nlinarith
  · have he : (v*√(z/(W*(W-z))))^2=h^2 := by rw [mul_pow,hsh,hhsq]
    have hp : 0 ≤ v*√(z/(W*(W-z))) := by positivity
    nlinarith

#print axioms sum_of_two_levels
#print axioms two_level_values
end Blueprint.Thomson.Tail.Implementation
