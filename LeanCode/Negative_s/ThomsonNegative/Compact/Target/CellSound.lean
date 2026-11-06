import ThomsonNegative.Compact.Target.CellKernel
import ThomsonNegative.Compact.Target.Sound
import ThomsonNegative.Compact.Packed.InputSound

noncomputable section
namespace ThomsonNegative.Compact.Target.Cells
open ThomsonNegative.Compact.Packed

def parameter (d : Data) (t : ℝ) : ℝ := d.centerNumerator/10+t/10
def proposed (d : Data) : ℝ → ℝ := poly context (heightInput d)
def heightFunction (d : Data) : ℝ → ℝ := extendedHeight (parameter d) (proposed d)
def polynomialFunction (d : Data) (t : ℝ) : Polynomial ℝ :=
  semanticPolynomial (parameter d t) (heightFunction d t)

theorem context_good : Good 10 384 448 1024 := by
  constructor <;> norm_num
  exact (show 11≤(2:ℕ)^4 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem gate_info {d : Data} (h : gate d=true) :
    1≤d.centerNumerator ∧ d.centerNumerator≤9 ∧ (result d).ok=true ∧
      sameTM (result d).height d.heightCheckpoint=true ∧
      sameList (result d).coefficients d.coefficientCheckpoints=true := by
  simpa only [gate,Bool.and_eq_true,Nat.ble_eq,and_assoc] using h

theorem small_ratMag (k : ℕ) (hk : k≤9) : ratMag context k 10<2^1024 := by
  change Nat.div (Nat.mul k (2^384)) 10<2^1024
  apply (Nat.div_lt_iff_lt_mul (by norm_num : 0<10)).2
  have hp : (2:ℕ)^384≤2^1024 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 := Nat.mul_lt_mul_of_pos_right (show k<10 by omega) (Nat.two_pow_pos 384)
  have h2 := Nat.mul_le_mul_left 10 hp
  change k*2^384<2^1024*10
  calc
    k*2^384 < 10*2^384 := h1
    _ ≤ 10*2^1024 := h2
    _ = 2^1024*10 := Nat.mul_comm _ _

theorem parameter_encl (d : Data) (hgate : gate d=true) :
    Encl context (parameterInput d) (parameter d) := by
  obtain ⟨hn0,hn1,hok,_,_⟩ := gate_info hgate
  have hQok := (build_flags hok).2.2.1
  let e0 : ℕ := if d.centerNumerator=5 then 0 else 1
  have hshape : parameterInput d=affineInput context (ratMag context d.centerNumerator 10)
      (ratMag context 1 10) (e0+1) := by
    unfold parameterInput
    by_cases h5 : d.centerNumerator=5 <;> simp [e0,h5]
  have hcenter : |(d.centerNumerator:ℝ)/10-(ratMag context d.centerNumerator 10:ℝ)/2^384| ≤ (e0:ℝ)/2^384 := by
    by_cases h5 : d.centerNumerator=5
    · have hh := half_scalar (S:=384) (by norm_num)
      norm_num only [Nat.reduceSub] at hh
      simp only [e0,if_pos h5,h5,centerFive_exact,Nat.cast_zero,Nat.cast_ofNat]
      change |(5:ℝ)/10-((2^383:ℕ):ℝ)/2^384| ≤ (0:ℝ)/2^384
      rw [hh]
      norm_num
    · have h := ratMag_err (N:=10) (S:=384) (B:=448) (W:=1024) (false,d.centerNumerator,10)
      simpa [e0,h5,qval,context] using h
  have hslope : |(1:ℝ)/10-(ratMag context 1 10:ℝ)/2^384| ≤ (1:ℝ)/2^384 := by
    simpa [qval,context] using ratMag_err (N:=10) (S:=384) (B:=448) (W:=1024) (false,1,10)
  rw [hshape] at hQok ⊢
  have h := affineInput_sound context_good _ _ e0 1 (d.centerNumerator/10) (1/10)
    (small_ratMag _ hn1) (small_ratMag 1 (by norm_num)) (by norm_num)
    hcenter (by simpa using hslope) hQok
  exact h.congr (fun t _ => by unfold parameter; ring)

theorem proposed_encl (d : Data) (hgate : gate d=true) :
    Encl context (heightInput d) (proposed d) := by
  have hok := (build_flags (gate_info hgate).2.2.1).2.2.2.1
  exact ofPQ_poly_sound context_good d.heightPositive d.heightNegative 0 hok

theorem parameter_domain (d : Data) (hgate : gate d=true) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    parameter d t ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : (1:ℝ)≤d.centerNumerator := by exact_mod_cast (gate_info hgate).1
  have hn1 : (d.centerNumerator:ℝ)≤9 := by exact_mod_cast (gate_info hgate).2.1
  unfold parameter
  constructor <;> linarith [ht.1,ht.2]

theorem sameTM_eq {x y : TM} (h : sameTM x y=true) : x=y := by
  cases x with
  | mk xv xa xs xe xo =>
    cases y with
    | mk yv ya ys ye yo =>
      have hh : xv=yv ∧ xa=ya ∧ xs=ys ∧ xe=ye ∧ xo=yo := by simpa [sameTM,and_assoc] using h
      rcases hh with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl

theorem sameList_eq {L R : List TM} (h : sameList L R=true) : L=R := by
  induction L generalizing R with
  | nil => cases R <;> simp_all [sameList]
  | cons x xs ih =>
    cases R with
    | nil => simp [sameList] at h
    | cons y ys =>
      simp only [sameList,Bool.and_eq_true] at h
      rw [sameTM_eq h.1,ih h.2]

theorem checkpoints (d : Data) (hgate : gate d=true) :
    (result d).height=d.heightCheckpoint ∧ (result d).coefficients=d.coefficientCheckpoints :=
  ⟨sameTM_eq (gate_info hgate).2.2.2.1,sameList_eq (gate_info hgate).2.2.2.2⟩

theorem height_encl (d : Data) (hgate : gate d=true) :
    Encl context d.heightCheckpoint (heightFunction d) := by
  rw [← (checkpoints d hgate).1]
  exact (build_root_sound context_good (parameter_encl d hgate) (proposed_encl d hgate)
    (parameter_domain d hgate) d.inverseSqrtTwo defaultParameters (gate_info hgate).2.2.1).2.2.2

theorem coefficient_encl (d : Data) (hgate : gate d=true) (i : ℕ) (hi : i<8) :
    Encl context (d.coefficientCheckpoints.getD i zeroTM) (fun t => (polynomialFunction d t).coeff i) := by
  rw [← (checkpoints d hgate).2]
  exact (build_coefficients_sound context_good (parameter_encl d hgate) (proposed_encl d hgate)
    (parameter_domain d hgate) d.inverseSqrtTwo defaultParameters (gate_info hgate).2.2.1).2 i hi

theorem height_range (d : Data) (hgate : gate d=true) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    heightFunction d t ∈ Set.Ioo (5/16:ℝ) (1/3) := by
  have hp := (build_root_sound context_good (parameter_encl d hgate) (proposed_encl d hgate)
    (parameter_domain d hgate) d.inverseSqrtTwo defaultParameters (gate_info hgate).2.2.1).1
  exact extendedHeight_range (parameter d) (proposed d) hp t ht

theorem interior_bridge (d : Data) (t : ℝ) (hq : parameter d t ∈ Set.Ioo (0:ℝ) 1) :
    heightFunction d t=aStar (2*parameter d t-2) ∧
    polynomialFunction d t=Geometry.hermiteH7 (parameter d t)
      (sourceContact (aStar (2*parameter d t-2))) :=
  ⟨extendedHeight_interior (parameter d) (proposed d) t hq,
    semanticPolynomial_at_root (parameter d) (proposed d) t hq⟩

#print axioms height_encl
#print axioms coefficient_encl
end ThomsonNegative.Compact.Target.Cells
