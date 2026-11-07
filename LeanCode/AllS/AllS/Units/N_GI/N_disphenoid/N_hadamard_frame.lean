import AllS.Units.N_GI.N_disphenoid.N_centroid_zero

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def hadamardG (A : Fin 4 → Point) : Point := (1/4:ℝ) • (A 0+A 1+A 2+A 3)
def hadamardU (A : Fin 4 → Point) : Point := (1/4:ℝ) • (A 0+A 1-A 2-A 3)
def hadamardV (A : Fin 4 → Point) : Point := (1/4:ℝ) • (A 0-A 1+A 2-A 3)
def hadamardW (A : Fin 4 → Point) : Point := (1/4:ℝ) • (A 0-A 1-A 2+A 3)

theorem hadamard_half_pairs (A : Fin 4 → Point) (h : ∑i,A i=0) :
    hadamardU A=(1/2:ℝ) • (A 0+A 1) ∧
    hadamardV A=(1/2:ℝ) • (A 0+A 2) ∧
    hadamardW A=(1/2:ℝ) • (A 0+A 3) := by
  have hu : hadamardU A=(1/2:ℝ) • (A 0+A 1)-(1/4:ℝ) • (∑i,A i) := by
    rw [Fin.sum_univ_four];unfold hadamardU;module
  have hv : hadamardV A=(1/2:ℝ) • (A 0+A 2)-(1/4:ℝ) • (∑i,A i) := by
    rw [Fin.sum_univ_four];unfold hadamardV;module
  have hw : hadamardW A=(1/2:ℝ) • (A 0+A 3)-(1/4:ℝ) • (∑i,A i) := by
    rw [Fin.sum_univ_four];unfold hadamardW;module
  simpa only [h,smul_zero,sub_zero] using And.intro hu (And.intro hv hw)

theorem disphenoid_hadamard_frame (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    hadamardG A=0 ∧ inner ℝ (hadamardU A) (hadamardV A)=0 ∧
    inner ℝ (hadamardU A) (hadamardW A)=0 ∧ inner ℝ (hadamardV A) (hadamardW A)=0 ∧
    hadamardU A≠0 ∧ hadamardV A≠0 ∧ hadamardW A≠0 := by
  obtain ⟨d01,d02,d03⟩ := disphenoid_opposite_lengths A B c hc hAunit hBunit hAinj hBinj hcross hmatched
  have h01 := unit_dist_eq_inner_eq _ _ _ _ (hAunit 0) (hAunit 1) (hAunit 2) (hAunit 3) d01
  have h02 := unit_dist_eq_inner_eq _ _ _ _ (hAunit 0) (hAunit 2) (hAunit 1) (hAunit 3) d02
  have h03 := unit_dist_eq_inner_eq _ _ _ _ (hAunit 0) (hAunit 3) (hAunit 1) (hAunit 2) d03
  obtain ⟨w,_,hw,hwA,_⟩ := polar_tetrahedra_positive_relation A B c hAunit hAinj hBinj hc hcross hmatched
  have hsum := disphenoid_sum_zero A hAunit h01 h02 h03 w hw hwA
  obtain ⟨hu,hv,hw⟩ := hadamard_half_pairs A hsum
  have hG : hadamardG A=0 := by
    unfold hadamardG
    rw [←Fin.sum_univ_four,hsum,smul_zero]
  have hii : inner ℝ (A 0) (A 0)=1 := by rw [real_inner_self_eq_norm_sq,hAunit];norm_num
  have h10 : inner ℝ (A 1) (A 0)=inner ℝ (A 0) (A 1) := real_inner_comm _ _
  have h20 : inner ℝ (A 2) (A 0)=inner ℝ (A 0) (A 2) := real_inner_comm _ _
  have hS : 1+inner ℝ (A 0) (A 1)+inner ℝ (A 0) (A 2)+inner ℝ (A 0) (A 3)=0 := by
    have hh := congrArg (fun x => inner ℝ (A 0) x) hsum
    simpa only [inner_sum,Fin.sum_univ_four,inner_add_right,hii,inner_zero_right] using hh
  have huv : inner ℝ (hadamardU A) (hadamardV A)=0 := by
    rw [hu,hv]
    simp only [inner_smul_left,inner_smul_right,conj_trivial,inner_add_left,inner_add_right,hii,h10]
    nlinarith
  have huw : inner ℝ (hadamardU A) (hadamardW A)=0 := by
    rw [hu,hw]
    simp only [inner_smul_left,inner_smul_right,conj_trivial,inner_add_left,inner_add_right,hii,h10]
    nlinarith
  have hvw : inner ℝ (hadamardV A) (hadamardW A)=0 := by
    rw [hv,hw]
    simp only [inner_smul_left,inner_smul_right,conj_trivial,inner_add_left,inner_add_right,hii,h20]
    nlinarith
  have hun : hadamardU A≠0 := by
    intro he
    have hh : inner ℝ (hadamardU A) (B 3)=c := by
      rw [hu,inner_smul_left,conj_trivial,inner_add_left,hcross 0 3 (by decide),hcross 1 3 (by decide)];ring
    rw [he,inner_zero_left] at hh
    exact hc.ne hh
  have hvn : hadamardV A≠0 := by
    intro he
    have hh : inner ℝ (hadamardV A) (B 3)=c := by
      rw [hv,inner_smul_left,conj_trivial,inner_add_left,hcross 0 3 (by decide),hcross 2 3 (by decide)];ring
    rw [he,inner_zero_left] at hh
    exact hc.ne hh
  have hwn : hadamardW A≠0 := by
    intro he
    have hh : inner ℝ (hadamardW A) (B 2)=c := by
      rw [hw,inner_smul_left,conj_trivial,inner_add_left,hcross 0 2 (by decide),hcross 3 2 (by decide)];ring
    rw [he,inner_zero_left] at hh
    exact hc.ne hh
  exact ⟨hG,huv,huw,hvw,hun,hvn,hwn⟩

#print axioms disphenoid_hadamard_frame
end Blueprint.Thomson.Tail.Implementation
