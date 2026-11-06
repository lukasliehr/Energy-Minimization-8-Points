import AllS.Units.N_F.N_bpair_cases
import Lean_Code.ContactDirections

noncomputable section
open Real
open SquareAntiprismVerification (crossVec crossVec_inner_left crossVec_inner_right crossVec_norm_sq)
namespace Blueprint.Thomson.Finite

def bpairE (a : ℝ) (x z : Point) : Point := (2*√a)⁻¹ • (x+z)
def bpairF (a : ℝ) (x z : Point) : Point := (2*√(1-a))⁻¹ • (x-z)
def bpairG (a : ℝ) (x z : Point) : Point := crossVec (bpairE a x z) (bpairF a x z)
def bpairFrame (a : ℝ) (x z : Point) : Fin 3 → Point := ![bpairE a x z,bpairF a x z,bpairG a x z]

theorem bpair_frame_norms (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    ‖bpairE a x z‖=1 ∧ ‖bpairF a x z‖=1 ∧ inner ℝ (bpairE a x z) (bpairF a x z)=0 := by
  have hsa := Real.sq_sqrt ha0.le
  have hsb := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have hna : ‖x+z‖=2*√a := by
    have h := norm_add_sq_real x z
    rw [hx,hz,hB] at h
    nlinarith [norm_nonneg (x+z),Real.sqrt_nonneg a]
  have hnb : ‖x-z‖=2*√(1-a) := by
    have h := norm_sub_sq_real x z
    rw [hx,hz,hB] at h
    nlinarith [norm_nonneg (x-z),Real.sqrt_nonneg (1-a)]
  have hi : inner ℝ (x+z) (x-z)=0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,hx,hz]
    rw [real_inner_comm z x]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [bpairE,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hna]
    exact inv_mul_cancel₀ (by positivity)
  · rw [bpairF,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hnb]
    exact inv_mul_cancel₀ (by positivity)
  · simp only [bpairE,bpairF,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial,hi,mul_zero]

theorem bpairFrame_orthonormal (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    Orthonormal ℝ (bpairFrame a x z) := by
  obtain ⟨he,hf,hef⟩ := bpair_frame_norms a x z ha0 ha1 hx hz hB
  have hge : inner ℝ (bpairG a x z) (bpairE a x z)=0 := crossVec_inner_left _ _
  have hgf : inner ℝ (bpairG a x z) (bpairF a x z)=0 := crossVec_inner_right _ _
  have hg : ‖bpairG a x z‖=1 := by
    have h := crossVec_norm_sq (bpairE a x z) (bpairF a x z)
    rw [he,hf,hef] at h
    change ‖bpairG a x z‖^2 = _ at h
    nlinarith [norm_nonneg (bpairG a x z)]
  have hfe : inner ℝ (bpairF a x z) (bpairE a x z)=0 := by rw [real_inner_comm]; exact hef
  have heg : inner ℝ (bpairE a x z) (bpairG a x z)=0 := by rw [real_inner_comm]; exact hge
  have hfg : inner ℝ (bpairF a x z) (bpairG a x z)=0 := by rw [real_inner_comm]; exact hgf
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bpairFrame,Fin.ext_iff,he,hf,hg,hef,hfe,hge,heg,hgf,hfg]

def bpairOrthonormalBasis (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) : OrthonormalBasis (Fin 3) ℝ Point :=
  let hon := bpairFrame_orthonormal a x z ha0 ha1 hx hz hB
  let b := basisOfOrthonormalOfCardEqFinrank hon (by simp [Point])
  b.toOrthonormalBasis (by simpa [b] using hon)

theorem bpairOrthonormalBasis_coe (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB : Fin 3 → Point)=bpairFrame a x z := by
  simp [bpairOrthonormalBasis]

theorem exclude_six_frame (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    Orthonormal ℝ (bpairFrame a x z) ∧
    ∀ w : Point, w=inner ℝ (bpairE a x z) w • bpairE a x z+
      inner ℝ (bpairF a x z) w • bpairF a x z+inner ℝ (bpairG a x z) w • bpairG a x z := by
  refine ⟨bpairFrame_orthonormal a x z ha0 ha1 hx hz hB,?_⟩
  intro w
  have he := (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB).sum_repr' w
  rw [bpairOrthonormalBasis_coe] at he
  simpa [bpairFrame,Fin.sum_univ_succ,add_assoc] using he.symm

#check exclude_six_frame
#print axioms exclude_six_frame
end Blueprint.Thomson.Finite
