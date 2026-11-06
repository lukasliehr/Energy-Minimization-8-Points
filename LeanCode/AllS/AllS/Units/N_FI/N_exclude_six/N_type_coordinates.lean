import AllS.Units.N_FI.N_exclude_six.N_frame

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem bpair_e_coordinate (a : ℝ) (x z y : Point) :
    inner ℝ (bpairE a x z) y=(inner ℝ x y+inner ℝ z y)/(2*√a) := by
  simp only [bpairE,inner_smul_left,inner_add_left,starRingEnd_apply,star_trivial]
  ring

theorem bpair_f_coordinate (a : ℝ) (x z y : Point) :
    inner ℝ (bpairF a x z) y=(inner ℝ x y-inner ℝ z y)/(2*√(1-a)) := by
  simp only [bpairF,inner_smul_left,inner_sub_left,starRingEnd_apply,star_trivial]
  ring

theorem bpair_frame_inner (a : ℝ) (x z y w : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    inner ℝ y w=inner ℝ (bpairE a x z) y*inner ℝ (bpairE a x z) w+
      inner ℝ (bpairF a x z) y*inner ℝ (bpairF a x z) w+
      inner ℝ (bpairG a x z) y*inner ℝ (bpairG a x z) w := by
  have he := (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB).sum_inner_mul_inner y w
  rw [bpairOrthonormalBasis_coe] at he
  simpa [bpairFrame,Fin.sum_univ_succ,real_inner_comm,add_assoc] using he.symm

theorem exclude_six_type_coordinates (a : ℝ) (x z y : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hB : inner ℝ x z=2*a-1)
    (alpha beta xi : ℝ) (hxy : inner ℝ x y=alpha) (hzy : inner ℝ z y=beta)
    (hxi : inner ℝ (bpairG a x z) y=xi) :
    inner ℝ (bpairE a x z) y=(alpha+beta)/(2*√a) ∧
    inner ℝ (bpairF a x z) y=(alpha-beta)/(2*√(1-a)) ∧
    ((alpha+beta)/(2*√a))^2+((alpha-beta)/(2*√(1-a)))^2+xi^2=1 := by
  have he : inner ℝ (bpairE a x z) y=(alpha+beta)/(2*√a) := by rw [bpair_e_coordinate,hxy,hzy]
  have hf : inner ℝ (bpairF a x z) y=(alpha-beta)/(2*√(1-a)) := by rw [bpair_f_coordinate,hxy,hzy]
  refine ⟨he,hf,?_⟩
  have hp := bpair_frame_inner a x z y y ha0 ha1 hx hz hB
  rw [real_inner_self_eq_norm_sq,hy,he,hf,hxi] at hp
  nlinarith

theorem bpair_reversed_coordinate_squares (a : ℝ) (x z y w : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hw : ‖w‖=1)
    (hB : inner ℝ x z=2*a-1) (alpha beta : ℝ)
    (hxy : inner ℝ x y=alpha) (hzy : inner ℝ z y=beta)
    (hxw : inner ℝ x w=beta) (hzw : inner ℝ z w=alpha) :
    (inner ℝ (bpairG a x z) y)^2=(inner ℝ (bpairG a x z) w)^2 := by
  have hyc := (exclude_six_type_coordinates a x z y ha0 ha1 hx hz hy hB alpha beta _ hxy hzy rfl).2.2
  have hwc := (exclude_six_type_coordinates a x z w ha0 ha1 hx hz hw hB beta alpha _ hxw hzw rfl).2.2
  have hplus : ((alpha+beta)/(2*√a))^2=((beta+alpha)/(2*√a))^2 := by ring
  have hminus : ((alpha-beta)/(2*√(1-a)))^2=((beta-alpha)/(2*√(1-a)))^2 := by ring
  nlinarith

#check exclude_six_type_coordinates
#print axioms exclude_six_type_coordinates
end Blueprint.Thomson.Finite
