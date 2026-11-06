import Blueprint.Target

noncomputable section
namespace Blueprint.Thomson.Finite

theorem no_antipodes_antipodal_identity (x z : Point) (hx : ‖x‖=1) (hz : ‖z‖=1)
    (h : inner ℝ x z = -1) : z = -x := by
  have hn : ‖x+z‖^2=0 := by rw [norm_add_sq_real,hx,hz,h]; norm_num
  have hv : x+z=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact eq_neg_of_add_eq_zero_right hv

theorem unit_inner_one_eq (x z : Point) (hx : ‖x‖=1) (hz : ‖z‖=1)
    (h : inner ℝ x z = 1) : x=z := by
  have hn : ‖x-z‖^2=0 := by rw [norm_sub_sq_real,hx,hz,h]; norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

#check no_antipodes_antipodal_identity
#print axioms no_antipodes_antipodal_identity
end Blueprint.Thomson.Finite
