import Thomson8.Algebra
import Mathlib.Topology.Order.IntermediateValue

namespace Thomson8

def quartic (a0 a1 a2 a3 a4 x : ℝ) : ℝ :=
  a0+x*(a1+x*(a2+x*(a3+x*a4)))

theorem quartic_factor (a0 a1 a2 a3 a4 r0 r1 r2 r3 : ℝ)
    (h01 : r0 < r1) (h12 : r1 < r2) (h23 : r2 < r3)
    (h0 : quartic a0 a1 a2 a3 a4 r0=0)
    (h1 : quartic a0 a1 a2 a3 a4 r1=0)
    (h2 : quartic a0 a1 a2 a3 a4 r2=0)
    (h3 : quartic a0 a1 a2 a3 a4 r3=0) (x : ℝ) :
    quartic a0 a1 a2 a3 a4 x = a4*(x-r0)*(x-r1)*(x-r2)*(x-r3) := by
  let b0 := a1+r0*(a2+r0*(a3+r0*a4))
  let b1 := a2+r0*(a3+r0*a4)
  let b2 := a3+r0*a4
  let p1 := fun t : ℝ => b0+t*(b1+t*(b2+t*a4))
  have f0 (t : ℝ) : quartic a0 a1 a2 a3 a4 t = (t-r0)*p1 t := by
    dsimp only [quartic,p1,b0,b1,b2] at h0 ⊢
    linear_combination h0
  have p1zero (r : ℝ) (hne : r ≠ r0) (hr : quartic a0 a1 a2 a3 a4 r=0) : p1 r=0 := by
    rw [f0] at hr
    exact (mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr hne)
  have h1' := p1zero r1 (by linarith) h1
  have h2' := p1zero r2 (by linarith) h2
  have h3' := p1zero r3 (by linarith) h3
  let c0 := b1+r1*(b2+r1*a4)
  let c1 := b2+r1*a4
  let p2 := fun t : ℝ => c0+t*(c1+t*a4)
  have f1 (t : ℝ) : p1 t = (t-r1)*p2 t := by
    dsimp only [p1,p2,c0,c1] at h1' ⊢
    linear_combination h1'
  have p2zero (r : ℝ) (hne : r ≠ r1) (hr : p1 r=0) : p2 r=0 := by
    rw [f1] at hr
    exact (mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr hne)
  have h2'' := p2zero r2 (by linarith) h2'
  have h3'' := p2zero r3 (by linarith) h3'
  let d0 := c1+r2*a4
  let p3 := fun t : ℝ => d0+t*a4
  have f2 (t : ℝ) : p2 t = (t-r2)*p3 t := by
    dsimp only [p2,p3,d0] at h2'' ⊢
    linear_combination h2''
  have h3''' : p3 r3=0 := by
    rw [f2] at h3''
    exact (mul_eq_zero.mp h3'').resolve_left (by linarith)
  have f3 (t : ℝ) : p3 t=a4*(t-r3) := by
    dsimp only [p3] at h3''' ⊢
    linear_combination h3'''
  rw [f0,f1,f2,f3]
  ring

theorem root_between_of_sign_change (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ r, a < r ∧ r < b ∧ f r=0 := by
  obtain ⟨r,hr,heq⟩ := intermediate_value_Icc hab.le hf ⟨ha.le,hb.le⟩
  have hna : r ≠ a := by intro h; subst r; linarith
  have hnb : r ≠ b := by intro h; subst r; linarith
  exact ⟨r,lt_of_le_of_ne hr.1 hna.symm,lt_of_le_of_ne hr.2 hnb,heq⟩

#print axioms quartic_factor

end Thomson8
