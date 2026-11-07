import ThomsonNegative.Geometry.Base

noncomputable section


open scoped BigOperators
namespace ThomsonNegative.Geometry

/-- Ordered coordinate tensor; every ordered coordinate tuple occurs once. -/
def oddMoment (r : ℕ) (Y : Fin 8 → Point) (α : Fin r → Fin 3) : ℝ :=
  ∑ i, ∏ j, (Y i) (α j)

theorem inner_pow_coordinates (r : ℕ) (x y : Point) :
    (inner ℝ x y)^r = ∑ α : Fin r → Fin 3, (∏ j, x (α j))*(∏ j, y (α j)) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.prod_mul_distrib]
  ring

theorem oddMoment_contraction (r : ℕ) (Y : Fin 8 → Point) (x : Point) :
    ∑ i, (inner ℝ x (Y i))^r =
      ∑ α : Fin r → Fin 3, (∏ j, x (α j))*oddMoment r Y α := by
  simp_rw [inner_pow_coordinates]
  rw [Finset.sum_comm]
  simp [oddMoment, Finset.mul_sum]

theorem oddMoment_square_identity (r : ℕ) (Y : Fin 8 → Point) :
    ∑ i, ∑ j, (inner ℝ (Y i) (Y j))^r =
      ∑ α : Fin r → Fin 3, (oddMoment r Y α)^2 := by
  simp_rw [oddMoment_contraction]
  rw [Finset.sum_comm]
  simp [oddMoment, Finset.sum_mul, pow_two]

theorem oddMoment_multicontraction (r : ℕ) (Y : Fin 8 → Point) (x : Fin r → Point) :
    (∑ i, ∏ j, inner ℝ (x j) (Y i)) =
      ∑ α : Fin r → Fin 3, (∏ j, (x j) (α j))*oddMoment r Y α := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [Fintype.prod_sum,Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  simp [oddMoment,Finset.mul_sum,mul_comm]

theorem zero_tensors_norm_square_identity (Y : Fin 8 → Point) :
    (∑ i, ∑ j, inner ℝ (Y i) (Y j)) = ‖∑ i, Y i‖^2 ∧
    (∑ i, ∑ j, (inner ℝ (Y i) (Y j))^3) =
      ∑ α : Fin 3 → Fin 3, (oddMoment 3 Y α)^2 := by
  constructor
  · simp_rw [← inner_sum]
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  · exact oddMoment_square_identity 3 Y

end ThomsonNegative.Geometry


open scoped BigOperators
namespace ThomsonNegative.Geometry

theorem oddMoment_one_iff (Y : Fin 8 → Point) :
    oddMoment 1 Y = 0 ↔ ∑ i, Y i = 0 := by
  constructor
  · intro h
    ext k
    have hk := congrFun h (fun _ => k)
    simpa [oddMoment, Fin.prod_univ_succ] using hk
  · intro h
    funext α
    have hk := congrArg (fun x : Point => x (α 0)) h
    simpa [oddMoment, Fin.prod_univ_succ] using hk

theorem oddMoment_zero_of_vertex (r : ℕ) (Y : Fin 8 → Point)
    (h : ∀ i, ∑ j, (inner ℝ (Y i) (Y j))^r = 0) : oddMoment r Y = 0 := by
  have hs : ∑ α : Fin r → Fin 3, (oddMoment r Y α)^2 = 0 := by
    rw [← oddMoment_square_identity]
    simp [h]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => sq_nonneg (oddMoment r Y α))).mp hs
  funext α
  exact (sq_eq_zero_iff).mp (hz α (Finset.mem_univ _))

theorem oddMoment_zero_contraction (r : ℕ) (Y : Fin 8 → Point)
    (h : oddMoment r Y = 0) (x : Point) : ∑ i, (inner ℝ x (Y i))^r = 0 := by
  rw [oddMoment_contraction, h]
  simp

theorem oddMoment_zero_multicontraction (r : ℕ) (Y : Fin 8 → Point)
    (h : oddMoment r Y=0) (x : Fin r → Point) : (∑ i, ∏ j, inner ℝ (x j) (Y i))=0 := by
  rw [oddMoment_multicontraction,h]
  simp

theorem oddMoment_three_mixed (Y : Fin 8 → Point) (h : oddMoment 3 Y=0) (u v w : Point) :
    (∑ i, inner ℝ u (Y i)*inner ℝ v (Y i)*inner ℝ w (Y i))=0 := by
  simpa [Fin.prod_univ_succ,mul_assoc] using
    oddMoment_zero_multicontraction 3 Y h ![u,v,w]

theorem zero_tensors_equivalence (Y : Fin 8 → Point) :
    (∀ i, (∑ j, inner ℝ (Y i) (Y j))=0 ∧
      (∑ j, (inner ℝ (Y i) (Y j))^3)=0) ↔
    (∑ i, Y i)=0 ∧ oddMoment 3 Y=0 := by
  constructor
  · intro h
    refine ⟨(oddMoment_one_iff Y).mp ?_, oddMoment_zero_of_vertex 3 Y (fun i => (h i).2)⟩
    apply oddMoment_zero_of_vertex 1 Y
    intro i
    simpa using (h i).1
  · rintro ⟨h1,h3⟩ i
    constructor
    · simpa using oddMoment_zero_contraction 1 Y ((oddMoment_one_iff Y).mpr h1) (Y i)
    · exact oddMoment_zero_contraction 3 Y h3 (Y i)

theorem zero_tensors_arbitrary_moments (Y : Fin 8 → Point)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (x : Point) :
    (∑ j, inner ℝ x (Y j))=0 ∧ (∑ j, (inner ℝ x (Y j))^3)=0 := by
  exact ⟨by simpa using oddMoment_zero_contraction 1 Y ((oddMoment_one_iff Y).mpr h1) x,
    oddMoment_zero_contraction 3 Y h3 x⟩

end ThomsonNegative.Geometry
#print axioms ThomsonNegative.Geometry.zero_tensors_equivalence
