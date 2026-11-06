import AllS.Units.N_GI.N_constants.N_weights

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactInner (x y : ContactIndex→ℝ) : ℝ := ∑ e, contactWeight e*x e*y e
def contactNorm (x : ContactIndex→ℝ) : ℝ := √(∑ e, contactWeight e*(x e)^2)
def contactMean (x : ContactIndex→ℝ) : ℝ := (∑ e, contactWeight e*x e)/contactTotalWeight
def contactCenter (x : ContactIndex→ℝ) (e : ContactIndex) : ℝ := x e-contactMean x
def contactWeightedVector (x : ContactIndex→ℝ) : EuclideanSpace ℝ ContactIndex :=
  WithLp.toLp 2 (fun e=>√(contactWeight e)*x e)

theorem contactTotalWeight_pos : 0<contactTotalWeight := by
  dsimp [contactTotalWeight]
  positivity

theorem contactWeight_pos (e : ContactIndex) : 0<contactWeight e := by
  linarith [contactWeight_ge_one e]

theorem contactNorm_nonneg (x : ContactIndex→ℝ) : 0≤contactNorm x := Real.sqrt_nonneg _

theorem contactNorm_sq (x : ContactIndex→ℝ) :
    (contactNorm x)^2=∑ e, contactWeight e*(x e)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun e _=>mul_nonneg (contactWeight_pos e).le (sq_nonneg _)))

theorem contactNorm_eq_norm (x : ContactIndex→ℝ) : contactNorm x=‖contactWeightedVector x‖ := by
  have he : ‖contactWeightedVector x‖^2=∑ e, contactWeight e*(x e)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro e _
    change ‖√(contactWeight e)*x e‖^2=contactWeight e*(x e)^2
    rw [Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt (contactWeight_pos e).le]
  nlinarith [contactNorm_sq x,contactNorm_nonneg x,norm_nonneg (contactWeightedVector x)]

theorem contactNorm_add_le (x y : ContactIndex→ℝ) :
    contactNorm (fun e=>x e+y e)≤contactNorm x+contactNorm y := by
  have he : contactWeightedVector (fun e=>x e+y e)=contactWeightedVector x+contactWeightedVector y := by
    ext e
    simp [contactWeightedVector,mul_add]
  simp only [contactNorm_eq_norm,he]
  exact norm_add_le _ _

theorem contactNorm_smul (c : ℝ) (x : ContactIndex→ℝ) :
    contactNorm (fun e=>c*x e)=|c| *contactNorm x := by
  have he : contactWeightedVector (fun e=>c*x e)=c • contactWeightedVector x := by
    ext e
    simp [contactWeightedVector]
    ring
  rw [contactNorm_eq_norm,he,norm_smul,Real.norm_eq_abs,←contactNorm_eq_norm]

theorem contactNorm_neg (x : ContactIndex→ℝ) : contactNorm (fun e=>-x e)=contactNorm x := by
  simpa using contactNorm_smul (-1) x

theorem contactMean_add (x y : ContactIndex→ℝ) :
    contactMean (fun e=>x e+y e)=contactMean x+contactMean y := by
  simp [contactMean,mul_add,Finset.sum_add_distrib,add_div]

theorem contactMean_smul (c : ℝ) (x : ContactIndex→ℝ) :
    contactMean (fun e=>c*x e)=c*contactMean x := by
  unfold contactMean
  have he : (∑ e, contactWeight e*(c*x e))=c*(∑ e, contactWeight e*x e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [he]
  ring

theorem contactMean_const (c : ℝ) : contactMean (fun _=>c)=c := by
  simp only [contactMean,←Finset.sum_mul,contactWeight_sum]
  field_simp [contactTotalWeight_pos.ne']

theorem contactMean_center (x : ContactIndex→ℝ) : contactMean (contactCenter x)=0 := by
  unfold contactCenter
  simp only [sub_eq_add_neg,contactMean_add]
  rw [contactMean_const]
  ring

theorem contactCenter_idempotent (x : ContactIndex→ℝ) : contactCenter (contactCenter x)=contactCenter x := by
  funext e
  simp [contactCenter,contactMean_center]

theorem contactCenter_add (x y : ContactIndex→ℝ) :
    contactCenter (fun e=>x e+y e)=fun e=>contactCenter x e+contactCenter y e := by
  funext e
  simp only [contactCenter,contactMean_add]
  ring

theorem contactCenter_smul (c : ℝ) (x : ContactIndex→ℝ) :
    contactCenter (fun e=>c*x e)=fun e=>c*contactCenter x e := by
  funext e
  simp only [contactCenter,contactMean_smul]
  ring

theorem contactCenter_of_mean_zero (x : ContactIndex→ℝ) (hx : contactMean x=0) : contactCenter x=x := by
  funext e
  simp [contactCenter,hx]

theorem contactMean_mul_total (x : ContactIndex→ℝ) :
    contactTotalWeight*contactMean x=∑ e, contactWeight e*x e := by
  unfold contactMean
  field_simp [contactTotalWeight_pos.ne']

theorem contactCenter_square_identity (x : ContactIndex→ℝ) :
    (contactNorm (contactCenter x))^2+contactTotalWeight*(contactMean x)^2=(contactNorm x)^2 := by
  simp only [contactNorm_sq,contactCenter]
  have he : (∑ e, contactWeight e*(x e-contactMean x)^2)=
      (∑ e, contactWeight e*(x e)^2)-2*contactMean x*(∑ e, contactWeight e*x e)+
        (contactMean x)^2*(∑ e, contactWeight e) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he,contactWeight_sum,←contactMean_mul_total x]
  ring

theorem contactNorm_center_le (x : ContactIndex→ℝ) : contactNorm (contactCenter x)≤contactNorm x := by
  have h := contactCenter_square_identity x
  nlinarith [contactNorm_nonneg (contactCenter x),contactNorm_nonneg x,
    mul_nonneg contactTotalWeight_pos.le (sq_nonneg (contactMean x))]

theorem contactCenter_orthogonal (x : ContactIndex→ℝ) (c : ℝ) :
    contactInner (contactCenter x) (fun _=>c)=0 := by
  unfold contactInner
  rw [←Finset.sum_mul,←contactMean_mul_total,contactMean_center]
  ring

theorem contactCenter_selfAdjoint (x y : ContactIndex→ℝ) :
    contactInner (contactCenter x) y=contactInner x (contactCenter y) := by
  have hl : contactInner (contactCenter x) y=contactInner x y-contactMean x*(∑ e, contactWeight e*y e) := by
    simp only [contactInner,contactCenter,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _; ring
  have hr : contactInner x (contactCenter y)=contactInner x y-contactMean y*(∑ e, contactWeight e*x e) := by
    simp only [contactInner,contactCenter,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [hl,hr,←contactMean_mul_total x,←contactMean_mul_total y]
  ring

theorem variance_basic_centering_projection :
    (∀ x, contactCenter (contactCenter x)=contactCenter x) ∧
    (∀ x y, contactCenter (fun e=>x e+y e)=fun e=>contactCenter x e+contactCenter y e) ∧
    (∀ c x, contactCenter (fun e=>c*x e)=fun e=>c*contactCenter x e) ∧
    (∀ x y, contactInner (contactCenter x) y=contactInner x (contactCenter y)) ∧
    (∀ x, contactMean (contactCenter x)=0 ∧ contactNorm (contactCenter x)≤contactNorm x) :=
  ⟨contactCenter_idempotent,contactCenter_add,contactCenter_smul,contactCenter_selfAdjoint,
    fun x=>⟨contactMean_center x,contactNorm_center_le x⟩⟩

#print axioms variance_basic_centering_projection
end Blueprint.Thomson.Tail.Implementation
