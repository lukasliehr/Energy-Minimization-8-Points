import Coulomb8.Dyadic

namespace Coulomb8.Dyadic
open scoped BigOperators

theorem weighted_bounds {b : Dyadic} {x : ℝ} (hx : b.Contains x) (c : ℤ) :
    (min (c*b.lo) (c*b.hi) : ℤ) ≤ (scale : ℝ)*((c : ℝ)*x) ∧
    (scale : ℝ)*((c : ℝ)*x) ≤ (max (c*b.lo) (c*b.hi) : ℤ) := by
  have he : (scale : ℝ)*((c : ℝ)*x)=(c : ℝ)*((scale : ℝ)*x) := by ring
  rw [he]
  push_cast
  by_cases hc : (0 : ℝ) ≤ (c : ℝ)
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hc)).trans (le_max_left _ _)⟩

def lowerDot : List ℤ → List Dyadic → ℤ
  | c::cs,b::bs => min (c*b.lo) (c*b.hi)+lowerDot cs bs
  | _,_ => 0

def upperDot : List ℤ → List Dyadic → ℤ
  | c::cs,b::bs => max (c*b.lo) (c*b.hi)+upperDot cs bs
  | _,_ => 0

def realDot : List ℤ → List ℝ → ℝ
  | c::cs,x::xs => (c : ℝ)*x+realDot cs xs
  | _,_ => 0

theorem dot_bounds (cs : List ℤ) {bs : List Dyadic} {xs : List ℝ}
    (h : List.Forall₂ Contains bs xs) :
    (lowerDot cs bs : ℝ) ≤ (scale : ℝ)*realDot cs xs ∧
    (scale : ℝ)*realDot cs xs ≤ (upperDot cs bs : ℝ) := by
  induction h generalizing cs with
  | nil => cases cs <;> simp [lowerDot,upperDot,realDot]
  | @cons b x bs xs hx h ih =>
    cases cs with
    | nil => simp [lowerDot,upperDot,realDot]
    | cons c cs =>
      have ht := ih cs
      have hw := weighted_bounds hx c
      simp only [lowerDot,upperDot,realDot,Int.cast_add,mul_add]
      exact ⟨add_le_add hw.1 ht.1,add_le_add hw.2 ht.2⟩

theorem realDot_ofFn {n : ℕ} (c : Fin n → ℤ) (x : Fin n → ℝ) :
    realDot (List.ofFn c) (List.ofFn x)=∑ j : Fin n, (c j : ℝ)*x j := by
  induction n with
  | zero => simp [realDot]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,realDot,ih,Fin.sum_univ_succ]

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.dot_bounds

namespace Coulomb8.Dyadic

def errorNumerator (cs : List ℤ) (bs : List Dyadic) (target : Dyadic) (d : ℤ) : ℤ :=
  max |target.lo*d-upperDot cs bs| |target.hi*d-lowerDot cs bs|

theorem linear_error_bound (cs : List ℤ) {bs : List Dyadic} {xs : List ℝ}
    {target : Dyadic} {t : ℝ} {d E : ℤ} (hd : 0 < d)
    (hxs : List.Forall₂ Contains bs xs) (ht : target.Contains t)
    (hE : errorNumerator cs bs target d ≤ E) :
    |t-realDot cs xs/(d : ℝ)| ≤ (E : ℝ)/((scale : ℝ)*(d : ℝ)) := by
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp := dot_bounds cs hxs
  have htl := mul_le_mul_of_nonneg_right ht.1 hdr.le
  have htu := mul_le_mul_of_nonneg_right ht.2 hdr.le
  have hl : -(E : ℝ) ≤ (target.lo : ℝ)*(d : ℝ)-(upperDot cs bs : ℝ) := by
    have hh : |target.lo*d-upperDot cs bs| ≤ E := (le_max_left _ _).trans hE
    exact_mod_cast (abs_le.mp hh).1
  have hu : (target.hi : ℝ)*(d : ℝ)-(lowerDot cs bs : ℝ) ≤ (E : ℝ) := by
    have hh : |target.hi*d-lowerDot cs bs| ≤ E := (le_max_right _ _).trans hE
    exact_mod_cast (abs_le.mp hh).2
  have he : ((scale : ℝ)*(d : ℝ))*(t-realDot cs xs/(d : ℝ))=
      (scale : ℝ)*t*(d : ℝ)-(scale : ℝ)*realDot cs xs := by
    field_simp [hdr.ne']
    <;> ring
  have ha : |((scale : ℝ)*(d : ℝ))*(t-realDot cs xs/(d : ℝ))| ≤ (E : ℝ) := by
    rw [he]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsd : (0 : ℝ) < (scale : ℝ)*(d : ℝ) := mul_pos scale_pos hdr
  apply (le_div_iff₀ hsd).mpr
  simpa only [abs_mul,abs_of_pos hsd,abs_of_pos hdr,abs_of_pos scale_pos,mul_comm] using ha

theorem forall₂_ofFn {α β : Type*} {n : ℕ} (R : α → β → Prop)
    (f : Fin n → α) (g : Fin n → β) (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

theorem ofFn_getD {α : Type*} (d : α) (xs : List α) :
    List.ofFn (fun i : Fin xs.length => xs.getD i.val d)=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.ofFn_succ] using congrArg (List.cons x) ih

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.linear_error_bound
