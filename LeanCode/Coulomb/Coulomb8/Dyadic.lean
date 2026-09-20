import Coulomb8.Algebra
import Coulomb8.Interval

namespace Coulomb8

structure Dyadic where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace Dyadic

def scale : ℤ := 2^128

def Contains (b : Dyadic) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ (scale : ℝ)*x ∧ (scale : ℝ)*x ≤ (b.hi : ℝ)

def zero : Dyadic := ⟨0,0⟩
def add (b c : Dyadic) : Dyadic := ⟨b.lo+c.lo,b.hi+c.hi⟩
def neg (b : Dyadic) : Dyadic := ⟨-b.hi,-b.lo⟩

def RationalFits (q : ℚ) (b : Dyadic) : Prop :=
  (b.lo : ℚ) ≤ (scale : ℚ)*q ∧ (scale : ℚ)*q ≤ (b.hi : ℚ)
instance (q : ℚ) (b : Dyadic) : Decidable (RationalFits q b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def MulFits (b c d : Dyadic) : Prop :=
  d.lo*scale ≤ min (min (b.lo*c.lo) (b.lo*c.hi)) (min (b.hi*c.lo) (b.hi*c.hi)) ∧
  max (max (b.lo*c.lo) (b.lo*c.hi)) (max (b.hi*c.lo) (b.hi*c.hi)) ≤ d.hi*scale
instance (b c d : Dyadic) : Decidable (MulFits b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

def AddFits (b c d : Dyadic) : Prop := d.lo ≤ b.lo+c.lo ∧ b.hi+c.hi ≤ d.hi
instance (b c d : Dyadic) : Decidable (AddFits b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]

theorem contains_zero : zero.Contains 0 := by simp [Contains,zero]

theorem contains_rational {q : ℚ} {b : Dyadic} (hb : RationalFits q b) : b.Contains (q : ℝ) := by
  rcases hb with ⟨hl,hu⟩
  constructor <;> exact_mod_cast ‹_›

theorem contains_add {b c d : Dyadic} {x y : ℝ}
    (hx : b.Contains x) (hy : c.Contains y) (h : AddFits b c d) : d.Contains (x+y) := by
  have hl : (d.lo : ℝ) ≤ b.lo+c.lo := by exact_mod_cast h.1
  have hu : (b.hi : ℝ)+c.hi ≤ d.hi := by exact_mod_cast h.2
  rcases hx with ⟨hxl,hxu⟩
  rcases hy with ⟨hyl,hyu⟩
  constructor <;> nlinarith

private theorem lower_mul {l x u a L : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : L ≤ l*a) (hu : L ≤ u*a) : L ≤ x*a := by
  by_cases ha : 0 ≤ a
  · exact hl.trans (mul_le_mul_of_nonneg_right hx.1 ha)
  · exact hu.trans (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge ha))

private theorem upper_mul {l x u a U : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : l*a ≤ U) (hu : u*a ≤ U) : x*a ≤ U := by
  by_cases ha : 0 ≤ a
  · exact (mul_le_mul_of_nonneg_right hx.2 ha).trans hu
  · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge ha)).trans hl

theorem contains_mul {b c d : Dyadic} {x y : ℝ}
    (hx : b.Contains x) (hy : c.Contains y) (h : MulFits b c d) : d.Contains (x*y) := by
  have hl : (d.lo : ℝ)*(scale : ℝ) ≤
      min (min ((b.lo : ℝ)*c.lo) ((b.lo : ℝ)*c.hi))
        (min ((b.hi : ℝ)*c.lo) ((b.hi : ℝ)*c.hi)) := by exact_mod_cast h.1
  have hu : max (max ((b.lo : ℝ)*c.lo) ((b.lo : ℝ)*c.hi))
        (max ((b.hi : ℝ)*c.lo) ((b.hi : ℝ)*c.hi)) ≤ (d.hi : ℝ)*(scale : ℝ) := by exact_mod_cast h.2
  have hp : (d.lo : ℝ)*(scale : ℝ) ≤ ((scale : ℝ)*x)*((scale : ℝ)*y) ∧
      ((scale : ℝ)*x)*((scale : ℝ)*y) ≤ (d.hi : ℝ)*(scale : ℝ) := by
    constructor
    · apply lower_mul hx
      · rw [mul_comm (b.lo : ℝ)]
        apply lower_mul hy
        · simpa [mul_comm] using hl.trans ((min_le_left _ _).trans (min_le_left _ _))
        · simpa [mul_comm] using hl.trans ((min_le_left _ _).trans (min_le_right _ _))
      · rw [mul_comm (b.hi : ℝ)]
        apply lower_mul hy
        · simpa [mul_comm] using hl.trans ((min_le_right _ _).trans (min_le_left _ _))
        · simpa [mul_comm] using hl.trans ((min_le_right _ _).trans (min_le_right _ _))
    · apply upper_mul hx
      · rw [mul_comm (b.lo : ℝ)]
        apply upper_mul hy
        · simpa [mul_comm] using ((le_max_left _ _).trans (le_max_left _ _)).trans hu
        · simpa [mul_comm] using ((le_max_right _ _).trans (le_max_left _ _)).trans hu
      · rw [mul_comm (b.hi : ℝ)]
        apply upper_mul hy
        · simpa [mul_comm] using ((le_max_left _ _).trans (le_max_right _ _)).trans hu
        · simpa [mul_comm] using ((le_max_right _ _).trans (le_max_right _ _)).trans hu
  have he : ((scale : ℝ)*x)*((scale : ℝ)*y)=(scale : ℝ)*(x*y)*(scale : ℝ) := by ring
  rw [he] at hp
  exact ⟨(mul_le_mul_iff_left₀ scale_pos).mp hp.1,(mul_le_mul_iff_left₀ scale_pos).mp hp.2⟩

structure HornerStep where
  coefficient : Dyadic
  product : Dyadic
  result : Dyadic
  deriving DecidableEq, Repr

def output : List HornerStep → Dyadic
  | [] => zero
  | s::_ => s.result

def HornerCheck (x : Dyadic) : K → List HornerStep → Prop
  | [],[] => True
  | c::p,s::ss => RationalFits c s.coefficient ∧ MulFits x (output ss) s.product ∧
      AddFits s.coefficient s.product s.result ∧ HornerCheck x p ss
  | _,_ => False
instance (x : Dyadic) (p : K) (s : List HornerStep) : Decidable (HornerCheck x p s) := by
  induction p generalizing s with
  | nil => cases s <;> unfold HornerCheck <;> infer_instance
  | cons c p ih =>
    cases s with
    | nil => unfold HornerCheck; infer_instance
    | cons s ss => unfold HornerCheck; exact instDecidableAnd

theorem horner_sound {x : Dyadic} {t : ℝ} (hx : x.Contains t)
    (p : K) (ss : List HornerStep) (h : HornerCheck x p ss) :
    (output ss).Contains (K.evalAt t p) := by
  induction p generalizing ss with
  | nil =>
    cases ss with
    | nil => exact contains_zero
    | cons s ss => cases h
  | cons c p ih =>
    cases ss with
    | nil => cases h
    | cons s ss =>
      rcases h with ⟨hc,hm,ha,hh⟩
      exact contains_add (contains_rational hc) (contains_mul hx (ih ss hh) hm) ha

end Dyadic
end Coulomb8

#print axioms Coulomb8.Dyadic.horner_sound
