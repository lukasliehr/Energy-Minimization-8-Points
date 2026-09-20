import Lean_Code.BoundaryPartition
import Lean_Code.RhombusFace

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def finIndexEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv _ := by subst n; rfl
  right_inv _ := by subst n; rfl

lemma fin_cast_add_one {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (i : Fin m) :
    Fin.cast h (i + 1) = Fin.cast h i + 1 := by subst n; rfl

lemma fin_cast_sub_one {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (i : Fin m) :
    Fin.cast h (i - 1) = Fin.cast h i - 1 := by subst n; rfl

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

def reindex (C : ContactBoundaryCycle Y c hY hc) {n : ℕ} (hlen : C.size + 1 = n) : Fin n → Fin 8 :=
  fun j => C.vertex (Fin.cast hlen.symm j)

theorem reindex_injective (C : ContactBoundaryCycle Y c hY hc) {n : ℕ}
    (hlen : C.size + 1 = n) (hsupport : C.StrictSupport) : Function.Injective (C.reindex hlen) := by
  intro i j heq
  have h := C.vertex_injective_of_support hsupport heq
  exact Fin.ext (congrArg (fun k : Fin (C.size + 1) => k.val) h)

theorem reindex_side (C : ContactBoundaryCycle Y c hY hc) {n : ℕ} [NeZero n]
    (hlen : C.size + 1 = n) (j : Fin n) :
    inner ℝ (Y (C.reindex hlen j)) (Y (C.reindex hlen (j + 1))) = c := by
  unfold reindex
  rw [fin_cast_add_one]
  exact C.contact _

theorem reindex_triangle_contacts (C : ContactBoundaryCycle Y c hY hc)
    (hlen : C.size + 1 = 3) (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (Y (C.reindex hlen i)) (Y (C.reindex hlen j)) = c := by
  have h01 := C.reindex_side hlen 0
  have h12 := C.reindex_side hlen 1
  have h20 := C.reindex_side hlen 2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01
    | exact h12
    | exact h20
    | exact (real_inner_comm _ _).trans h01
    | exact (real_inner_comm _ _).trans h12
    | exact (real_inner_comm _ _).trans h20

theorem reindex_diagonal (C : ContactBoundaryCycle Y c hY hc)
    (hlen : C.size + 1 = 4) (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : C.StrictSupport) (i j : Fin 4)
    (hji : j ≠ i) (hjnext : j ≠ i + 1) (hjprev : j ≠ i - 1) :
    inner ℝ (Y (C.reindex hlen i)) (Y (C.reindex hlen j)) < c := by
  apply C.nonadjacent_inner_lt hirr hbound hsupport
  · intro heq
    exact hji (Fin.ext (congrArg (fun k : Fin (C.size + 1) => k.val) heq))
  · rw [← fin_cast_add_one]
    intro heq
    exact hjnext (Fin.ext (congrArg (fun k : Fin (C.size + 1) => k.val) heq))
  · rw [← fin_cast_sub_one]
    intro heq
    exact hjprev (Fin.ext (congrArg (fun k : Fin (C.size + 1) => k.val) heq))

theorem reindex_triangle_angle (C : ContactBoundaryCycle Y c hY hc)
    (hlen : C.size + 1 = 3) (j : Fin 3) :
    contactAngle c (Y (C.reindex hlen (j + 1))) (Y (C.reindex hlen (j - 1))) =
      Real.arccos (c / (1 + c)) := by
  apply equilateral_contact_angle _ _ c hc
  apply C.reindex_triangle_contacts hlen
  fin_cases j <;> decide

theorem reindex_quadrilateral_angle (C : ContactBoundaryCycle Y c hY hc)
    (hlen : C.size + 1 = 4) (j : Fin 4) :
    contactAngle c (Y (C.reindex hlen (j + 1))) (Y (C.reindex hlen (j - 1))) =
      quadrilateralAngle c (fun k => Y (C.reindex hlen k)) j := by
  rw [quadrilateralAngle, contactAngle_comm]
  have hj : j + 3 = j - 1 := by fin_cases j <;> decide
  rw [hj]

theorem reindex_corner_sum (C : ContactBoundaryCycle Y c hY hc) {n : ℕ} [NeZero n]
    (hlen : C.size + 1 = n) (v : Fin 8) :
    (∑ j : Fin n, (if C.reindex hlen j = v then (1 : ℝ) else 0) *
      contactAngle c (Y (C.reindex hlen (j + 1))) (Y (C.reindex hlen (j - 1)))) =
      ∑ i, (if C.vertex i = v then (1 : ℝ) else 0) *
        contactAngle c (Y (C.vertex (i + 1))) (Y (C.vertex (i - 1))) := by
  classical
  simp only [reindex, fin_cast_add_one, fin_cast_sub_one]
  exact Equiv.sum_comp (finIndexEquiv hlen.symm) (fun i =>
    (if C.vertex i = v then (1 : ℝ) else 0) *
      contactAngle c (Y (C.vertex (i + 1))) (Y (C.vertex (i - 1))))

end ContactBoundaryCycle

end SquareAntiprismVerification
