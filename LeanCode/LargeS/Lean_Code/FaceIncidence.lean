import Lean_Code.AreaSummation

noncomputable section
namespace SquareAntiprismVerification

def faceCornersAt {g m : ℕ} (V : Fin g → Fin m → Fin 8) (v : Fin 8) :
    Finset (Fin g × Fin m) := Finset.univ.filter (fun p => V p.1 p.2 = v)

def faceCornerCount {g m : ℕ} (V : Fin g → Fin m → Fin 8) (v : Fin 8) : ℕ :=
  (faceCornersAt V v).card

def faceIncidentSum {g m : ℕ} (V : Fin g → Fin m → Fin 8)
    (f : Fin g → Fin m → ℝ) (v : Fin 8) : ℝ :=
  ∑ p ∈ faceCornersAt V v, f p.1 p.2

lemma sum_faceIncidentSum {g m : ℕ} (V : Fin g → Fin m → Fin 8)
    (f : Fin g → Fin m → ℝ) :
    ∑ v, faceIncidentSum V f v = ∑ i, ∑ j, f i j := by
  classical
  simp only [faceIncidentSum, faceCornersAt, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [Fintype.sum_prod_type]

lemma faceCornerCount_eq_sum_one {g m : ℕ} (V : Fin g → Fin m → Fin 8) (v : Fin 8) :
    (faceCornerCount V v : ℝ) = faceIncidentSum V (fun _ _ => 1) v := by
  simp [faceCornerCount, faceIncidentSum]

lemma sum_faceCornerCount {g m : ℕ} (V : Fin g → Fin m → Fin 8) :
    ∑ v, (faceCornerCount V v : ℝ) = (m : ℝ) * (g : ℝ) := by
  simp only [faceCornerCount_eq_sum_one]
  rw [sum_faceIncidentSum]
  simp [mul_comm]

lemma sum_faceIncidentArea {g m : ℕ} (V : Fin g → Fin m → Fin 8) (A : Fin g → ℝ) :
    ∑ v, faceIncidentSum V (fun i _ => A i) v = (m : ℝ) * ∑ i, A i := by
  rw [sum_faceIncidentSum]
  simp [Finset.mul_sum]

lemma faceIncidentSum_const {g m : ℕ} (V : Fin g → Fin m → Fin 8) (v : Fin 8) (a : ℝ) :
    faceIncidentSum V (fun _ _ => a) v = (faceCornerCount V v : ℝ) * a := by
  simp [faceIncidentSum, faceCornerCount]

lemma faceIncidentSum_add {g m : ℕ} (V : Fin g → Fin m → Fin 8)
    (f k : Fin g → Fin m → ℝ) (v : Fin 8) :
    faceIncidentSum V (fun i j => f i j + k i j) v = faceIncidentSum V f v + faceIncidentSum V k v := by
  simp only [faceIncidentSum, Finset.sum_add_distrib]

lemma faceIncidentSum_eq_subtype_sum {g m : ℕ} (V : Fin g → Fin m → Fin 8)
    (f : Fin g → Fin m → ℝ) (v : Fin 8) :
    faceIncidentSum V f v = ∑ p : ↥(faceCornersAt V v), f p.val.1 p.val.2 := by
  simp [faceIncidentSum]
  exact (Finset.sum_attach _ _).symm

lemma faceCornerCount_eq_fintype_card {g m : ℕ} (V : Fin g → Fin m → Fin 8) (v : Fin 8) :
    faceCornerCount V v = Fintype.card ↥(faceCornersAt V v) := by
  simp [faceCornerCount]

end SquareAntiprismVerification
