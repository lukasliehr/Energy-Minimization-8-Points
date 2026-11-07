import AllS.Units.N_GI.N_polar_tetrahedra.N_positive_relation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_affine_independent (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) : AffineIndependent ℝ A := by
  apply (affineIndependent_iff_of_fintype ℝ A).mpr
  intro w hsum hzero i
  rw [Finset.univ.weightedVSub_eq_linear_combination hsum] at hzero
  have hh := cube_cross_inner_sum A B c hcross w i
  rw [hsum,hzero,inner_zero_left,mul_zero,zero_add] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (sub_ne_zero.mpr (hstrict i).ne)

theorem cube_affine_coordinates (A : Fin 4 → Point) (hA : AffineIndependent ℝ A)
    (x : Point) : ∃w : Fin 4 → ℝ,(∑i,w i=1) ∧ x=∑i,w i • A i := by
  have htop : affineSpan ℝ (Set.range A)=⊤ :=
    hA.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Point])
  obtain ⟨w,hw,hx⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    (show x∈affineSpan ℝ (Set.range A) by rw [htop];trivial)
  exact ⟨w,hw,hx.trans (Finset.univ.affineCombination_eq_linear_combination A w hw)⟩

theorem cube_coordinate_halfspace (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (w : Fin 4 → ℝ)
    (hsum : ∑i,w i=1) (i : Fin 4) :
    inner ℝ (∑j,w j • A j) (B i)≤c ↔ 0≤w i := by
  rw [cube_cross_inner_sum A B c hcross w i,hsum,mul_one]
  have hi := hstrict i
  constructor <;> intro h <;> nlinarith

theorem cube_coordinate_plane (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (w : Fin 4 → ℝ)
    (hsum : ∑i,w i=1) (i : Fin 4) :
    inner ℝ (∑j,w j • A j) (B i)=c ↔ w i=0 := by
  rw [cube_cross_inner_sum A B c hcross w i,hsum,mul_one]
  have hi := hstrict i
  constructor <;> intro h <;> nlinarith

theorem cube_convex_hull_halfspaces (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) :
    convexHull ℝ (Set.range A)={x | ∀i,inner ℝ x (B i)≤c} := by
  apply Set.Subset.antisymm
  · intro x hx i
    apply convexHull_min (t:={x | inner ℝ x (B i)≤c}) ?_ ?_ hx
    · rintro _ ⟨j,rfl⟩
      by_cases hji : j=i
      · subst j;exact (hstrict i).le
      · exact (hcross j i hji).le
    · intro u hu v hv a b ha hb hab
      simp only [Set.mem_setOf_eq,inner_add_left,inner_smul_left,conj_trivial] at *
      calc
        a*inner ℝ u (B i)+b*inner ℝ v (B i) ≤ a*c+b*c :=
          add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
        _ = c := by rw [←add_mul,hab,one_mul]
  · intro x hx
    obtain ⟨w,hw,hxw⟩ := cube_affine_coordinates A (cube_affine_independent A B c hcross hstrict) x
    have hnonneg : ∀i,0≤w i := fun i =>
      (cube_coordinate_halfspace A B c hcross hstrict w hw i).mp (hxw ▸ hx i)
    rw [hxw]
    exact mem_convexHull_of_exists_fintype w A hnonneg hw (fun i => ⟨i,rfl⟩) rfl

#print axioms cube_affine_independent
#print axioms cube_affine_coordinates
#print axioms cube_convex_hull_halfspaces
end Blueprint.Thomson.Tail.Implementation
