import ThomsonNegative.Geometry.Contacts
import ThomsonNegative.CertificateReduction.ContactCounts

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative.Geometry

def baselineCounts : Fin 4 → ℕ := ![2,1,2,2]

theorem contact_counts_baseline (a : ℝ) :
    (∑ k, baselineCounts k)=7 ∧
    1+(∑ k, (baselineCounts k : ℝ)*contacts a k)=0 ∧
    1+(∑ k, (baselineCounts k : ℝ)*(contacts a k)^3)=0 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  simp only [baselineCounts,contacts,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Fin.sum_univ_zero,add_zero,Nat.cast_ofNat]
  refine ⟨by norm_num,by ring,?_⟩
  rw [div_eq_mul_inv,hinv]
  linear_combination -3*a*(a-1)^2*hs

def contactNeighbors (a : ℝ) (Y : Fin 8 → Point) (i : Fin 8) (k : Fin 4) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => j ≠ i ∧ inner ℝ (Y i) (Y j)=contacts a k)

def vertexContactCounts (a : ℝ) (Y : Fin 8 → Point) (i : Fin 8) (k : Fin 4) : ℕ :=
  (contactNeighbors a Y i k).card

theorem contact_count_partition (a : ℝ) (Y : Fin 8 → Point) (ha : physical a)
    (hc : ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ∈ Set.range (contacts a))
    (i : Fin 8) (f : ℝ → ℝ) :
    (∑ k, (vertexContactCounts a Y i k:ℝ)*f (contacts a k))=
      ∑ j : Fin 8, if j=i then 0 else f (inner ℝ (Y i) (Y j)) := by
  have hn (k : Fin 4) : (vertexContactCounts a Y i k:ℝ)*f (contacts a k)=
      ∑ j : Fin 8, if j ≠ i ∧ inner ℝ (Y i) (Y j)=contacts a k then f (contacts a k) else 0 := by
    simp [vertexContactCounts,contactNeighbors,← Finset.sum_filter]
  simp_rw [hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · simp [hj]
  · obtain ⟨k,hk⟩ := hc i j (Ne.symm hj)
    rw [← hk]
    simp [hj,(contact_injective a ha).eq_iff]


def AllowedContacts (a : ℝ) (Y : Configuration) : Prop :=
  ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ∈ Set.range (contacts a)

lemma vertex_moment_counts (a : ℝ) (Y : Configuration) (ha : physical a)
    (hY : IsConfiguration Y) (hc : AllowedContacts a Y) (i : Fin 8) (r : ℕ) :
    1+(∑ k,(vertexContactCounts a Y i k:ℝ)*(contacts a k)^r)=
      ∑ j,(inner ℝ (Y i) (Y j))^r := by
  rw [contact_count_partition a Y ha hc i (fun x => x^r)]
  have hii : inner ℝ (Y i) (Y i)=1 := by rw [real_inner_self_eq_norm_sq,hY.1]; norm_num
  have hdiag : (∑ j : Fin 8,if j=i then (1:ℝ) else 0)=1 := by simp
  rw [← hdiag,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · simp [hj,hY.1]
  · simp [hj]

theorem vertex_counts_from_first (a : ℝ) (ha : physical a) (hlo : (5/16:ℝ) ≤ a)
    (Y : Configuration) (hY : IsConfiguration Y) (hc : AllowedContacts a Y)
    (hfirst : ∀ i,(∑ j,inner ℝ (Y i) (Y j))=0) :
    ∀ i,vertexContactCounts a Y i=baselineCounts := by
  intro i
  have hsum : (∑ k,vertexContactCounts a Y i k)=7 := by
    have hp := contact_count_partition a Y ha hc i (fun _ => 1)
    simp only [mul_one] at hp
    have hi : (∑ j : Fin 8,if j=i then (0:ℝ) else 1)=7 := by
      rw [Finset.sum_ite]
      simp [Finset.filter_ne']
    rw [hi,← Nat.cast_sum] at hp
    exact_mod_cast hp
  have hm := (vertex_moment_counts a Y ha hY hc i 1).trans (by simpa using hfirst i)
  have hh := CertificateReduction.antiprism_contact_counts_from_first_moment a hlo ha.2
    (vertexContactCounts a Y i 0) (vertexContactCounts a Y i 1)
    (vertexContactCounts a Y i 2) (vertexContactCounts a Y i 3)
    (by simpa [Fin.sum_univ_succ,add_assoc] using hsum)
    (by simpa [contacts,Fin.sum_univ_succ,add_assoc,mul_comm] using hm)
  funext k
  fin_cases k
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2.1
  · exact hh.2.2.2

theorem third_moments_from_counts (a : ℝ) (ha : physical a)
    (Y : Configuration) (hY : IsConfiguration Y) (hc : AllowedContacts a Y)
    (hn : ∀ i,vertexContactCounts a Y i=baselineCounts) :
    ∀ i,(∑ j,(inner ℝ (Y i) (Y j))^3)=0 := by
  intro i
  have h := vertex_moment_counts a Y ha hY hc i 3
  rw [hn i,(contact_counts_baseline a).2.2] at h
  exact h.symm

#print axioms vertex_counts_from_first
#print axioms third_moments_from_counts
end ThomsonNegative.Geometry
