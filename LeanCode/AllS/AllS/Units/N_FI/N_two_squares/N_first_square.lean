import AllS.Units.N_FI.N_two_squares.N_square_geometry

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem square_of_common_A {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (R : CommonAPair a Y r t) :
    ∃ S : SquareRealization a Y, S.label= ![r,R.plus,t,R.minus] := by
  classical
  have hp : R.plus ∈ bpairCell a Y r t 0 0 := by rw [R.cell]; simp
  have hm : R.minus ∈ bpairCell a Y r t 0 0 := by rw [R.cell]; simp
  obtain ⟨hpr,hpt,hrp,htp⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨hmr,hmt,hrm,htm⟩ := (Finset.mem_filter.mp hm).2
  have ha := physical_mem_Ioo a h.physical
  have hpm : inner ℝ (Y R.plus) (Y R.minus)=2*a-1 := by
    have he := bpair_frame_inner a (Y r) (Y t) (Y R.plus) (Y R.minus)
      ha.1 ha.2 (h.configuration.1 r) (h.configuration.1 t) hB
    obtain ⟨hep,hfp,hgp⟩ := R.plus_coordinates
    obtain ⟨hem,hfm,hgm⟩ := R.minus_coordinates
    rw [hep,hfp,hgp,hem,hfm,hgm] at he
    have hsa := Real.sq_sqrt ha.1.le
    have hsb := Real.sq_sqrt (show 0 ≤ 1-a by linarith [ha.2])
    nlinarith
  let lab : Fin 4 → Fin 8 := ![r,R.plus,t,R.minus]
  have hinj : Function.Injective lab := by
    intro i j hij
    have hpmne := R.distinct
    fin_cases i <;> fin_cases j <;> simp_all [lab]
  have hgram := SquareAntiprismVerification.square_gram_of_diagonals (Y ∘ lab) a
    (fun i => h.configuration.1 _) hrp (by rw [real_inner_comm]; exact htp) htm
    (by rw [real_inner_comm]; exact hrm) hB hpm
  obtain ⟨U,hU⟩ := SquareAntiprismVerification.square_gram_congruent (Y ∘ lab) a ha hgram
  refine ⟨⟨lab,hinj,U,?_⟩,rfl⟩
  intro i
  have he : SquareAntiprismVerification.Xc a=X a :=
    (SquareAntiprismVerification.X_eq_Xc a).symm.trans (Blueprint.antiprism_coordinates a)
  rw [he] at hU
  exact (hU i).symm

theorem two_squares_first_square {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    ∃ S : SquareRealization a Y, S.label 0=r ∧ S.label 2=t ∧ S.labels.card=4 ∧
      (∀ i j, i ∈ S.labels → i ≠ j →
        (inner ℝ (Y i) (Y j)=contacts a 0 ∨ inner ℝ (Y i) (Y j)=contacts a 1) → j ∈ S.labels) := by
  obtain ⟨_,⟨R⟩⟩ := two_squares_common_A h h1 h3 r t hrt hB
  obtain ⟨S,hS⟩ := square_of_common_A h r t hrt hB R
  exact ⟨S,by rw [hS]; rfl,by rw [hS]; rfl,S.card,S.closed_AB h⟩

#check two_squares_first_square
#print axioms two_squares_first_square
end Blueprint.Thomson.Finite
