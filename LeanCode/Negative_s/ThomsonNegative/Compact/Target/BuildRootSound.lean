import ThomsonNegative.Compact.Target.JetsBridge

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

theorem getD_map_lt {α β : Type*} (f : α → β) (L : List α) (i : ℕ)
    (da : α) (db : β) (hi : i<L.length) : (L.map f).getD i db=f (L.getD i da) := by
  rw [getD_eq_get _ _ _ (by simpa using hi),getD_eq_get _ _ _ hi]
  simp

theorem allJetsOK_getD {L : List JetPair} (h : allJetsOK L=true) (i : ℕ) (hi : i<L.length) :
    (L.getD i zeroPair).value.ok=true ∧ (L.getD i zeroPair).slope.ok=true := by
  induction L generalizing i with
  | nil => simp at hi
  | cons J js ih =>
    simp only [allJetsOK,Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i => exact ih h.2 i (by simpa using hi)

theorem allJetsOK_widen (L : List JetPair) (ε : ℕ) :
    allJetsOK (L.map (fun J => JetPair.mk (widen J.value (Nat.mul 2 ε))
      (widen J.slope (Nat.mul 9 ε))))=allJetsOK L := by
  induction L with
  | nil => rfl
  | cons J js ih => simp only [List.map_cons,allJetsOK,ih]; rfl

theorem build_flags {c : Ctx} {Q P : TM} {ir2 : ℕ} {p : Parameters}
    (h : (build c Q P ir2 p).ok=true) :
    1≤c.S ∧ (ir2TM c ir2).ok=true ∧ Q.ok=true ∧ P.ok=true ∧
      (build c Q P ir2 p).rootResidual.ok=true ∧ proposalTubeOK c P=true ∧
      allJetsOK (proposedJets c Q P (ir2TM c ir2) p)=true ∧
      allOK (build c Q P ir2 p).coefficients=true := by
  simpa only [build,Bool.and_eq_true,Nat.ble_eq,allJetsOK_widen,and_assoc] using h

/-- Root semantics for the complete executable constructor. The endpoint
extension is explicit and agrees with `aStar` at every requested q. -/
theorem build_root_sound (hg : Good N S B W) {Q P : TM} {q p : ℝ → ℝ}
    (hQ : Encl (mkCtx N S B W) Q q) (hP : Encl (mkCtx N S B W) P p)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (ir2 : ℕ) (par : Parameters) (hok : (build (mkCtx N S B W) Q P ir2 par).ok=true) :
    (∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3)) ∧
    Encl (mkCtx N S B W) (build (mkCtx N S B W) Q P ir2 par).rootResidual
      (fun t => rawRoot (q t) (p t)) ∧
    (∀ t ∈ Set.Icc (-1:ℝ) 1, |extendedHeight q p t-p t| ≤
      ((build (mkCtx N S B W) Q P ir2 par).rootError:ℝ)/2^S) ∧
    Encl (mkCtx N S B W) (build (mkCtx N S B W) Q P ir2 par).height (extendedHeight q p) := by
  obtain ⟨hS,hIR,hQok,hPok,hRok,htube,hJok,hCok⟩ := build_flags hok
  have hp := proposalTube_sound hg hP htube
  have hI : EOK (mkCtx N S B W) (ir2TM (mkCtx N S B W) ir2) (fun _ => (Real.sqrt 2)⁻¹) :=
    fun h => ir2TM_sound hg ir2 h
  have hJ := proposedJets_eok hg hS (EOK.of_encl hQ) (EOK.of_encl hP) hI hq
    (fun t ht => ⟨(hp t ht).1.le,(hp t ht).2.le⟩) par
  have hR := rootFromJets_eok hg hI (proposedJets (mkCtx N S B W) Q P (ir2TM (mkCtx N S B W) ir2) par)
    (fun i => (hJ i).2) hRok
  have hm (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (hi : 0<q t ∧ q t<1) :
      rawRoot (q t) (p t)=seriesRoot (q t) (p t) :=
    rawRoot_interior (q t) (p t) hi ⟨(hp t ht).1.le,(hp t ht).2.le⟩
  exact ⟨hp,hR,extendedHeight_error hg hR hp hm,extendedHeight_sound hg hP hR hp hm⟩

theorem build_jets_getD (c : Ctx) (Q P : TM) (ir2 : ℕ) (par : Parameters) (i : Fin 4) :
    (build c Q P ir2 par).jets.getD i.val zeroPair=
      JetPair.mk (widen ((proposedJets c Q P (ir2TM c ir2) par).getD i.val zeroPair).value
        (Nat.mul 2 (build c Q P ir2 par).rootError))
      (widen ((proposedJets c Q P (ir2TM c ir2) par).getD i.val zeroPair).slope
        (Nat.mul 9 (build c Q P ir2 par).rootError)) := by
  apply getD_map_lt
  simpa only [proposedJets,List.length_cons,List.length_nil] using i.isLt

/-- All four cached value/slope pairs enclose their explicit endpoint-extended
semantics. Interior matching with the potential is `rawJets_interior`. -/
theorem build_jets_sound (hg : Good N S B W) {Q P : TM} {q p : ℝ → ℝ}
    (hQ : Encl (mkCtx N S B W) Q q) (hP : Encl (mkCtx N S B W) P p)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (ir2 : ℕ) (par : Parameters) (hok : (build (mkCtx N S B W) Q P ir2 par).ok=true)
    (i : Fin 4) :
    Encl (mkCtx N S B W) ((build (mkCtx N S B W) Q P ir2 par).jets.getD i.val zeroPair).value
      (fun t => rawValue (q t) (extendedHeight q p t) i) ∧
    Encl (mkCtx N S B W) ((build (mkCtx N S B W) Q P ir2 par).jets.getD i.val zeroPair).slope
      (fun t => rawSlope (q t) (extendedHeight q p t) i) := by
  obtain ⟨hS,hIR,hQok,hPok,hRok,htube,hJok,hCok⟩ := build_flags hok
  obtain ⟨hp,hR,he,hA⟩ := build_root_sound hg hQ hP hq ir2 par hok
  have hI : EOK (mkCtx N S B W) (ir2TM (mkCtx N S B W) ir2) (fun _ => (Real.sqrt 2)⁻¹) :=
    fun h => ir2TM_sound hg ir2 h
  have hJ := proposedJets_eok hg hS (EOK.of_encl hQ) (EOK.of_encl hP) hI hq
    (fun t ht => ⟨(hp t ht).1.le,(hp t ht).2.le⟩) par i
  have hj := allJetsOK_getD hJok i.val (by
    simpa only [proposedJets,List.length_cons,List.length_nil] using i.isLt)
  rw [build_jets_getD]
  exact ⟨cachedValue_sound (build (mkCtx N S B W) Q P ir2 par).rootError (hJ.1 hj.1) hp he,
    cachedSlope_sound (build (mkCtx N S B W) Q P ir2 par).rootError (hJ.2 hj.2) hp he⟩

#print axioms build_root_sound
#print axioms build_jets_sound
end ThomsonNegative.Compact.Target
