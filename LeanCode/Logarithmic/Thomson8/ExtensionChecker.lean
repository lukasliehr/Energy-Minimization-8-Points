import Thomson8.ExtensionData
import Thomson8.GramAlgebra
import Thomson8.RootBounds

namespace Thomson8

def contactK (i : Fin 4) : K := nodes.getD i K.zero

def tripleCode (u v t : Fin 4) : ℕ := 16*u.val+4*v.val+t.val

def anchors (u v t : Fin 4) : Fin 8 × Fin 8 × Fin 8 :=
  ExtensionData.anchors.getD (tripleCode u v t) (0,1,2)

def extensionWitness (u v t a b c : Fin 4) : Fin 8 :=
  ((ExtensionData.witnesses.getD (tripleCode u v t) []).getD (tripleCode a b c) 0)

abbrev BaseCompatible (u v t : Fin 4) : Prop :=
  let z := anchors u v t
  z.1 ≠ z.2.1 ∧ z.1 ≠ z.2.2 ∧ z.2.1 ≠ z.2.2 ∧
    (candidateCode z.1 z.2.1).val=u.val+1 ∧
    (candidateCode z.1 z.2.2).val=v.val+1 ∧
    (candidateCode z.2.1 z.2.2).val=t.val+1

abbrev ExtensionCompatible (u v t a b c : Fin 4) : Prop :=
  let z := anchors u v t
  let w := extensionWitness u v t a b c
  w ≠ z.1 ∧ w ≠ z.2.1 ∧ w ≠ z.2.2 ∧
    (candidateCode z.1 w).val=a.val+1 ∧
    (candidateCode z.2.1 w).val=b.val+1 ∧
    (candidateCode z.2.2 w).val=c.val+1

def ExcludesZero (b : Box) : Prop := b.hi < 0 ∨ 0 < b.lo
instance (b : Box) : Decidable (ExcludesZero b) := inferInstanceAs (Decidable (b.hi < 0 ∨ 0 < b.lo))

theorem encloseK_excludes_zero (x : K) (h : ExcludesZero (encloseK x)) : x.eval ≠ 0 := by
  have hc := encloseK_contains x
  rcases h with hn | hp
  · exact ne_of_lt (hc.2.trans_lt (by exact_mod_cast hn))
  · exact ne_of_gt ((Rat.cast_pos.mpr hp).trans_le hc.1)

abbrev extensionCheck (u v t a b c : Fin 4) : Prop :=
  (BaseCompatible u v t ∧ ExtensionCompatible u v t a b c) ∨
    ExcludesZero (encloseK (gramResidualK (contactK u) (contactK v) (contactK t)
      (contactK a) (contactK b) (contactK c)))

theorem extensionCheck_sound (u v t a b c : Fin 4) (hc : extensionCheck u v t a b c)
    (hr : gramResidual (contactK u).eval (contactK v).eval (contactK t).eval
      (contactK a).eval (contactK b).eval (contactK c).eval=0) :
    BaseCompatible u v t ∧ ExtensionCompatible u v t a b c := by
  rcases hc with h | h
  · exact h
  · exfalso
    apply encloseK_excludes_zero _ h
    simpa only [eval_gramResidualK] using hr

theorem contact_gramDet3_nonzero (u v t : Fin 4) :
    gramDet3 (contactK u).eval (contactK v).eval (contactK t).eval ≠ 0 := by
  have hc : ExcludesZero (encloseK (gramDet3K (contactK u) (contactK v) (contactK t))) := by
    fin_cases u <;> fin_cases v <;> fin_cases t <;> decide +kernel
  simpa only [eval_gramDet3K] using encloseK_excludes_zero _ hc

end Thomson8
