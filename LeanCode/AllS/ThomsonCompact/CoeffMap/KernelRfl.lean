import Lean

/-!
# `kernel_rfl_theorem`: definitional equalities checked by the kernel only

`kernel_rfl_theorem n : lhs = rhs` adds `theorem n : lhs = rhs := Eq.refl lhs` through `addDecl`, so the
equality is checked by the kernel's definitional-equality test alone (as `decide +kernel` does for decidable
propositions). This is needed for the bridges to the old `Polynomial ℚ` literals: the elaborator cannot
reduce `Rat.mul`/`Rat.inv` (`@[irreducible]`), the kernel can. No axiom, `sorry` or native code is involved;
`#print axioms` of a bridge lists nothing beyond the ingredients' axioms.

**Status: approved by the coordinator (2026-11-05)**, same trust level as `decide +kernel`, on two conditions
that every use must keep:
1. every theorem produced by `kernel_rfl_theorem` has standard `#print axioms`
   (`propext, Classical.choice, Quot.sound` or fewer); each generated module prints the axioms of at least one
   of its bridges, and the final audit prints all of them;
2. every such theorem is covered by the final `leanchecker` replay of the complete development (the replay
   re-checks the `Eq.refl` proofs in a fresh kernel, independently of this elaborator command).
-/

open Lean Elab Command Meta in
/-- `kernel_rfl_theorem n : lhs = rhs` — a theorem proved by `Eq.refl lhs`, checked by the kernel only. -/
elab "kernel_rfl_theorem " id:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then throwError "kernel_rfl_theorem: statement has metavariables"
    let some (_, lhs, _) := ty.eq? | throwError "kernel_rfl_theorem: not an equality"
    let pf ← mkEqRefl lhs
    addDecl <| Declaration.thmDecl
      { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := pf }
