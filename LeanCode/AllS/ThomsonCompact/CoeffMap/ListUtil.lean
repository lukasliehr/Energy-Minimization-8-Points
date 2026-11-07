/-!
# Recursor-built lists and lookups (Init only)

`mkList f n = [f 0, …, f (n-1)]` built by `Nat.rec`, so that every element is `f t` with `t` a recursor
predecessor (a literal): the kernel then evaluates each element once, however often it is looked up.
`listAt d L i = L.getD i d` by a direct recursor. Lemmas: `CoeffMap.PackLemmas`.
-/

namespace ThomsonCompact.CoeffMap

/-- `[f 0, …, f (n-1)]` (elements are `f t` with `t` a recursor predecessor). -/
noncomputable def mkList {α : Type} (f : Nat → α) (n : Nat) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun acc => acc) (fun t ih acc => ih (f t :: acc)) n []

/-- `L.getD i d` (direct recursor). -/
noncomputable def listAt {α : Type} (d : α) (L : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih i => Nat.casesOn (motive := fun _ => α) i a (fun j => ih j)) L

end ThomsonCompact.CoeffMap
