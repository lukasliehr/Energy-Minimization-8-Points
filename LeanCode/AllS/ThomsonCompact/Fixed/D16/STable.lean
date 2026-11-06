import ThomsonCompact.Fixed.D16.GTable
import ThomsonCompact.Fixed.D16.LTable
import ThomsonCompact.Fixed.D16.SData
import ThomsonCompact.Fixed.KernelSem

namespace ThomsonCompact.Fixed.D16

noncomputable def colAll (b j u : Nat) : Nat :=
  bif Nat.beq b 2 then col2T (Nat.add (Nat.mul 41 j) u) else col3T (Nat.add (Nat.mul 54 j) u)

def ncolAll (b : Nat) : Nat := bif Nat.beq b 2 then 36 else bif Nat.beq b 3 then 47 else 0

def nrawAll (b : Nat) : Nat := bif Nat.beq b 2 then 41 else bif Nat.beq b 3 then 54 else 0

/-- Semantic data of D16. -/
noncomputable def stab : STab where
  sc := fun b j => scT (Nat.add (Nat.mul 64 b) j)
  rd := rdT
  rnum := rnumT
  rsc := rscT
  rdi := rdiT
  rden := rdenT
  rdsc := rdscT
  rcof := rcofT
  rrho := rrhoT
  rblk := rblkT
  nden := 7
  col := colAll
  ncol := ncolAll
  nraw := nrawAll
  LN := 14
  wN := 26
  LD := 7
  wD := 10
  LC := 7
  wC := 10
  fac := facT
  fexp := fexpT
  nfac := 9
  fsgn := false

end ThomsonCompact.Fixed.D16
