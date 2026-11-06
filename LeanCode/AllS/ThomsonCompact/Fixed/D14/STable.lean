import ThomsonCompact.Fixed.D14.GTable
import ThomsonCompact.Fixed.D14.LTable
import ThomsonCompact.Fixed.D14.SData
import ThomsonCompact.Fixed.KernelSem

namespace ThomsonCompact.Fixed.D14

noncomputable def colAll (b j u : Nat) : Nat :=
  bif Nat.beq b 2 then col2T (Nat.add (Nat.mul 31 j) u) else col3T (Nat.add (Nat.mul 39 j) u)

def ncolAll (b : Nat) : Nat := bif Nat.beq b 2 then 26 else bif Nat.beq b 3 then 32 else 0

def nrawAll (b : Nat) : Nat := bif Nat.beq b 2 then 31 else bif Nat.beq b 3 then 39 else 0

/-- Semantic data of D14. -/
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
  LN := 13
  wN := 23
  LD := 7
  wD := 10
  LC := 7
  wC := 10
  fac := facT
  fexp := fexpT
  nfac := 9
  fsgn := false

end ThomsonCompact.Fixed.D14
