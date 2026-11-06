import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.LData

namespace ThomsonCompact.Fixed.D14

noncomputable def kc0 : Nat → Nat → Nat
  | 0 => k0_00
  | 1 => k0_01
  | 2 => k0_02
  | 3 => k0_03
  | 4 => k0_04
  | 5 => k0_05
  | 6 => k0_06
  | _ => fun _ => 0

def kn0 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

noncomputable def kc1 : Nat → Nat → Nat
  | 0 => k1_00
  | 1 => k1_01
  | 2 => k1_02
  | 3 => k1_03
  | 4 => k1_04
  | 5 => k1_05
  | _ => fun _ => 0

def kn1 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 0

noncomputable def kc2 : Nat → Nat → Nat
  | 0 => k2_00
  | 1 => k2_01
  | 2 => k2_02
  | 3 => k2_03
  | 4 => k2_04
  | 5 => k2_05
  | 6 => k2_06
  | 7 => k2_07
  | 8 => k2_08
  | 9 => k2_09
  | 10 => k2_10
  | 11 => k2_11
  | 12 => k2_12
  | 13 => k2_13
  | 14 => k2_14
  | 15 => k2_15
  | 16 => k2_16
  | 17 => k2_17
  | 18 => k2_18
  | 19 => k2_19
  | 20 => k2_20
  | 21 => k2_21
  | 22 => k2_22
  | 23 => k2_23
  | 24 => k2_24
  | 25 => k2_25
  | _ => fun _ => 0

def kn2 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | _ => 0

noncomputable def kc3 : Nat → Nat → Nat
  | 0 => k3_00
  | 1 => k3_01
  | 2 => k3_02
  | 3 => k3_03
  | 4 => k3_04
  | 5 => k3_05
  | 6 => k3_06
  | 7 => k3_07
  | 8 => k3_08
  | 9 => k3_09
  | 10 => k3_10
  | 11 => k3_11
  | 12 => k3_12
  | 13 => k3_13
  | 14 => k3_14
  | 15 => k3_15
  | 16 => k3_16
  | 17 => k3_17
  | 18 => k3_18
  | 19 => k3_19
  | 20 => k3_20
  | 21 => k3_21
  | 22 => k3_22
  | 23 => k3_23
  | 24 => k3_24
  | 25 => k3_25
  | 26 => k3_26
  | 27 => k3_27
  | 28 => k3_28
  | 29 => k3_29
  | 30 => k3_30
  | 31 => k3_31
  | _ => fun _ => 0

def kn3 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 1
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | _ => 0

noncomputable def kcAll (b : Nat) : Nat → Nat → Nat :=
  bif Nat.blt b 2 then (bif Nat.beq b 0 then kc0 else kc1) else (bif Nat.beq b 2 then kc2 else kc3)

def knAll (b : Nat) : Nat → Nat :=
  bif Nat.blt b 2 then (bif Nat.beq b 0 then kn0 else kn1) else (bif Nat.beq b 2 then kn2 else kn3)

noncomputable def rtAll (b u : Nat) : Nat :=
  bif Nat.beq b 2 then fld rt2 (Nat.mul 16 u) 16 else bif Nat.beq b 3 then fld rt3 (Nat.mul 16 u) 16 else 0

noncomputable def zr0 : Nat → Nat
  | 0 => zt0_0
  | 1 => zt0_1
  | 2 => zt0_2
  | 3 => zt0_3
  | 4 => zt0_4
  | 5 => zt0_5
  | 6 => zt0_6
  | 7 => zt0_7
  | _ => 0

noncomputable def zr1 : Nat → Nat
  | 0 => zt1_0
  | 1 => zt1_1
  | 2 => zt1_2
  | 3 => zt1_3
  | 4 => zt1_4
  | 5 => zt1_5
  | 6 => zt1_6
  | _ => 0

noncomputable def ztAll (b u v : Nat) : Nat :=
  bif Nat.beq b 0 then fld (zr0 u) (Nat.mul 1536 v) 1536 else bif Nat.beq b 1 then fld (zr1 u) (Nat.mul 1536 v) 1536 else 0

/-- N link data of D14. -/
noncomputable def ltab : LTab where
  D := 14
  oinfo := fun k => fld oinfo (Nat.mul 32 k) 32
  kc := kcAll
  kn := knAll
  rt := rtAll
  zt := ztAll
  rtag := fun i => fld rtagc (Nat.mul 16 i) 16

end ThomsonCompact.Fixed.D14
