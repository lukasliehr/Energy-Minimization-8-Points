import ThomsonCompact.Floor.B.Kernel
import ThomsonCompact.Floor.Tables.D12b.Rows0
import ThomsonCompact.Floor.Tables.D12b.Rows1
import ThomsonCompact.Floor.Tables.D12b.Rows2
import ThomsonCompact.Floor.Tables.D12b.Rows3
import ThomsonCompact.Floor.Tables.D12b.Rows4
import ThomsonCompact.Floor.Tables.D12b.Rows5
import ThomsonCompact.Floor.Tables.D12b.Rows6
import ThomsonCompact.Floor.Tables.D12b.Rows7
import ThomsonCompact.Floor.Tables.D12b.Rows8
import ThomsonCompact.Floor.Tables.D12b.Rows9
/-! D12 re-expanded table: accessors, anchor, block ranges, target directions (generated). -/


namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

noncomputable def row : Nat → RowT
  | 0 => row000
  | 1 => row001
  | 2 => row002
  | 3 => row003
  | 4 => row004
  | 5 => row005
  | 6 => row006
  | 7 => row007
  | 8 => row008
  | 9 => row009
  | 10 => row010
  | 11 => row011
  | 12 => row012
  | 13 => row013
  | 14 => row014
  | 15 => row015
  | 16 => row016
  | 17 => row017
  | 18 => row018
  | 19 => row019
  | 20 => row020
  | 21 => row021
  | 22 => row022
  | 23 => row023
  | 24 => row024
  | 25 => row025
  | 26 => row026
  | 27 => row027
  | 28 => row028
  | 29 => row029
  | 30 => row030
  | 31 => row031
  | 32 => row032
  | 33 => row033
  | 34 => row034
  | 35 => row035
  | 36 => row036
  | 37 => row037
  | 38 => row038
  | 39 => row039
  | 40 => row040
  | 41 => row041
  | 42 => row042
  | 43 => row043
  | 44 => row044
  | 45 => row045
  | 46 => row046
  | 47 => row047
  | 48 => row048
  | 49 => row049
  | 50 => row050
  | 51 => row051
  | 52 => row052
  | 53 => row053
  | 54 => row054
  | 55 => row055
  | 56 => row056
  | 57 => row057
  | 58 => row058
  | 59 => row059
  | 60 => row060
  | 61 => row061
  | 62 => row062
  | 63 => row063
  | 64 => row064
  | 65 => row065
  | 66 => row066
  | 67 => row067
  | 68 => row068
  | 69 => row069
  | 70 => row070
  | 71 => row071
  | 72 => row072
  | 73 => row073
  | 74 => row074
  | 75 => row075
  | 76 => row076
  | 77 => row077
  | 78 => row078
  | 79 => row079
  | 80 => row080
  | 81 => row081
  | 82 => row082
  | 83 => row083
  | 84 => row084
  | 85 => row085
  | 86 => row086
  | 87 => row087
  | 88 => row088
  | 89 => row089
  | 90 => row090
  | 91 => row091
  | 92 => row092
  | 93 => row093
  | 94 => row094
  | 95 => row095
  | 96 => row096
  | 97 => row097
  | 98 => row098
  | 99 => row099
  | _ => { ms := 0, nms := 0, L := 0, w := 1, F := 0, t := [], Ld := 0, Fd := 0, dh := 0, wd := 1, mag := 0, wm := 1, u := 0, v := 0 }

/-- anchor `a0 = 19/2^6`, `σ = 2^-4`; magnitude radius `u_D = 2^-1` -/
def ancP : Nat := 19
def ancQ : Nat := 6
def ancG : Nat := 4
def uDg : Nat := 1

def j0F0 : Nat := 0
def nrF0 : Nat := 11
def lmaxF0 : Nat := 41

def j0F1 : Nat := 11
def nrF1 : Nat := 4
def lmaxF1 : Nat := 22

def j0M0plus : Nat := 15
def nrM0plus : Nat := 79
def lmaxM0plus : Nat := 61

def j0M0standard : Nat := 94
def nrM0standard : Nat := 6
def lmaxM0standard : Nat := 45

end ThomsonCompact.Floor.Tables.D12b
