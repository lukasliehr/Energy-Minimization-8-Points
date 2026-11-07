import ThomsonNegative.Certificate.Correction.q07.Input
import ThomsonNegative.Certificate.Correction.SourceData03

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm12 : Nat := 0x2
noncomputable def inverse12 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse12_checked : sameTM (denominatorInverse context argument Source.r12d norm12) inverse12=true := by decide +kernel
theorem norm12_positive : 0 < norm12 := by decide +kernel
noncomputable def columns12 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014, 0x3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006]
theorem columns12_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse12 (Source.r12n j) norm12 1; M.ok && Nat.beq (rangeX context M) (columns12.getD j 0))=true := by decide +kernel
noncomputable def center12_0 : Nat := 0x322d26fef1761f602703270334e580000000000000000000000000000000000000000000000000000414601000
noncomputable def model12_0 : TM := ⟨0x916937f78bb0fb0138193819a72c00000000000000000000000000000000000000000000000000002, 0x916937f78bb0fb0138193819a72c00000000000000000000000000000000000000000000000000002, 0x916937f78bb0fb0138193819a72c00000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_1 : Nat := 0x1b4c623aa3b58bdaac8813b626aca4fffffffffffffffffffffffffffffffffffffffffffffffffffff414f01000
noncomputable def model12_1 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeda6311d51dac5ed564409db1356527ffffffffffffffffffffffffffffffffffffffffffffffffffffa, 0x1259cee2ae253a12a9bbf624eca9ad800000000000000000000000000000000000000000000000000006, 0x1259cee2ae253a12a9bbf624eca9ad800000000000000000000000000000000000000000000000000006, 0x4, true⟩
noncomputable def center12_2 : Nat := 0x31782447175bb954de1020e7be58657ffffffffffffffffffffffffffffffffffffffffffffffffffffc14e01000
noncomputable def model12_2 : TM := ⟨0x8bc12238baddcaa6f081073df2c32bffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x8bc12238baddcaa6f081073df2c32bffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x8bc12238baddcaa6f081073df2c32bffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center12_3 : Nat := 0x77819cf56b5387434f742eece2a26bfffffffffffffffffffffffffffffffffffffffffffffffffffff214f01000
noncomputable def model12_3 : TM := ⟨0x1bc0ce7ab5a9c3a1a7ba1776715135fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x1bc0ce7ab5a9c3a1a7ba1776715135fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x1bc0ce7ab5a9c3a1a7ba1776715135fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x4, true⟩
noncomputable def center12_4 : Nat := 0x39dd76bf51ad921de1c882d3f573fb00000000000000000000000000000000000000000000000000000415001000
noncomputable def model12_4 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdceebb5fa8d6c90ef0e44169fab9fd800000000000000000000000000000000000000000000000000002, 0x231144a0572936f10f1bbe960546027ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x231144a0572936f10f1bbe960546027ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center12_5 : Nat := 0x35f28da1c3c045eaf9fbff5bea62ae00000000000000000000000000000000000000000000000000001015001000
noncomputable def model12_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdaf946d0e1e022f57cfdffadf53157000000000000000000000000000000000000000000000000000008, 0x2506b92f1e1fdd0a830200520acea8fffffffffffffffffffffffffffffffffffffffffffffffffffff8, 0x2506b92f1e1fdd0a830200520acea8fffffffffffffffffffffffffffffffffffffffffffffffffffff8, 0x4, true⟩
noncomputable def center12_6 : Nat := 0x7abb578e298caa0b5198672e2ce16700000000000000000000000000000000000000000000000000000014f01000
noncomputable def model12_6 : TM := ⟨0x1d5dabc714c65505a8cc33971670b3800000000000000000000000000000000000000000000000000000, 0x1d5dabc714c65505a8cc33971670b3800000000000000000000000000000000000000000000000000000, 0x1d5dabc714c65505a8cc33971670b3800000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_7 : Nat := 0x76e8c488c3974bfd104b7ac76e694c00000000000000000000000000000000000000000000000000000e14f01000
noncomputable def model12_7 : TM := ⟨0x1b74624461cba5fe8825bd63b734a6000000000000000000000000000000000000000000000000000007, 0x1b74624461cba5fe8825bd63b734a6000000000000000000000000000000000000000000000000000007, 0x1b74624461cba5fe8825bd63b734a6000000000000000000000000000000000000000000000000000007, 0x4, true⟩
noncomputable def center12_8 : Nat := 0xe9e74122e1b869841c83209dabbaf80000000000000000000000000000000000000000000000000000014e01000
noncomputable def model12_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff74f3a09170dc34c20e41904ed5dd7c00000000000000000000000000000000000000000000000000000, 0x8b0c5f6e8f23cb3df1be6fb12a228400000000000000000000000000000000000000000000000000000, 0x8b0c5f6e8f23cb3df1be6fb12a228400000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_9 : Nat := 0xb556df6b49012c3271d0f44bff2f500000000000000000000000000000000000000000000000000000614e01000
noncomputable def model12_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5aab6fb5a480961938e87a25ff97a800000000000000000000000000000000000000000000000000003, 0xa554904a5b7f69e6c71785da006857ffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0xa554904a5b7f69e6c71785da006857ffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x4, true⟩
noncomputable def center12_10 : Nat := 0x325505b1cb6ba1dee0f5cbef155a380000000000000000000000000000000000000000000000000000014d01000
noncomputable def model12_10 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff992a82d8e5b5d0ef707ae5f78aad1c00000000000000000000000000000000000000000000000000000, 0x66d57d271a4a2f108f851a087552e400000000000000000000000000000000000000000000000000000, 0x66d57d271a4a2f108f851a087552e400000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def centers12 : Nat → Nat
  | 0 => center12_0
  | 1 => center12_1
  | 2 => center12_2
  | 3 => center12_3
  | 4 => center12_4
  | 5 => center12_5
  | 6 => center12_6
  | 7 => center12_7
  | 8 => center12_8
  | 9 => center12_9
  | 10 => center12_10
  | _ => 0x100000
noncomputable def models12 : Nat → TM
  | 0 => model12_0
  | 1 => model12_1
  | 2 => model12_2
  | 3 => model12_3
  | 4 => model12_4
  | 5 => model12_5
  | 6 => model12_6
  | 7 => model12_7
  | 8 => model12_8
  | 9 => model12_9
  | 10 => model12_10
  | _ => zeroTM
theorem centers12_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse12 (centers12 k) norm12 (Nat.pow 2 384)) (models12 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
