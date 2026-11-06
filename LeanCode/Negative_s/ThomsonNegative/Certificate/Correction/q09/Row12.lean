import ThomsonNegative.Certificate.Correction.q09.Input
import ThomsonNegative.Certificate.Correction.SourceData03

namespace ThomsonNegative.Certificate.Correction.q09
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
noncomputable def center12_0 : Nat := 0xb2cf340e369013b0aa4610fa4747ffffffffffffffffffffffffffffffffffffffffffffffffffff614601000
noncomputable def model12_0 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff59679a071b4809d85523087d23a3ffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0xa69865f8e4b7f627aadcf782dc5c00000000000000000000000000000000000000000000000000005, 0xa69865f8e4b7f627aadcf782dc5c00000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center12_1 : Nat := 0x1ba79d5a8bec2d02869a9ec166c0cd00000000000000000000000000000000000000000000000000000c14d01000
noncomputable def model12_1 : TM := ⟨0x5d3cead45f61681434d4f60b36066800000000000000000000000000000000000000000000000000006, 0x5d3cead45f61681434d4f60b36066800000000000000000000000000000000000000000000000000006, 0x5d3cead45f61681434d4f60b36066800000000000000000000000000000000000000000000000000006, 0x4, true⟩
noncomputable def center12_2 : Nat := 0x1260539a9f2319ff8b48f0eff8ccea7ffffffffffffffffffffffffffffffffffffffffffffffffffffc14f01000
noncomputable def model12_2 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe93029cd4f918cffc5a47877fc66753ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x16cfd632b06e73003a5b878803998ac00000000000000000000000000000000000000000000000000002, 0x16cfd632b06e73003a5b878803998ac00000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_3 : Nat := 0x63b0a4ea00ef8f5bcae2e9afc9e87bfffffffffffffffffffffffffffffffffffffffffffffffffffff214f01000
noncomputable def model12_3 : TM := ⟨0x11d852750077c7ade57174d7e4f43dfffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x11d852750077c7ade57174d7e4f43dfffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x11d852750077c7ade57174d7e4f43dfffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x4, true⟩
noncomputable def center12_4 : Nat := 0xc6154a0fcbc190b32d9b87b97f553100000000000000000000000000000000000000000000000000000015001000
noncomputable def model12_4 : TM := ⟨0x230aa507e5e0c85996cdc3dcbfaa98800000000000000000000000000000000000000000000000000000, 0x230aa507e5e0c85996cdc3dcbfaa98800000000000000000000000000000000000000000000000000000, 0x230aa507e5e0c85996cdc3dcbfaa98800000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_5 : Nat := 0x7917b41e8b363e1c6a96eee8fc154dfffffffffffffffffffffffffffffffffffffffffffffffffffffe15101000
noncomputable def model12_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc8bda0f459b1f0e354b77747e0aa6ffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x437425f0ba64e0f1cab4888b81f559000000000000000000000000000000000000000000000000000001, 0x437425f0ba64e0f1cab4888b81f559000000000000000000000000000000000000000000000000000001, 0x4, true⟩
noncomputable def center12_6 : Nat := 0xf8b7125b64b0f2a7b5e94472bb45100000000000000000000000000000000000000000000000000000414c01000
noncomputable def model12_6 : TM := ⟨0x3c5b892db2587953daf4a2395da28800000000000000000000000000000000000000000000000000002, 0x3c5b892db2587953daf4a2395da28800000000000000000000000000000000000000000000000000002, 0x3c5b892db2587953daf4a2395da28800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_7 : Nat := 0xd81bd0d17e3c9831bd74e48811bbbc00000000000000000000000000000000000000000000000000001015001000
noncomputable def model12_7 : TM := ⟨0x2c0de868bf1e4c18deba724408ddde000000000000000000000000000000000000000000000000000008, 0x2c0de868bf1e4c18deba724408ddde000000000000000000000000000000000000000000000000000008, 0x2c0de868bf1e4c18deba724408ddde000000000000000000000000000000000000000000000000000008, 0x4, true⟩
noncomputable def center12_8 : Nat := 0xf2cc8014ec86bc0ffd77fe2ff5da7ffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model12_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87966400a76435e07febbff17faed3ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x78699bff589bca1f8014400e80512c00000000000000000000000000000000000000000000000000002, 0x78699bff589bca1f8014400e80512c00000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_9 : Nat := 0xba40520b73fbbe4328bd525e1b1ad00000000000000000000000000000000000000000000000000000014e01000
noncomputable def model12_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5d202905b9fddf21945ea92f0d8d6800000000000000000000000000000000000000000000000000000, 0xa2dfd6fa460220de6ba156d0f2729800000000000000000000000000000000000000000000000000000, 0xa2dfd6fa460220de6ba156d0f2729800000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_10 : Nat := 0x19ef72f7c9ecdcfce59a79c8865f4480000000000000000000000000000000000000000000000000000a14d01000
noncomputable def model12_10 : TM := ⟨0x4f7b97be4f66e7e72cd3ce4432fa2400000000000000000000000000000000000000000000000000005, 0x4f7b97be4f66e7e72cd3ce4432fa2400000000000000000000000000000000000000000000000000005, 0x4f7b97be4f66e7e72cd3ce4432fa2400000000000000000000000000000000000000000000000000005, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q09
