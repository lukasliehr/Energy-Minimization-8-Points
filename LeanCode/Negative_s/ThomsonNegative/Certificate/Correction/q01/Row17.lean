import ThomsonNegative.Certificate.Correction.q01.Input
import ThomsonNegative.Certificate.Correction.SourceData04

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm17 : Nat := 0x2
noncomputable def inverse17 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse17_checked : sameTM (denominatorInverse context argument Source.r17d norm17) inverse17=true := by decide +kernel
theorem norm17_positive : 0 < norm17 := by decide +kernel
noncomputable def columns17 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014, 0x1, 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006]
theorem columns17_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse17 (Source.r17n j) norm17 1; M.ok && Nat.beq (rangeX context M) (columns17.getD j 0))=true := by decide +kernel
noncomputable def center17_0 : Nat := 0xf660863bff93a82a4c6cf6c5a8e96fffffffffffffffffffffffffffffffffffffffffffffffffffff414c01000
noncomputable def model17_0 : TM := ⟨0x3b30431dffc9d41526367b62d474b7ffffffffffffffffffffffffffffffffffffffffffffffffffffa, 0x3b30431dffc9d41526367b62d474b7ffffffffffffffffffffffffffffffffffffffffffffffffffffa, 0x3b30431dffc9d41526367b62d474b7ffffffffffffffffffffffffffffffffffffffffffffffffffffa, 0x4, true⟩
noncomputable def center17_1 : Nat := 0x1d7253a9f01d4ad3ab0ad759758e000000000000000000000000000000000000000000000000000000614c01000
noncomputable def model17_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffceb929d4f80ea569d5856bacbac70000000000000000000000000000000000000000000000000000003, 0x3146d62b07f15a962a7a94534538ffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x3146d62b07f15a962a7a94534538ffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x4, true⟩
noncomputable def center17_2 : Nat := 0x25669a0197f439c240c982342f1d8fffffffffffffffffffffffffffffffffffffffffffffffffffff214e01000
noncomputable def model17_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff12b34d00cbfa1ce12064c11a178ec7ffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0xed4cb2ff3405e31edf9b3ee5e8713800000000000000000000000000000000000000000000000000007, 0xed4cb2ff3405e31edf9b3ee5e8713800000000000000000000000000000000000000000000000000007, 0x4, true⟩
noncomputable def center17_3 : Nat := 0x4a8c04d954e9bf81b254998971c6ffffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model17_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa546026caa74dfc0d92a4cc4b8e37fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x5ab9fd93558b203f26d5b33b471c8000000000000000000000000000000000000000000000000000002, 0x5ab9fd93558b203f26d5b33b471c8000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_4 : Nat := 0xccb6042672f7f9dc4f47287228fd7600000000000000000000000000000000000000000000000000000415001000
noncomputable def model17_4 : TM := ⟨0x265b0213397bfcee27a39439147ebb000000000000000000000000000000000000000000000000000002, 0x265b0213397bfcee27a39439147ebb000000000000000000000000000000000000000000000000000002, 0x265b0213397bfcee27a39439147ebb000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_5 : Nat := 0x6e187d8b9b0cbb27e91a2a07ffdb2ffffffffffffffffffffffffffffffffffffffffffffffffffffffc14f01000
noncomputable def model17_5 : TM := ⟨0x170c3ec5cd865d93f48d1503ffed97fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x170c3ec5cd865d93f48d1503ffed97fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x170c3ec5cd865d93f48d1503ffed97fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center17_6 : Nat := 0x169ef2e6a72649811982d6383ff1e200000000000000000000000000000000000000000000000000000014f01000
noncomputable def model17_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4f7973539324c08cc16b1c1ff8f1000000000000000000000000000000000000000000000000000000, 0x14b0868cac6cdb3f733e94e3e0070f000000000000000000000000000000000000000000000000000000, 0x14b0868cac6cdb3f733e94e3e0070f000000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center17_7 : Nat := 0x19c5864055b67ed335caa40976045000000000000000000000000000000000000000000000000000000a14f01000
noncomputable def model17_7 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffece2c3202adb3f699ae55204bb0228000000000000000000000000000000000000000000000000000005, 0x131d3cdfd524c096651aadfb44fdd7fffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0x131d3cdfd524c096651aadfb44fdd7fffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0x4, true⟩
noncomputable def center17_8 : Nat := 0xb37b653a1c7a53b553de8b084982fffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model17_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff859bdb29d0e3d29daa9ef458424c17ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x7a6424d62f1c2d6255610ba7bdb3e800000000000000000000000000000000000000000000000000002, 0x7a6424d62f1c2d6255610ba7bdb3e800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_9 : Nat := 0xff6833bab4d26464dfec29e4d3a2ffffffffffffffffffffffffffffffffffffffffffffffffffffffc14c01000
noncomputable def model17_9 : TM := ⟨0x3fb419dd5a6932326ff614f269d17fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x3fb419dd5a6932326ff614f269d17fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x3fb419dd5a6932326ff614f269d17fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center17_10 : Nat := 0x18587bcf61b4ba9224e3f5d80e5bb500000000000000000000000000000000000000000000000000000814d01000
noncomputable def model17_10 : TM := ⟨0x42c3de7b0da5d491271faec072dda800000000000000000000000000000000000000000000000000004, 0x42c3de7b0da5d491271faec072dda800000000000000000000000000000000000000000000000000004, 0x42c3de7b0da5d491271faec072dda800000000000000000000000000000000000000000000000000004, 0x4, true⟩
noncomputable def centers17 : Nat → Nat
  | 0 => center17_0
  | 1 => center17_1
  | 2 => center17_2
  | 3 => center17_3
  | 4 => center17_4
  | 5 => center17_5
  | 6 => center17_6
  | 7 => center17_7
  | 8 => center17_8
  | 9 => center17_9
  | 10 => center17_10
  | _ => 0x100000
noncomputable def models17 : Nat → TM
  | 0 => model17_0
  | 1 => model17_1
  | 2 => model17_2
  | 3 => model17_3
  | 4 => model17_4
  | 5 => model17_5
  | 6 => model17_6
  | 7 => model17_7
  | 8 => model17_8
  | 9 => model17_9
  | 10 => model17_10
  | _ => zeroTM
theorem centers17_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse17 (centers17 k) norm17 (Nat.pow 2 384)) (models17 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
