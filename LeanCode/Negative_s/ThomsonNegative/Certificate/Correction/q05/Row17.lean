import ThomsonNegative.Certificate.Correction.q05.Input
import ThomsonNegative.Certificate.Correction.SourceData04

namespace ThomsonNegative.Certificate.Correction.q05
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
noncomputable def center17_0 : Nat := 0x47acf22166dcfd0d161f478d032800000000000000000000000000000000000000000000000000000214d01000
noncomputable def model17_0 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff823d67910b36e7e868b0fa3c68194000000000000000000000000000000000000000000000000000001, 0x7dc2986ef4c91817974f05c397e6bffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x7dc2986ef4c91817974f05c397e6bffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x4, true⟩
noncomputable def center17_1 : Nat := 0xe3d2616e7b06947352badc232a1ebfffffffffffffffffffffffffffffffffffffffffffffffffffffe14c01000
noncomputable def model17_1 : TM := ⟨0x31e930b73d834a39a95d6e11950f5ffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x31e930b73d834a39a95d6e11950f5ffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x31e930b73d834a39a95d6e11950f5ffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x4, true⟩
noncomputable def center17_2 : Nat := 0xde7dae36c22f3f29624a13a07fc3dfffffffffffffffffffffffffffffffffffffffffffffffffffffc14e01000
noncomputable def model17_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6f3ed71b61179f94b12509d03fe1efffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x90c128e49ee8606b4edaf62fc01e1000000000000000000000000000000000000000000000000000002, 0x90c128e49ee8606b4edaf62fc01e1000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_3 : Nat := 0x3d8908944eb4347743fdb67e964bffffffffffffffffffffffffffffffffffffffffffffffffffffff614a01000
noncomputable def model17_3 : TM := ⟨0xec4844a275a1a3ba1fedb3f4b25ffffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0xec4844a275a1a3ba1fedb3f4b25ffffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0xec4844a275a1a3ba1fedb3f4b25ffffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0x4, true⟩
noncomputable def center17_4 : Nat := 0x6537064123f69e2d03e0416f1f8ee800000000000000000000000000000000000000000000000000000a14f01000
noncomputable def model17_4 : TM := ⟨0x129b832091fb4f1681f020b78fc774000000000000000000000000000000000000000000000000000005, 0x129b832091fb4f1681f020b78fc774000000000000000000000000000000000000000000000000000005, 0x129b832091fb4f1681f020b78fc774000000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center17_5 : Nat := 0x967f3f4203ae7959f6a046b6ae1b800000000000000000000000000000000000000000000000000000414f01000
noncomputable def model17_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4b3f9fa101d73cacfb50235b570dc000000000000000000000000000000000000000000000000000002, 0x1b4c0605efe28c35304afdca4a8f23fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x1b4c0605efe28c35304afdca4a8f23fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center17_6 : Nat := 0x9df2db97c9f5fe8df8f5e984cdde400000000000000000000000000000000000000000000000000000014f01000
noncomputable def model17_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4ef96dcbe4faff46fc7af4c266ef2000000000000000000000000000000000000000000000000000000, 0x1b10692341b0500b903850b3d9910e000000000000000000000000000000000000000000000000000000, 0x1b10692341b0500b903850b3d9910e000000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center17_7 : Nat := 0x3df79fd0b85edd01c21e54965edf2000000000000000000000000000000000000000000000000000000414e01000
noncomputable def model17_7 : TM := ⟨0xefbcfe85c2f6e80e10f2a4b2f6f90000000000000000000000000000000000000000000000000000002, 0xefbcfe85c2f6e80e10f2a4b2f6f90000000000000000000000000000000000000000000000000000002, 0xefbcfe85c2f6e80e10f2a4b2f6f90000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_8 : Nat := 0x33384d145fa061bc26030dec4db14000000000000000000000000000000000000000000000000000000014e01000
noncomputable def model17_8 : TM := ⟨0x99c268a2fd030de130186f626d8a0000000000000000000000000000000000000000000000000000000, 0x99c268a2fd030de130186f626d8a0000000000000000000000000000000000000000000000000000000, 0x99c268a2fd030de130186f626d8a0000000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center17_9 : Nat := 0xe56bcc435e01ff67a91ab64f6847c00000000000000000000000000000000000000000000000000000614c01000
noncomputable def model17_9 : TM := ⟨0x32b5e621af00ffb3d48d5b27b423e000000000000000000000000000000000000000000000000000003, 0x32b5e621af00ffb3d48d5b27b423e000000000000000000000000000000000000000000000000000003, 0x32b5e621af00ffb3d48d5b27b423e000000000000000000000000000000000000000000000000000003, 0x4, true⟩
noncomputable def center17_10 : Nat := 0xeacdfee210813f71d5e6fc2b4a78e00000000000000000000000000000000000000000000000000001414c01000
noncomputable def model17_10 : TM := ⟨0x3566ff7108409fb8eaf37e15a53c700000000000000000000000000000000000000000000000000000a, 0x3566ff7108409fb8eaf37e15a53c700000000000000000000000000000000000000000000000000000a, 0x3566ff7108409fb8eaf37e15a53c700000000000000000000000000000000000000000000000000000a, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q05
