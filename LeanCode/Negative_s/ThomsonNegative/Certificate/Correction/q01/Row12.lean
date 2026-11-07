import ThomsonNegative.Certificate.Correction.q01.Input
import ThomsonNegative.Certificate.Correction.SourceData03

namespace ThomsonNegative.Certificate.Correction.q01
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
noncomputable def center12_0 : Nat := 0x1804339a924f47b075cc47037548fefffffffffffffffffffffffffffffffffffffffffffffffffffff214d01000
noncomputable def model12_0 : TM := ⟨0x40219cd4927a3d83ae62381baa47f7ffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x40219cd4927a3d83ae62381baa47f7ffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x40219cd4927a3d83ae62381baa47f7ffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x4, true⟩
noncomputable def center12_1 : Nat := 0xd907423c34869f4c1716b878e70800000000000000000000000000000000000000000000000000000614b01000
noncomputable def model12_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6c83a11e1a434fa60b8b5c3c7384000000000000000000000000000000000000000000000000000003, 0x1937c5ee1e5bcb059f474a3c38c7bfffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1937c5ee1e5bcb059f474a3c38c7bfffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x4, true⟩
noncomputable def center12_2 : Nat := 0x2ce88429b79d7d1e53d7bd701d8b0fffffffffffffffffffffffffffffffffffffffffffffffffffff214e01000
noncomputable def model12_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff16744214dbcebe8f29ebdeb80ec587ffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0xe98bbdeb24314170d6142147f13a7800000000000000000000000000000000000000000000000000007, 0xe98bbdeb24314170d6142147f13a7800000000000000000000000000000000000000000000000000007, 0x4, true⟩
noncomputable def center12_3 : Nat := 0x22137fe76cfd2822e93c59015ceffffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model12_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81109bff3b67e9411749e2c80ae77fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x7eef6400c49816bee8b61d37f5188000000000000000000000000000000000000000000000000000002, 0x7eef6400c49816bee8b61d37f5188000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_4 : Nat := 0xc98987b7030691c61f555c0577039600000000000000000000000000000000000000000000000000000415001000
noncomputable def model12_4 : TM := ⟨0x24c4c3db818348e30faaae02bb81cb000000000000000000000000000000000000000000000000000002, 0x24c4c3db818348e30faaae02bb81cb000000000000000000000000000000000000000000000000000002, 0x24c4c3db818348e30faaae02bb81cb000000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_5 : Nat := 0x6cdb34e4326effd29c4cea3604611ffffffffffffffffffffffffffffffffffffffffffffffffffffffc14f01000
noncomputable def model12_5 : TM := ⟨0x166d9a7219377fe94e26751b02308ffffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x166d9a7219377fe94e26751b02308ffffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x166d9a7219377fe94e26751b02308ffffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center12_6 : Nat := 0x161cf69ce0442cf1ebbc7f23bc7441fffffffffffffffffffffffffffffffffffffffffffffffffffffa14f01000
noncomputable def model12_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb0e7b4e70221678f5de3f91de3a20fffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x14f184b18fdde9870a21c06e21c5df000000000000000000000000000000000000000000000000000003, 0x14f184b18fdde9870a21c06e21c5df000000000000000000000000000000000000000000000000000003, 0x4, true⟩
noncomputable def center12_7 : Nat := 0x1fd41f3c3418ae58ccb4ac5676525000000000000000000000000000000000000000000000000000000414f01000
noncomputable def model12_7 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefea0f9e1a0c572c665a562b3b2928000000000000000000000000000000000000000000000000000002, 0x1015f061e5f3a8d399a5a9d4c4d6d7fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x1015f061e5f3a8d399a5a9d4c4d6d7fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center12_8 : Nat := 0x3f68c76011d2ab9389c94c6ede07afffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model12_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9fb463b008e955c9c4e4a6376f03d7ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x604b9c4ff716aa363b1b59c890fc2800000000000000000000000000000000000000000000000000002, 0x604b9c4ff716aa363b1b59c890fc2800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_9 : Nat := 0xe3b5e3eced0ca9a8360fc58748697fffffffffffffffffffffffffffffffffffffffffffffffffffff814c01000
noncomputable def model12_9 : TM := ⟨0x31daf1f6768654d41b07e2c3a434bfffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x31daf1f6768654d41b07e2c3a434bfffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x31daf1f6768654d41b07e2c3a434bfffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x4, true⟩
noncomputable def center12_10 : Nat := 0xfeb837fb4f867a0a66769dc19f5fd00000000000000000000000000000000000000000000000000000614c01000
noncomputable def model12_10 : TM := ⟨0x3f5c1bfda7c33d05333b4ee0cfafe800000000000000000000000000000000000000000000000000003, 0x3f5c1bfda7c33d05333b4ee0cfafe800000000000000000000000000000000000000000000000000003, 0x3f5c1bfda7c33d05333b4ee0cfafe800000000000000000000000000000000000000000000000000003, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q01
