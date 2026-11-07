import ThomsonNegative.Certificate.Correction.q05.Input
import ThomsonNegative.Certificate.Correction.SourceData03

namespace ThomsonNegative.Certificate.Correction.q05
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
noncomputable def center12_0 : Nat := 0x3de3c6c953ef3d97436d9024dff4780000000000000000000000000000000000000000000000000000214d01000
noncomputable def model12_0 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9ef1e364a9f79ecba1b6c8126ffa3c00000000000000000000000000000000000000000000000000001, 0x610e1c9b560861345e4937ed9005c3fffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x610e1c9b560861345e4937ed9005c3fffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x4, true⟩
noncomputable def center12_1 : Nat := 0x188791ef5561c958d67c4eb516dc7100000000000000000000000000000000000000000000000000000414d01000
noncomputable def model12_1 : TM := ⟨0x443c8f7aab0e4ac6b3e275a8b6e38800000000000000000000000000000000000000000000000000002, 0x443c8f7aab0e4ac6b3e275a8b6e38800000000000000000000000000000000000000000000000000002, 0x443c8f7aab0e4ac6b3e275a8b6e38800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_2 : Nat := 0x87656366e08a476a6fec81f19797ffffffffffffffffffffffffffffffffffffffffffffffffffffc14d01000
noncomputable def model12_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8043b2b1b3704523b537f640f8cbcbffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x7fbc4d4e4c8fbadc4ac809bf07343400000000000000000000000000000000000000000000000000002, 0x7fbc4d4e4c8fbadc4ac809bf07343400000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_3 : Nat := 0x6c31ea1ab2f0c667675b2dcc745ebfffffffffffffffffffffffffffffffffffffffffffffffffffff614d01000
noncomputable def model12_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb618f50d59786333b3ad96e63a2f5fffffffffffffffffffffffffffffffffffffffffffffffffffffb, 0x49e70af2a6879ccc4c526919c5d0a000000000000000000000000000000000000000000000000000005, 0x49e70af2a6879ccc4c526919c5d0a000000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center12_4 : Nat := 0x3bc97e6817f19833776b5b3cf475a700000000000000000000000000000000000000000000000000000414e01000
noncomputable def model12_4 : TM := ⟨0xde4bf340bf8cc19bbb5ad9e7a3ad3800000000000000000000000000000000000000000000000000002, 0xde4bf340bf8cc19bbb5ad9e7a3ad3800000000000000000000000000000000000000000000000000002, 0xde4bf340bf8cc19bbb5ad9e7a3ad3800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center12_5 : Nat := 0x1dd71502c7c64ea9fc6687eaa0e6e600000000000000000000000000000000000000000000000000000414f01000
noncomputable def model12_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeeb8a8163e32754fe3343f5507373000000000000000000000000000000000000000000000000000002, 0x1114757e9c1cd8ab01ccbc0aaf8c8cfffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x1114757e9c1cd8ab01ccbc0aaf8c8cfffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center12_6 : Nat := 0x1698d91e199edd7b6e690b5ddaedf700000000000000000000000000000000000000000000000000000014f01000
noncomputable def model12_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4c6c8f0ccf6ebdb73485aeed76fb800000000000000000000000000000000000000000000000000000, 0x14b39370f330914248cb7a51128904800000000000000000000000000000000000000000000000000000, 0x14b39370f330914248cb7a51128904800000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_7 : Nat := 0x342a11c37139fe700fdd87155c8bac00000000000000000000000000000000000000000000000000000a14e01000
noncomputable def model12_7 : TM := ⟨0xa1508e1b89cff3807eec38aae45d6000000000000000000000000000000000000000000000000000005, 0xa1508e1b89cff3807eec38aae45d6000000000000000000000000000000000000000000000000000005, 0xa1508e1b89cff3807eec38aae45d6000000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center12_8 : Nat := 0x31aac237316662bc292907f682765180000000000000000000000000000000000000000000000000000014e01000
noncomputable def model12_8 : TM := ⟨0x8d5611b98b3315e149483fb413b28c00000000000000000000000000000000000000000000000000000, 0x8d5611b98b3315e149483fb413b28c00000000000000000000000000000000000000000000000000000, 0x8d5611b98b3315e149483fb413b28c00000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center12_9 : Nat := 0xe395a47cb276b2ea511b7a977381100000000000000000000000000000000000000000000000000000814c01000
noncomputable def model12_9 : TM := ⟨0x31cad23e593b5975288dbd4bb9c08800000000000000000000000000000000000000000000000000004, 0x31cad23e593b5975288dbd4bb9c08800000000000000000000000000000000000000000000000000004, 0x31cad23e593b5975288dbd4bb9c08800000000000000000000000000000000000000000000000000004, 0x4, true⟩
noncomputable def center12_10 : Nat := 0x7e324bffa05a8bdf9940db8edae4f80000000000000000000000000000000000000000000000000001614b01000
noncomputable def model12_10 : TM := ⟨0x1f1925ffd02d45efcca06dc76d727c0000000000000000000000000000000000000000000000000000b, 0x1f1925ffd02d45efcca06dc76d727c0000000000000000000000000000000000000000000000000000b, 0x1f1925ffd02d45efcca06dc76d727c0000000000000000000000000000000000000000000000000000b, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q05
