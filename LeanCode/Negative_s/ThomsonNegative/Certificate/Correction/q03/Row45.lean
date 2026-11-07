import ThomsonNegative.Certificate.Correction.q03.Input
import ThomsonNegative.Certificate.Correction.SourceData11

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm45 : Nat := 0x2
noncomputable def inverse45 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse45_checked : sameTM (denominatorInverse context argument Source.r45d norm45) inverse45=true := by decide +kernel
theorem norm45_positive : 0 < norm45 := by decide +kernel
noncomputable def columns45 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1]
theorem columns45_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse45 (Source.r45n j) norm45 1; M.ok && Nat.beq (rangeX context M) (columns45.getD j 0))=true := by decide +kernel
noncomputable def center45_0 : Nat := 0x30f9f4474c900c1b1ba0d1560a42ccf4dc91ee4ac8fb5b71d1cef31f1e3f52ff13949a3cf901b02678e14a01000
noncomputable def model45_0 : TM := ⟨0x87cfa23a648060d8dd068ab0521667a6e48f725647dadb8e8e7798f8f1fa97f89ca4d1e7c80d8133c7, 0x87cfa23a648060d8dd068ab0521667a6e48f725647dadb8e8e7798f8f1fa97f89ca4d1e7c80d8133c7, 0x87cfa23a648060d8dd068ab0521667a6e48f725647dadb8e8e7798f8f1fa97f89ca4d1e7c80d8133c7, 0x4, true⟩
noncomputable def center45_1 : Nat := 0x3f45aa750200972573b13c50f61b7cdbe62a7d87b4f2c2c79037228a7ade7f6e5ac427d98261078b97414d01000
noncomputable def model45_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9fa2d53a81004b92b9d89e287b0dbe6df3153ec3da796163c81b91453d6f3fb72d6213ecc13083c5cba, 0x605d2ac57effb46d462761d784f241920ceac13c25869e9c37e46ebac290c048d29dec133ecf7c3a346, 0x605d2ac57effb46d462761d784f241920ceac13c25869e9c37e46ebac290c048d29dec133ecf7c3a346, 0x4, true⟩
noncomputable def center45_2 : Nat := 0x3e12977abde47f05b6fded2b3340d390d7909bb8fb8687dcb33ded10122f80d2b83603b9c8380f61f1a14e01000
noncomputable def model45_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1f094bbd5ef23f82db7ef69599a069c86bc84ddc7dc343ee599ef6880917c0695c1b01dce41c07b0f8d, 0xe0f6b442a10dc07d2481096a665f96379437b223823cbc11a6610977f6e83f96a3e4fe231be3f84f073, 0xe0f6b442a10dc07d2481096a665f96379437b223823cbc11a6610977f6e83f96a3e4fe231be3f84f073, 0x4, true⟩
noncomputable def center45_3 : Nat := 0x617c8450779ffb14e50e1bddac5f6ea04e66a252688ba2a5feeb0836d3bb372ed1281e205f536b1f52fa14f01000
noncomputable def model45_3 : TM := ⟨0x10be42283bcffd8a72870deed62fb750273351293445d152ff75841b69dd9b9768940f102fa9b58fa97d, 0x10be42283bcffd8a72870deed62fb750273351293445d152ff75841b69dd9b9768940f102fa9b58fa97d, 0x10be42283bcffd8a72870deed62fb750273351293445d152ff75841b69dd9b9768940f102fa9b58fa97d, 0x4, true⟩
noncomputable def center45_4 : Nat := 0xcdd9d17f61268b96869156717ff6bcccc9ae67f366d2f126ca1387072109e5ee9a6cfcf428d9256fda14801000
noncomputable def model45_4 : TM := ⟨0x26ece8bfb09345cb4348ab38bffb5e6664d733f9b36978936509c3839084f2f74d367e7a146c92b7ed, 0x26ece8bfb09345cb4348ab38bffb5e6664d733f9b36978936509c3839084f2f74d367e7a146c92b7ed, 0x26ece8bfb09345cb4348ab38bffb5e6664d733f9b36978936509c3839084f2f74d367e7a146c92b7ed, 0x4, true⟩
noncomputable def center45_5 : Nat := 0x7aa552ae4b6b82e5e7a86c90451b30121131dc7ee8bea9009cb9436fdb4c06d2383d3b64cf4f721667414b01000
noncomputable def model45_5 : TM := ⟨0x1d52a95725b5c172f3d43648228d98090898ee3f745f54804e5ca1b7eda603691c1e9db267a7b90b33a, 0x1d52a95725b5c172f3d43648228d98090898ee3f745f54804e5ca1b7eda603691c1e9db267a7b90b33a, 0x1d52a95725b5c172f3d43648228d98090898ee3f745f54804e5ca1b7eda603691c1e9db267a7b90b33a, 0x4, true⟩
noncomputable def center45_6 : Nat := 0x3c0242f5d9722301e5f819de39e947bfde2b474daaa58b4d33808c308c476016461b5d7f0c82e7f0067a14e01000
noncomputable def model45_6 : TM := ⟨0xe01217aecb91180f2fc0cef1cf4a3dfef15a3a6d552c5a699c046184623b00b230daebf864173f8033d, 0xe01217aecb91180f2fc0cef1cf4a3dfef15a3a6d552c5a699c046184623b00b230daebf864173f8033d, 0xe01217aecb91180f2fc0cef1cf4a3dfef15a3a6d552c5a699c046184623b00b230daebf864173f8033d, 0x4, true⟩
noncomputable def center45_7 : Nat := 0x8b808846a8acae67a44f6907bd12660c72d60666cdc7fb4c0fe47c92faba1b87d9adf4bc592c980767814e01000
noncomputable def model45_7 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff45c0442354565733d227b483de893306396b033366e3fda607f23e497d5d0dc3ecd6fa5e2c964c03b3c, 0xba3fbbdcaba9a8cc2dd84b7c2176ccf9c694fccc991c0259f80dc1b682a2f23c132905a1d369b3fc4c4, 0xba3fbbdcaba9a8cc2dd84b7c2176ccf9c694fccc991c0259f80dc1b682a2f23c132905a1d369b3fc4c4, 0x4, true⟩
noncomputable def center45_8 : Nat := 0xc87bc55f5a65f8dae1fa07d52e7a48b47a1dd9e123023596ace1a8403b719c4901c1e9c926cf674145c14e01000
noncomputable def model45_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff643de2afad32fc6d70fd03ea973d245a3d0eecf091811acb5670d4201db8ce2480e0f4e49367b3a0a2e, 0x9bc21d5052cd03928f02fc1568c2dba5c2f1130f6e7ee534a98f2bdfe24731db7f1f0b1b6c984c5f5d2, 0x9bc21d5052cd03928f02fc1568c2dba5c2f1130f6e7ee534a98f2bdfe24731db7f1f0b1b6c984c5f5d2, 0x4, true⟩
noncomputable def center45_9 : Nat := 0xe3b21a7a4fee05d5ca7389796d48475b08db6499caa43fa24aac1a35dab81c81282040ab05a54a6a26214c01000
noncomputable def model45_9 : TM := ⟨0x31d90d3d27f702eae539c4bcb6a423ad846db24ce5521fd125560d1aed5c0e409410205582d2a535131, 0x31d90d3d27f702eae539c4bcb6a423ad846db24ce5521fd125560d1aed5c0e409410205582d2a535131, 0x31d90d3d27f702eae539c4bcb6a423ad846db24ce5521fd125560d1aed5c0e409410205582d2a535131, 0x4, true⟩
noncomputable def center45_10 : Nat := 0x1ba855bc09f832220a2c0085b068247d40b798e033cf23a74a47f8074d300d0f7f947a5e6140e07e223a14d01000
noncomputable def model45_10 : TM := ⟨0x5d42ade04fc191105160042d834123ea05bcc7019e791d3a523fc03a6980687bfca3d2f30a0703f111d, 0x5d42ade04fc191105160042d834123ea05bcc7019e791d3a523fc03a6980687bfca3d2f30a0703f111d, 0x5d42ade04fc191105160042d834123ea05bcc7019e791d3a523fc03a6980687bfca3d2f30a0703f111d, 0x4, true⟩
noncomputable def centers45 : Nat → Nat
  | 0 => center45_0
  | 1 => center45_1
  | 2 => center45_2
  | 3 => center45_3
  | 4 => center45_4
  | 5 => center45_5
  | 6 => center45_6
  | 7 => center45_7
  | 8 => center45_8
  | 9 => center45_9
  | 10 => center45_10
  | _ => 0x100000
noncomputable def models45 : Nat → TM
  | 0 => model45_0
  | 1 => model45_1
  | 2 => model45_2
  | 3 => model45_3
  | 4 => model45_4
  | 5 => model45_5
  | 6 => model45_6
  | 7 => model45_7
  | 8 => model45_8
  | 9 => model45_9
  | 10 => model45_10
  | _ => zeroTM
theorem centers45_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse45 (centers45 k) norm45 (Nat.pow 2 384)) (models45 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
