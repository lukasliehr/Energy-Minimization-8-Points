import ThomsonNegative.Certificate.Correction.q01.Input
import ThomsonNegative.Certificate.Correction.SourceData11

namespace ThomsonNegative.Certificate.Correction.q01
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
noncomputable def center45_0 : Nat := 0x33396f31c3c8749578668d6a73eb4953c136f2399f26cf6c9c7064d23157a4b7101bf3bbdb9ffcdef37214e01000
noncomputable def model45_0 : TM := ⟨0x99cb798e1e43a4abc3346b539f5a4a9e09b791ccf9367b64e38326918abd25b880df9ddedcffe6f79b9, 0x99cb798e1e43a4abc3346b539f5a4a9e09b791ccf9367b64e38326918abd25b880df9ddedcffe6f79b9, 0x99cb798e1e43a4abc3346b539f5a4a9e09b791ccf9367b64e38326918abd25b880df9ddedcffe6f79b9, 0x4, true⟩
noncomputable def center45_1 : Nat := 0xf02fdee1b3cea8d6b39a164e9843c42bf840cdc6b187129cd14cbbbe373a8d7d963b595f141fe0078ec14e01000
noncomputable def model45_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7817ef70d9e7546b59cd0b274c21e215fc2066e358c3894e68a65ddf1b9d46becb1dacaf8a0ff003c76, 0x87e8108f2618ab94a632f4d8b3de1dea03df991ca73c76b19759a220e462b94134e2535075f00ffc38a, 0x87e8108f2618ab94a632f4d8b3de1dea03df991ca73c76b19759a220e462b94134e2535075f00ffc38a, 0x4, true⟩
noncomputable def center45_2 : Nat := 0x1661e2fa813751b28db3e561a30ca28cecd187d62c36525ed6bafa6bfd106ba5500e6f6a366772a7e2614e01000
noncomputable def model45_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b30f17d409ba8d946d9f2b0d18651467668c3eb161b292f6b5d7d35fe8835d2a80737b51b33b953f13, 0xf4cf0e82bf645726b9260d4f2e79aeb989973c14e9e4d6d094a282ca0177ca2d57f8c84ae4cc46ac0ed, 0xf4cf0e82bf645726b9260d4f2e79aeb989973c14e9e4d6d094a282ca0177ca2d57f8c84ae4cc46ac0ed, 0x4, true⟩
noncomputable def center45_3 : Nat := 0xf51e44e4df6b1b41e35e128d155d71bbcc02b7145a6321609b0b28886a890b41eee21e7f06048d001bee15001000
noncomputable def model45_3 : TM := ⟨0x3a8f22726fb58da0f1af09468aaeb8dde6015b8a2d3190b04d859444354485a0f7710f3f830246800df7, 0x3a8f22726fb58da0f1af09468aaeb8dde6015b8a2d3190b04d859444354485a0f7710f3f830246800df7, 0x3a8f22726fb58da0f1af09468aaeb8dde6015b8a2d3190b04d859444354485a0f7710f3f830246800df7, 0x4, true⟩
noncomputable def center45_4 : Nat := 0x331ed8a049d1302fc0d6ec58b3ce738d5b17a9922809cd59ea7b8842c8b55cd0df48846b31bf3b08fbd414e01000
noncomputable def model45_4 : TM := ⟨0x98f6c5024e89817e06b762c59e739c6ad8bd4c91404e6acf53dc421645aae686fa4423598df9d847dea, 0x98f6c5024e89817e06b762c59e739c6ad8bd4c91404e6acf53dc421645aae686fa4423598df9d847dea, 0x98f6c5024e89817e06b762c59e739c6ad8bd4c91404e6acf53dc421645aae686fa4423598df9d847dea, 0x4, true⟩
noncomputable def center45_5 : Nat := 0x62dc04b9daf08b8e27b96e70d254b9d90d8d83b75d5885438e27bbbed0bbd9485ea17231c344eee5e09c15101000
noncomputable def model45_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb16e025ced7845c713dcb738692a5cec86c6c1dbaeac42a1c713dddf685deca42f50b918e1a27772f04e, 0x4e91fda31287ba38ec2348c796d5a31379393e245153bd5e38ec222097a2135bd0af46e71e5d888d0fb2, 0x4e91fda31287ba38ec2348c796d5a31379393e245153bd5e38ec222097a2135bd0af46e71e5d888d0fb2, 0x4, true⟩
noncomputable def center45_6 : Nat := 0x145764e2cce6e95b072273e40893a7ab2a42cd8b40b8a27fe0611c482252a115bbf31ff34ca6261110e214f01000
noncomputable def model45_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffea2bb271667374ad839139f20449d3d5952166c5a05c513ff0308e241129508addf98ff9a65313088871, 0x15d44d8e998c8b527c6ec60dfbb62c2a6ade993a5fa3aec00fcf71dbeed6af752206700659acecf7778f, 0x15d44d8e998c8b527c6ec60dfbb62c2a6ade993a5fa3aec00fcf71dbeed6af752206700659acecf7778f, 0x4, true⟩
noncomputable def center45_7 : Nat := 0x72178e896a47a0b0f3b4ae246a1793d9570c8bfc7972fac63b4449d99656b0536ed954f53a11209abdda14f01000
noncomputable def model45_7 : TM := ⟨0x190bc744b523d05879da5712350bc9ecab8645fe3cb97d631da224eccb2b5829b76caa7a9d08904d5eed, 0x190bc744b523d05879da5712350bc9ecab8645fe3cb97d631da224eccb2b5829b76caa7a9d08904d5eed, 0x190bc744b523d05879da5712350bc9ecab8645fe3cb97d631da224eccb2b5829b76caa7a9d08904d5eed, 0x4, true⟩
noncomputable def center45_8 : Nat := 0x322d2989b09a93bffbec5894fbdb1c4e5d5e50601d584dbc2fde1f1942682da238619df20b26c31d2dac14e01000
noncomputable def model45_8 : TM := ⟨0x91694c4d84d49dffdf62c4a7ded8e272eaf28300eac26de17ef0f8ca13416d11c30cef90593618e96d6, 0x91694c4d84d49dffdf62c4a7ded8e272eaf28300eac26de17ef0f8ca13416d11c30cef90593618e96d6, 0x91694c4d84d49dffdf62c4a7ded8e272eaf28300eac26de17ef0f8ca13416d11c30cef90593618e96d6, 0x4, true⟩
noncomputable def center45_9 : Nat := 0x372bd23aef9898526063349dfe948514055ac274b4b87001e0cec4e8ce9c5cbeea3997e40b4baab312614d01000
noncomputable def model45_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9b95e91d77cc4c2930319a4eff4a428a02ad613a5a5c3800f0676274674e2e5f751ccbf205a5d559893, 0x646a16e28833b3d6cfce65b100b5bd75fd529ec5a5a3c7ff0f989d8b98b1d1a08ae3340dfa5a2aa676d, 0x646a16e28833b3d6cfce65b100b5bd75fd529ec5a5a3c7ff0f989d8b98b1d1a08ae3340dfa5a2aa676d, 0x4, true⟩
noncomputable def center45_10 : Nat := 0x3ee5c2bc7974236a0278f0fd81831083d36fff3e4e3face08ca151697b60d8aab894cf8b0a6e9ea67d614c01000
noncomputable def model45_10 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf72e15e3cba11b5013c787ec0c18841e9b7ff9f271fd6704650a8b4bdb06c555c4a67c585374f533eb, 0x208d1ea1c345ee4afec387813f3e77be16480060d8e0298fb9af574b424f93aaa3b5983a7ac8b0acc15, 0x208d1ea1c345ee4afec387813f3e77be16480060d8e0298fb9af574b424f93aaa3b5983a7ac8b0acc15, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q01
