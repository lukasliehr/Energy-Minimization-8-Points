import ThomsonNegative.Certificate.Correction.q01.Input
import ThomsonNegative.Certificate.Correction.SourceData02

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm11 : Nat := 0x2
noncomputable def inverse11 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse11_checked : sameTM (denominatorInverse context argument Source.r11d norm11) inverse11=true := by decide +kernel
theorem norm11_positive : 0 < norm11 := by decide +kernel
noncomputable def columns11 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a, 0x1, 0x1]
theorem columns11_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse11 (Source.r11n j) norm11 1; M.ok && Nat.beq (rangeX context M) (columns11.getD j 0))=true := by decide +kernel
noncomputable def center11_0 : Nat := 0xd62ca3114650e0289033e0a08edb87689e5a47e79b39e219598f912cbf8e42752629bdede1584c567e14a01000
noncomputable def model11_0 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6b165188a32870144819f050476dc3b44f2d23f3cd9cf10cacc7c8965fc7213a9314def6f0ac262b3f, 0x94e9ae775cd78febb7e60fafb8923c4bb0d2dc0c32630ef353383769a038dec56ceb21090f53d9d4c1, 0x94e9ae775cd78febb7e60fafb8923c4bb0d2dc0c32630ef353383769a038dec56ceb21090f53d9d4c1, 0x4, true⟩
noncomputable def center11_1 : Nat := 0x3086c5c840ce5340127b39590ec28a789c6e781f5a5b646e19c730e8c3433b636462ae9c2fcd26f19be14a01000
noncomputable def model11_1 : TM := ⟨0x84362e4206729a0093d9cac8761453c4e373c0fad2db2370ce3987461a19db1b231574e17e69378cdf, 0x84362e4206729a0093d9cac8761453c4e373c0fad2db2370ce3987461a19db1b231574e17e69378cdf, 0x84362e4206729a0093d9cac8761453c4e373c0fad2db2370ce3987461a19db1b231574e17e69378cdf, 0x4, true⟩
noncomputable def center11_2 : Nat := 0x3ae7317bd0419ae686524fcca42152e72a110233bd113b9c695b51e9fae94270bd12af8e284db9d978c14a01000
noncomputable def model11_2 : TM := ⟨0xd7398bde820cd73432927e65210a97395088119de889dce34ada8f4fd74a1385e8957c71426dcecbc6, 0xd7398bde820cd73432927e65210a97395088119de889dce34ada8f4fd74a1385e8957c71426dcecbc6, 0xd7398bde820cd73432927e65210a97395088119de889dce34ada8f4fd74a1385e8957c71426dcecbc6, 0x4, true⟩
noncomputable def center11_3 : Nat := 0x7236c846244faf0221e383f9ff651e5abf1451cec53d9f9f83ec1c32ad1f2972fb14a2a57bfb961d38e14d01000
noncomputable def model11_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb91b64231227d78110f1c1fcffb28f2d5f8a28e7629ecfcfc1f60e19568f94b97d8a5152bdfdcb0e9c7, 0x46e49bdcedd8287eef0e3e03004d70d2a075d7189d6130303e09f1e6a9706b468275aead420234f1639, 0x46e49bdcedd8287eef0e3e03004d70d2a075d7189d6130303e09f1e6a9706b468275aead420234f1639, 0x4, true⟩
noncomputable def center11_4 : Nat := 0x90193c210516d8241302aec3989baecaac0bd9eeb5cdf6c57d298fbd5a44ff71f68d02497c68a42ad414a01000
noncomputable def model11_4 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff480c9e10828b6c1209815761cc4dd7655605ecf75ae6fb62be94c7dead227fb8fb468124be3452156a, 0xb7f361ef7d7493edf67ea89e33b2289aa9fa1308a519049d416b382152dd804704b97edb41cbadea96, 0xb7f361ef7d7493edf67ea89e33b2289aa9fa1308a519049d416b382152dd804704b97edb41cbadea96, 0x4, true⟩
noncomputable def center11_5 : Nat := 0x1e70b34833f844fb42d5ab27b10c60b7a06f68ad96e00601f1300d1b648551a2593ec7435d4f7b0d0f4a14d01000
noncomputable def model11_5 : TM := ⟨0x73859a419fc227da16ad593d886305bd037b456cb700300f898068db242a8d12c9f63a1aea7bd8687a5, 0x73859a419fc227da16ad593d886305bd037b456cb700300f898068db242a8d12c9f63a1aea7bd8687a5, 0x73859a419fc227da16ad593d886305bd037b456cb700300f898068db242a8d12c9f63a1aea7bd8687a5, 0x4, true⟩
noncomputable def center11_6 : Nat := 0xc3ab31ad82361b22c104924e623f0a54186eef7a2002da718abbce05d40b1b4c349cc970ce426c7a48814c01000
noncomputable def model11_6 : TM := ⟨0x21d598d6c11b0d9160824927311f852a0c3777bd10016d38c55de702ea058da61a4e64b86721363d244, 0x21d598d6c11b0d9160824927311f852a0c3777bd10016d38c55de702ea058da61a4e64b86721363d244, 0x21d598d6c11b0d9160824927311f852a0c3777bd10016d38c55de702ea058da61a4e64b86721363d244, 0x4, true⟩
noncomputable def center11_7 : Nat := 0x16c878e71d02fd3b2f7c14dbdb89e0c91e3b91600e682833627c97e401dae19098df2523e9d1cad333a14c01000
noncomputable def model11_7 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcb643c738e817e9d97be0a6dedc4f0648f1dc8b007341419b13e4bf200ed70c84c6f9291f4e8e56999d, 0x349bc38c717e81626841f592123b0f9b70e2374ff8cbebe64ec1b40dff128f37b3906d6e0b171a96663, 0x349bc38c717e81626841f592123b0f9b70e2374ff8cbebe64ec1b40dff128f37b3906d6e0b171a96663, 0x4, true⟩
noncomputable def center11_8 : Nat := 0x178c93add4ba2eedf47631598a7fcec80f1096e3536bf31f01da1b7eb3eb79c2042f5cf4cfbdfa60b5214b01000
noncomputable def model11_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffebc649d6ea5d1776fa3b18acc53fe76407884b71a9b5f98f80ed0dbf59f5bce10217ae7a67defd305a9, 0x1439b62915a2e88905c4e7533ac0189bf877b48e564a06707f12f240a60a431efde85185982102cfa57, 0x1439b62915a2e88905c4e7533ac0189bf877b48e564a06707f12f240a60a431efde85185982102cfa57, 0x4, true⟩
noncomputable def center11_9 : Nat := 0x37323c18128cfe7a1927dde7b06e9170e966a835491ed3c6989d8438ea913f86b981dbb6fdf2c88e3c814a01000
noncomputable def model11_9 : TM := ⟨0xb991e0c09467f3d0c93eef3d83748b874b3541aa48f69e34c4ec21c75489fc35cc0eddb7ef964471e4, 0xb991e0c09467f3d0c93eef3d83748b874b3541aa48f69e34c4ec21c75489fc35cc0eddb7ef964471e4, 0xb991e0c09467f3d0c93eef3d83748b874b3541aa48f69e34c4ec21c75489fc35cc0eddb7ef964471e4, 0x4, true⟩
noncomputable def center11_10 : Nat := 0xee376ab4ba135ed97434fd0c08251c6cd3556739f7c52b73a6c2a7534f1bf54a25ef5c3571aa44390014801000
noncomputable def model11_10 : TM := ⟨0x371bb55a5d09af6cba1a7e8604128e3669aab39cfbe295b9d36153a9a78dfaa512f7ae1ab8d5221c80, 0x371bb55a5d09af6cba1a7e8604128e3669aab39cfbe295b9d36153a9a78dfaa512f7ae1ab8d5221c80, 0x371bb55a5d09af6cba1a7e8604128e3669aab39cfbe295b9d36153a9a78dfaa512f7ae1ab8d5221c80, 0x4, true⟩
noncomputable def centers11 : Nat → Nat
  | 0 => center11_0
  | 1 => center11_1
  | 2 => center11_2
  | 3 => center11_3
  | 4 => center11_4
  | 5 => center11_5
  | 6 => center11_6
  | 7 => center11_7
  | 8 => center11_8
  | 9 => center11_9
  | 10 => center11_10
  | _ => 0x100000
noncomputable def models11 : Nat → TM
  | 0 => model11_0
  | 1 => model11_1
  | 2 => model11_2
  | 3 => model11_3
  | 4 => model11_4
  | 5 => model11_5
  | 6 => model11_6
  | 7 => model11_7
  | 8 => model11_8
  | 9 => model11_9
  | 10 => model11_10
  | _ => zeroTM
theorem centers11_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse11 (centers11 k) norm11 (Nat.pow 2 384)) (models11 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
