import ThomsonNegative.Certificate.Correction.q07.Input
import ThomsonNegative.Certificate.Correction.SourceData02

namespace ThomsonNegative.Certificate.Correction.q07
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
noncomputable def center11_0 : Nat := 0x3e93ec58bd95cf45116e2f3212080c036f38cc51bf26c0798066d16200db702d7b97f6541a8a33af7e14601000
noncomputable def model11_0 : TM := ⟨0xf49f62c5ecae7a288b7179909040601b79c6628df93603cc03368b1006db816bdcbfb2a0d4519d7bf, 0xf49f62c5ecae7a288b7179909040601b79c6628df93603cc03368b1006db816bdcbfb2a0d4519d7bf, 0xf49f62c5ecae7a288b7179909040601b79c6628df93603cc03368b1006db816bdcbfb2a0d4519d7bf, 0x4, true⟩
noncomputable def center11_1 : Nat := 0x320641f4530885e006cacacc3600dcf0082b57794c23d3104fe393cb0c271ce3ee5e37f9ce7e83e819614a01000
noncomputable def model11_1 : TM := ⟨0x90320fa298442f0036565661b006e780415abbca611e98827f1c9e586138e71f72f1bfce73f41f40cb, 0x90320fa298442f0036565661b006e780415abbca611e98827f1c9e586138e71f72f1bfce73f41f40cb, 0x90320fa298442f0036565661b006e780415abbca611e98827f1c9e586138e71f72f1bfce73f41f40cb, 0x4, true⟩
noncomputable def center11_2 : Nat := 0x6b84953395780dc1d0034a3402700376b584791e88c856f050ed7a361de647ed58eef7993802e518c3814b01000
noncomputable def model11_2 : TM := ⟨0x15c24a99cabc06e0e801a51a013801bb5ac23c8f44642b782876bd1b0ef323f6ac777bcc9c01728c61c, 0x15c24a99cabc06e0e801a51a013801bb5ac23c8f44642b782876bd1b0ef323f6ac777bcc9c01728c61c, 0x15c24a99cabc06e0e801a51a013801bb5ac23c8f44642b782876bd1b0ef323f6ac777bcc9c01728c61c, 0x4, true⟩
noncomputable def center11_3 : Nat := 0x3226ed55115244bf6863fc77927e9bdc8c131cebfa76a51d3d695a24d9adda268a21d4827f39986e9b414d01000
noncomputable def model11_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff991376aa88a9225fb431fe3bc93f4dee46098e75fd3b528e9eb4ad126cd6ed134510ea413f9ccc374da, 0x66ec89557756dda04bce01c436c0b211b9f6718a02c4ad71614b52ed932912ecbaef15bec06333c8b26, 0x66ec89557756dda04bce01c436c0b211b9f6718a02c4ad71614b52ed932912ecbaef15bec06333c8b26, 0x4, true⟩
noncomputable def center11_4 : Nat := 0x33f8348d8442fbb3599ebeebb81ca75312e514c565826942a0c266f811823996acbaae8db4448f30f5214a01000
noncomputable def model11_4 : TM := ⟨0x9fc1a46c2217dd9accf5f75dc0e53a989728a62b2c134a15061337c08c11ccb565d5746da2247987a9, 0x9fc1a46c2217dd9accf5f75dc0e53a989728a62b2c134a15061337c08c11ccb565d5746da2247987a9, 0x9fc1a46c2217dd9accf5f75dc0e53a989728a62b2c134a15061337c08c11ccb565d5746da2247987a9, 0x4, true⟩
noncomputable def center11_5 : Nat := 0x373bc0a10e445a6bcb38c8dc8b9317b6349fbdae4ec18e4c2ccdc5b8390606eb31d00c55d072736bbf2814e01000
noncomputable def model11_5 : TM := ⟨0xb9de05087222d35e59c646e45c98bdb1a4fded72760c7261666e2dc1c83037598e8062ae83939b5df94, 0xb9de05087222d35e59c646e45c98bdb1a4fded72760c7261666e2dc1c83037598e8062ae83939b5df94, 0xb9de05087222d35e59c646e45c98bdb1a4fded72760c7261666e2dc1c83037598e8062ae83939b5df94, 0x4, true⟩
noncomputable def center11_6 : Nat := 0x3a76353f526963b8ba22245c91b22c8b20ef3eab197ddfdd4a68d80b0830342581a0a06bf6bdf25f8c14b01000
noncomputable def model11_6 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1d3b1a9fa934b1dc5d11122e48d9164590779f558cbeefeea5346c0584181a12c0d05035fb5ef92fc6, 0x1e2c4e56056cb4e23a2eeedd1b726e9ba6f8860aa734110115acb93fa7be7e5ed3f2fafca04a106d03a, 0x1e2c4e56056cb4e23a2eeedd1b726e9ba6f8860aa734110115acb93fa7be7e5ed3f2fafca04a106d03a, 0x4, true⟩
noncomputable def center11_7 : Nat := 0xe6e249f8482af0d85cf1669a6caa5d140df441f3073eee17b96ee0446cf4d42fa217ab80502f4eb285c14e01000
noncomputable def model11_7 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff737124fc2415786c2e78b34d36552e8a06fa20f9839f770bdcb77022367a6a17d10bd5c02817a75942e, 0x8c8edb03dbea8793d1874cb2c9aad175f905df067c6088f423488fddc98595e82ef42a3fd7e858a6bd2, 0x8c8edb03dbea8793d1874cb2c9aad175f905df067c6088f423488fddc98595e82ef42a3fd7e858a6bd2, 0x4, true⟩
noncomputable def center11_8 : Nat := 0xc3b003e705a662b1d2c0dd3ef8b8654f2053b61f6c1c539e244e8ce41eaa45a1d22e90e02a852ff9c14401000
noncomputable def model11_8 : TM := ⟨0x21d801f382d33158e9606e9f7c5c32a79029db0fb60e29cf122746720f5522d0e9174870154297fce, 0x21d801f382d33158e9606e9f7c5c32a79029db0fb60e29cf122746720f5522d0e9174870154297fce, 0x21d801f382d33158e9606e9f7c5c32a79029db0fb60e29cf122746720f5522d0e9174870154297fce, 0x4, true⟩
noncomputable def center11_9 : Nat := 0xc0358a6f6957033a057f9b5313185f2456699f895e8b9dd9b1d41a18f58a5ca243aa4f59683e0fc64d014c01000
noncomputable def model11_9 : TM := ⟨0x201ac537b4ab819d02bfcda9898c2f922b34cfc4af45ceecd8ea0d0c7ac52e5121d527acb41f07e3268, 0x201ac537b4ab819d02bfcda9898c2f922b34cfc4af45ceecd8ea0d0c7ac52e5121d527acb41f07e3268, 0x201ac537b4ab819d02bfcda9898c2f922b34cfc4af45ceecd8ea0d0c7ac52e5121d527acb41f07e3268, 0x4, true⟩
noncomputable def center11_10 : Nat := 0x3c308fb62630b96cf0af90a30c8c3c022672fe9383141184c1e0045e75f577de20bb93c8a02ca21254014a01000
noncomputable def model11_10 : TM := ⟨0xe1847db13185cb67857c85186461e0113397f49c18a08c260f0022f3afabbef105dc9e4501651092a0, 0xe1847db13185cb67857c85186461e0113397f49c18a08c260f0022f3afabbef105dc9e4501651092a0, 0xe1847db13185cb67857c85186461e0113397f49c18a08c260f0022f3afabbef105dc9e4501651092a0, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q07
