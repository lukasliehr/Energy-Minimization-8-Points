import ThomsonNegative.Certificate.Correction.q07.Input
import ThomsonNegative.Certificate.Correction.SourceData11

namespace ThomsonNegative.Certificate.Correction.q07
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
noncomputable def center45_0 : Nat := 0x4f7b4b9e2f90ed5827e7f924ca3b138b630fa1a911ed7d0602356925bb53634b3f971603c51174fe9214901000
noncomputable def model45_0 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa7bda5cf17c876ac13f3fc92651d89c5b187d0d488f6be83011ab492dda9b1a59fcb8b01e288ba7f49, 0x58425a30e8378953ec0c036d9ae2763a4e782f2b7709417cfee54b6d22564e5a603474fe1d774580b7, 0x58425a30e8378953ec0c036d9ae2763a4e782f2b7709417cfee54b6d22564e5a603474fe1d774580b7, 0x4, true⟩
noncomputable def center45_1 : Nat := 0xd0ddc44b6e8aa1d76feab5cdac77069962e622b860ccab1e152a11493e6bfdabed425471c8c7a07dca14a01000
noncomputable def model45_1 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff686ee225b74550ebb7f55ae6d63b834cb173115c3066558f0a9508a49f35fed5f6a12a38e463d03ee5, 0x97911dda48baaf14480aa51929c47cb34e8ceea3cf99aa70f56af75b60ca012a095ed5c71b9c2fc11b, 0x97911dda48baaf14480aa51929c47cb34e8ceea3cf99aa70f56af75b60ca012a095ed5c71b9c2fc11b, 0x4, true⟩
noncomputable def center45_2 : Nat := 0xd16f9451cef17bb9715a5d5df2e116114e70e5703bd50331e8f5db7e99f6cd14df49f21de930ea724b414c01000
noncomputable def model45_2 : TM := ⟨0x28b7ca28e778bddcb8ad2eaef9708b08a73872b81dea8198f47aedbf4cfb668a6fa4f90ef498753925a, 0x28b7ca28e778bddcb8ad2eaef9708b08a73872b81dea8198f47aedbf4cfb668a6fa4f90ef498753925a, 0x28b7ca28e778bddcb8ad2eaef9708b08a73872b81dea8198f47aedbf4cfb668a6fa4f90ef498753925a, 0x4, true⟩
noncomputable def center45_3 : Nat := 0xeac3341075822ffc5dc127792701eb556be345f6c7f25bba055471b0fbdc483e8113296310cf9d38ef2e15001000
noncomputable def model45_3 : TM := ⟨0x35619a083ac117fe2ee093bc9380f5aab5f1a2fb63f92ddd02aa38d87dee241f408994b18867ce9c7797, 0x35619a083ac117fe2ee093bc9380f5aab5f1a2fb63f92ddd02aa38d87dee241f408994b18867ce9c7797, 0x35619a083ac117fe2ee093bc9380f5aab5f1a2fb63f92ddd02aa38d87dee241f408994b18867ce9c7797, 0x4, true⟩
noncomputable def center45_4 : Nat := 0x1432af578dd9b55f8015f67b83cacfafa2b6e7aa34c4222dc7dede985657e5629419fbbb34f0a4d11ad015001000
noncomputable def model45_4 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffca1957abc6ecdaafc00afb3dc1e567d7d15b73d51a621116e3ef6f4c2b2bf2b14a0cfddd9a7852688d68, 0x35e6a854391325503ff504c23e1a98282ea48c2ae59deee91c1090b3d4d40d4eb5f302226587ad977298, 0x35e6a854391325503ff504c23e1a98282ea48c2ae59deee91c1090b3d4d40d4eb5f302226587ad977298, 0x4, true⟩
noncomputable def center45_5 : Nat := 0x1ea5cdbbe26cb371f909c3db494b721040e436d546b485a30b8c980ce48a9fe084644b9c68661c1044a415101000
noncomputable def model45_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f52e6ddf13659b8fc84e1eda4a5b90820721b6aa35a42d185c64c0672454ff0423225ce34330e082252, 0x70ad19220ec9a647037b1e125b5a46f7df8de4955ca5bd2e7a39b3f98dbab00fbdcdda31cbccf1f7ddae, 0x70ad19220ec9a647037b1e125b5a46f7df8de4955ca5bd2e7a39b3f98dbab00fbdcdda31cbccf1f7ddae, 0x4, true⟩
noncomputable def center45_6 : Nat := 0xe4973157e9d9af8dfafc6536fe956bb7ab227d2187871afb65682c0eeb1667cfb4f674f1183c13dc468815001000
noncomputable def model45_6 : TM := ⟨0x324b98abf4ecd7c6fd7e329b7f4ab5dbd5913e90c3c38d7db2b41607758b33e7da7b3a788c1e09ee2344, 0x324b98abf4ecd7c6fd7e329b7f4ab5dbd5913e90c3c38d7db2b41607758b33e7da7b3a788c1e09ee2344, 0x324b98abf4ecd7c6fd7e329b7f4ab5dbd5913e90c3c38d7db2b41607758b33e7da7b3a788c1e09ee2344, 0x4, true⟩
noncomputable def center45_7 : Nat := 0x19ed18da740eb867cf286d41cdc67d8907f24b59558906cdcc85d8900fe9aadb0b7842c2c042e0640fbbe15101000
noncomputable def model45_7 : TM := ⟨0x4f68c6d3a075c33e79436a0e6e33ec483f925acaac48366e642ec4807f4d56d85bc21616021703207ddf, 0x4f68c6d3a075c33e79436a0e6e33ec483f925acaac48366e642ec4807f4d56d85bc21616021703207ddf, 0x4f68c6d3a075c33e79436a0e6e33ec483f925acaac48366e642ec4807f4d56d85bc21616021703207ddf, 0x4, true⟩
noncomputable def center45_8 : Nat := 0x33fb8b2892b19851a315e9af1e3377598fdeda83c4613783530ffabfbe02dbc595ef10aec097826f13b414e01000
noncomputable def model45_8 : TM := ⟨0x9fdc5944958cc28d18af4d78f19bbacc7ef6d41e2309bc1a987fd5fdf016de2caf78857604bc13789da, 0x9fdc5944958cc28d18af4d78f19bbacc7ef6d41e2309bc1a987fd5fdf016de2caf78857604bc13789da, 0x9fdc5944958cc28d18af4d78f19bbacc7ef6d41e2309bc1a987fd5fdf016de2caf78857604bc13789da, 0x4, true⟩
noncomputable def center45_9 : Nat := 0x572c0f6aff5b97fe18ee74e97914bf7342048119b4bb6acef53f9293e95ffddfac6d90781e7c41621fe14e01000
noncomputable def model45_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2b9607b57fadcbff0c773a74bc8a5fb9a102408cda5db5677a9fc949f4affeefd636c83c0f3e20b10ff, 0xd469f84a80523400f388c58b4375a0465efdbf7325a24a98856036b60b50011029c937c3f0c1df4ef01, 0xd469f84a80523400f388c58b4375a0465efdbf7325a24a98856036b60b50011029c937c3f0c1df4ef01, 0x4, true⟩
noncomputable def center45_10 : Nat := 0xae84812ae3743d01c76d1adfc43ed8f5c3988cdd4210e9f044c9ed84d3c6ddb88768f49da361250b90a14e01000
noncomputable def model45_10 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5742409571ba1e80e3b68d6fe21f6c7ae1cc466ea10874f82264f6c269e36edc43b47a4ed1b09285c85, 0xa8bdbf6a8e45e17f1c4972901de093851e33b9915ef78b07dd9b093d961c9123bc4b85b12e4f6d7a37b, 0xa8bdbf6a8e45e17f1c4972901de093851e33b9915ef78b07dd9b093d961c9123bc4b85b12e4f6d7a37b, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q07
