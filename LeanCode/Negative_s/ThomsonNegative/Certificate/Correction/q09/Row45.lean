import ThomsonNegative.Certificate.Correction.q09.Input
import ThomsonNegative.Certificate.Correction.SourceData11

namespace ThomsonNegative.Certificate.Correction.q09
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
noncomputable def center45_0 : Nat := 0x37035b2dace05b85fd942916e95e9dfa88855d91d7a447984c1bf599a5f548561d3d48b202cd7046471214e01000
noncomputable def model45_0 : TM := ⟨0xb81ad96d6702dc2feca148b74af4efd4442aec8ebd223cc260dfaccd2faa42b0e9ea4590166b8232389, 0xb81ad96d6702dc2feca148b74af4efd4442aec8ebd223cc260dfaccd2faa42b0e9ea4590166b8232389, 0xb81ad96d6702dc2feca148b74af4efd4442aec8ebd223cc260dfaccd2faa42b0e9ea4590166b8232389, 0x4, true⟩
noncomputable def center45_1 : Nat := 0x4a2924e49422f08dafaddf9bd559853bc8c3b96d824b3d92229007195e8817596c37f12b758fb06a5a214d01000
noncomputable def model45_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51492724a117846d7d6efcdeaacc29de461dcb6c1259ec91148038caf440bacb61bf895bac7d8352d1, 0x5aeb6d8db5ee87b92829103215533d621b9e23493eda6136eeb7fc7350bbf45349e4076a453827cad2f, 0x5aeb6d8db5ee87b92829103215533d621b9e23493eda6136eeb7fc7350bbf45349e4076a453827cad2f, 0x4, true⟩
noncomputable def center45_2 : Nat := 0x63e08aacd08ba63e21147de382d0aacf0e2c1686543c1ebf4ffac7e8ec3f4f2d81583da8cddd9b4ff814a01000
noncomputable def model45_2 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff31f045566845d31f108a3ef1c168556787160b432a1e0f5fa7fd63f4761fa796c0ac1ed466eecda7fc, 0xce0fbaa997ba2ce0ef75c10e3e97aa9878e9f4bcd5e1f0a058029c0b89e058693f53e12b9911325804, 0xce0fbaa997ba2ce0ef75c10e3e97aa9878e9f4bcd5e1f0a058029c0b89e058693f53e12b9911325804, 0x4, true⟩
noncomputable def center45_3 : Nat := 0x231b9447da8fc4706d9f093badf967ec71d4b24feac487f6f927d0e6234323e97cd3f1d018d6735ac06615001000
noncomputable def model45_3 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd18dca23ed47e23836cf849dd6fcb3f638ea5927f56243fb7c93e87311a191f4be69f8e80c6b39ad6033, 0x2e7235dc12b81dc7c9307b6229034c09c715a6d80a9dbc04836c178cee5e6e0b41960717f394c6529fcd, 0x2e7235dc12b81dc7c9307b6229034c09c715a6d80a9dbc04836c178cee5e6e0b41960717f394c6529fcd, 0x4, true⟩
noncomputable def center45_4 : Nat := 0x3f55dcdeedb57be6dd35797fe5bd36627cb18e26201d9930ace67eef0d660fbf230b49be223af4f2dd7415001000
noncomputable def model45_4 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfaaee6f76dabdf36e9abcbff2de9b313e58c713100ecc9856733f7786b307df9185a4df111d7a796eba, 0x205511908925420c916543400d2164cec1a738eceff13367a98cc088794cf8206e7a5b20eee285869146, 0x205511908925420c916543400d2164cec1a738eceff13367a98cc088794cf8206e7a5b20eee285869146, 0x4, true⟩
noncomputable def center45_5 : Nat := 0x30e6eba2677d6e8b15de9fedc1c264bd4c3519c06a23f1acad2e207525fb33fcb9a1f5f4cd640be61b5ec15201000
noncomputable def model45_5 : TM := ⟨0x87375d133beb7458aef4ff6e0e1325ea61a8ce03511f8d65697103a92fd99fe5cd0fafa66b205f30daf6, 0x87375d133beb7458aef4ff6e0e1325ea61a8ce03511f8d65697103a92fd99fe5cd0fafa66b205f30daf6, 0x87375d133beb7458aef4ff6e0e1325ea61a8ce03511f8d65697103a92fd99fe5cd0fafa66b205f30daf6, 0x4, true⟩
noncomputable def center45_6 : Nat := 0x1b362d05d12b4517e308acb316ce6ca64c2e2b949b852cb122ee32661d6a18e6983777f20578987c3e74a15101000
noncomputable def model45_6 : TM := ⟨0x59b1682e895a28bf18456598b673653261715ca4dc29658917719330eb50c734c1bbbf902bc4c3e1f3a5, 0x59b1682e895a28bf18456598b673653261715ca4dc29658917719330eb50c734c1bbbf902bc4c3e1f3a5, 0x59b1682e895a28bf18456598b673653261715ca4dc29658917719330eb50c734c1bbbf902bc4c3e1f3a5, 0x4, true⟩
noncomputable def center45_7 : Nat := 0x58ebdfaf74f566b53e252f2ca1eb5e2c5494def3ff90fdbdccdb2b2a72108224c5458a0463490af8757a15101000
noncomputable def model45_7 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac75efd7ba7ab35a9f12979650f5af162a4a6f79ffc87edee66d95953908411262a2c50231a4857c3abd, 0x538a102845854ca560ed6869af0a50e9d5b590860037812119926a6ac6f7beed9d5d3afdce5b7a83c543, 0x538a102845854ca560ed6869af0a50e9d5b590860037812119926a6ac6f7beed9d5d3afdce5b7a83c543, 0x4, true⟩
noncomputable def center45_8 : Nat := 0xfefed28ceadd77947687a43122000c95816c5e08561f0e872c110a8e8af5dedb1b666927c3863c5013c15001000
noncomputable def model45_8 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7f7f6946756ebbca3b43d2189100064ac0b62f042b0f874396088547457aef6d8db33493e1c31e2809e, 0x3808096b98a914435c4bc2de76efff9b53f49d0fbd4f078bc69f77ab8ba851092724ccb6c1e3ce1d7f62, 0x3808096b98a914435c4bc2de76efff9b53f49d0fbd4f078bc69f77ab8ba851092724ccb6c1e3ce1d7f62, 0x4, true⟩
noncomputable def center45_9 : Nat := 0x1bd69f92647b9fd22ceb94066f613bc44c63a69722d0dab17de0e65e5f4b9522b76aea68f22b8e29c65214d01000
noncomputable def model45_9 : TM := ⟨0x5eb4fc9323dcfe91675ca0337b09de22631d34b91686d58bef0732f2fa5ca915bb575347915c714e329, 0x5eb4fc9323dcfe91675ca0337b09de22631d34b91686d58bef0732f2fa5ca915bb575347915c714e329, 0x5eb4fc9323dcfe91675ca0337b09de22631d34b91686d58bef0732f2fa5ca915bb575347915c714e329, 0x4, true⟩
noncomputable def center45_10 : Nat := 0x4c9cde821e606a8fab885e50b0e5a001f6249ae37e409466d617f5c476f30d55ad8d7bab6291ddfa69e14d01000
noncomputable def model45_10 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa64e6f410f303547d5c42f285872d000fb124d71bf204a336b0bfae23b7986aad6c6bdd5b148eefd34f, 0x59b190bef0cfcab82a3bd0d7a78d2fff04edb28e40dfb5cc94f4051dc48679552939422a4eb71102cb1, 0x59b190bef0cfcab82a3bd0d7a78d2fff04edb28e40dfb5cc94f4051dc48679552939422a4eb71102cb1, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q09
