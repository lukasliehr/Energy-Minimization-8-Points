import ThomsonNegative.Certificate.Correction.q05.Input
import ThomsonNegative.Certificate.Correction.SourceData11

namespace ThomsonNegative.Certificate.Correction.q05
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
noncomputable def center45_0 : Nat := 0x1fa2ce096ef78a69e1c14e0a12a49b1018dd7f78c0b039797733e7280caa1948ab5edcd0a5f1121f25214901000
noncomputable def model45_0 : TM := ⟨0x7d16704b77bc534f0e0a70509524d880c6ebfbc60581cbcbb99f39406550ca455af6e6852f8890f929, 0x7d16704b77bc534f0e0a70509524d880c6ebfbc60581cbcbb99f39406550ca455af6e6852f8890f929, 0x7d16704b77bc534f0e0a70509524d880c6ebfbc60581cbcbb99f39406550ca455af6e6852f8890f929, 0x4, true⟩
noncomputable def center45_1 : Nat := 0x39594b3ddcb5c4ff372f2af4d74adf5786a0b1af31d0444c2437165072f5d6f9bb99c6c029a83ae563e414e01000
noncomputable def model45_1 : TM := ⟨0xcaca59eee5ae27f9b97957a6ba56fabc35058d798e82226121b8b28397aeb7cddcce36014d41d72b1f2, 0xcaca59eee5ae27f9b97957a6ba56fabc35058d798e82226121b8b28397aeb7cddcce36014d41d72b1f2, 0xcaca59eee5ae27f9b97957a6ba56fabc35058d798e82226121b8b28397aeb7cddcce36014d41d72b1f2, 0x4, true⟩
noncomputable def center45_2 : Nat := 0x36cd134101858fcc1c83dca0162ba3207c62c10ad2bd8a70aba84ac32c221a04ab8c93fabfcaf255f4ea14e01000
noncomputable def model45_2 : TM := ⟨0xb6689a080c2c7e60e41ee500b15d1903e316085695ec53855d4256196110d0255c649fd5fe5792afa75, 0xb6689a080c2c7e60e41ee500b15d1903e316085695ec53855d4256196110d0255c649fd5fe5792afa75, 0xb6689a080c2c7e60e41ee500b15d1903e316085695ec53855d4256196110d0255c649fd5fe5792afa75, 0x4, true⟩
noncomputable def center45_3 : Nat := 0x26ebca85e0f7de6b40d244e0e657ededce991f8b8082166ae49271dc49f18b34c727c802bd45ec3d482215001000
noncomputable def model45_3 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd375e542f07bef35a0692270732bf6f6e74c8fc5c0410b35724938ee24f8c59a6393e4015ea2f61ea411, 0x2c8a1abd0f8410ca5f96dd8f8cd4090918b3703a3fbef4ca8db6c711db073a659c6c1bfea15d09e15bef, 0x2c8a1abd0f8410ca5f96dd8f8cd4090918b3703a3fbef4ca8db6c711db073a659c6c1bfea15d09e15bef, 0x4, true⟩
noncomputable def center45_4 : Nat := 0x29449edeac571370174e5a271fbee129de0e689f3ea9f76fba353dc9c360be5da620a8516f126e14550e15001000
noncomputable def model45_4 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd4a24f6f562b89b80ba72d138fdf7094ef07344f9f54fbb7dd1a9ee4e1b05f2ed3105428b789370a2a87, 0x2b5db090a9d47647f458d2ec70208f6b10f8cbb060ab044822e5611b1e4fa0d12cefabd74876c8f5d579, 0x2b5db090a9d47647f458d2ec70208f6b10f8cbb060ab044822e5611b1e4fa0d12cefabd74876c8f5d579, 0x4, true⟩
noncomputable def center45_5 : Nat := 0x79a97a77320ab8e27dbcd122b42482269069d581d29ec9ed6d792a481e7039b1ca1c88a7fc75b28c8daa14f01000
noncomputable def model45_5 : TM := ⟨0x1cd4bd3b99055c713ede68915a1241134834eac0e94f64f6b6bc95240f381cd8e50e4453fe3ad94646d5, 0x1cd4bd3b99055c713ede68915a1241134834eac0e94f64f6b6bc95240f381cd8e50e4453fe3ad94646d5, 0x1cd4bd3b99055c713ede68915a1241134834eac0e94f64f6b6bc95240f381cd8e50e4453fe3ad94646d5, 0x4, true⟩
noncomputable def center45_6 : Nat := 0xdbdb82d8835ef0a8fb319facaac93d80c2c0a196d2fe30e9bb2e72c9e37f23a28729f64bd386eb21c25815001000
noncomputable def model45_6 : TM := ⟨0x2dedc16c41af78547d98cfd655649ec0616050cb697f1874dd973964f1bf91d14394fb25e9c37590e12c, 0x2dedc16c41af78547d98cfd655649ec0616050cb697f1874dd973964f1bf91d14394fb25e9c37590e12c, 0x2dedc16c41af78547d98cfd655649ec0616050cb697f1874dd973964f1bf91d14394fb25e9c37590e12c, 0x4, true⟩
noncomputable def center45_7 : Nat := 0x368cd4e0b04cbf01a0ce22deee8369d7131354cce31f35d3edb799617c893085a09eab6c1122cffa4b5e14e01000
noncomputable def model45_7 : TM := ⟨0xb466a7058265f80d067116f7741b4eb8989aa66718f9ae9f6dbccb0be449842d04f55b6089167fd25af, 0xb466a7058265f80d067116f7741b4eb8989aa66718f9ae9f6dbccb0be449842d04f55b6089167fd25af, 0xb466a7058265f80d067116f7741b4eb8989aa66718f9ae9f6dbccb0be449842d04f55b6089167fd25af, 0x4, true⟩
noncomputable def center45_8 : Nat := 0x1c8def36f582330c5752e02a9aaaaf59fd7d66bacefe17552475dea5cab8b671db9a8e1aa9c1ec890bc814f01000
noncomputable def model45_8 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee46f79b7ac119862ba970154d5557acfebeb35d677f0baa923aef52e55c5b38edcd470d54e0f64485e4, 0x11b90864853ee679d4568feab2aaa85301414ca29880f4556dc510ad1aa3a4c71232b8f2ab1f09bb7a1c, 0x11b90864853ee679d4568feab2aaa85301414ca29880f4556dc510ad1aa3a4c71232b8f2ab1f09bb7a1c, 0x4, true⟩
noncomputable def center45_9 : Nat := 0x14b41c32565d3dc53aa419d65f298833d62bd1facc99ef93dbf2e1732cb506db3ae730a654c72cc1e7a14c01000
noncomputable def model45_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffca5a0e192b2e9ee29d520ceb2f94c419eb15e8fd664cf7c9edf970b9965a836d9d7398532a639660f3d, 0x35a5f1e6d4d1611d62adf314d06b3be614ea170299b3083612068f4669a57c92628c67acd59c699f0c3, 0x35a5f1e6d4d1611d62adf314d06b3be614ea170299b3083612068f4669a57c92628c67acd59c699f0c3, 0x4, true⟩
noncomputable def center45_10 : Nat := 0x61791c7c6cbb469144b3c95beb2072732dcb2a84e644f3dc21e7a5869470a09c4a51514c927f1cb36014901000
noncomputable def model45_10 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb0bc8e3e365da348a259e4adf590393996e59542732279ee10f3d2c34a38504e2528a8a6493f8e59b0, 0x4f4371c1c9a25cb75da61b520a6fc6c6691a6abd8cdd8611ef0c2d3cb5c7afb1dad75759b6c071a650, 0x4f4371c1c9a25cb75da61b520a6fc6c6691a6abd8cdd8611ef0c2d3cb5c7afb1dad75759b6c071a650, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q05
