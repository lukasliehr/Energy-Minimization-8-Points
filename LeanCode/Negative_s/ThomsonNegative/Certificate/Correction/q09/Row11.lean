import ThomsonNegative.Certificate.Correction.q09.Input
import ThomsonNegative.Certificate.Correction.SourceData02

namespace ThomsonNegative.Certificate.Correction.q09
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
noncomputable def center11_0 : Nat := 0x1c915fbf8d8c4adb395f69de42b7bc3a849c984be430189f0cc8d9367fe3d7ed2dfc6070c1f4bf3a9c614b01000
noncomputable def model11_0 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee48afdfc6c6256d9cafb4ef215bde1d424e4c25f2180c4f86646c9b3ff1ebf696fe303860fa5f9d4e3, 0x11b750203939da9263504b10dea421e2bdb1b3da0de7f3b0799b9364c00e14096901cfc79f05a062b1d, 0x11b750203939da9263504b10dea421e2bdb1b3da0de7f3b0799b9364c00e14096901cfc79f05a062b1d, 0x4, true⟩
noncomputable def center11_1 : Nat := 0x77ff14e770875636b95ee6b3e04ae243fd0a552ab6555a7e2e4fd50c7d7a7c150a4c227da2850bb97014a01000
noncomputable def model11_1 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3bff8a73b843ab1b5caf7359f0257121fe852a955b2aad3f1727ea863ebd3e0a8526113ed14285dcb8, 0xc400758c47bc54e4a3508ca60fda8ede017ad56aa4d552c0e8d81579c142c1f57ad9eec12ebd7a2348, 0xc400758c47bc54e4a3508ca60fda8ede017ad56aa4d552c0e8d81579c142c1f57ad9eec12ebd7a2348, 0x4, true⟩
noncomputable def center11_2 : Nat := 0x1e11c0a8f691b335f5d43a91d737febabe873a38210d69ac5a2a544619754eb0a9dedb95847d8d205b414b01000
noncomputable def model11_2 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef08e0547b48d99afaea1d48eb9bff5d5f439d1c1086b4d62d152a230cbaa75854ef6dcac23ec6902da, 0x10f71fab84b726650515e2b7146400a2a0bc62e3ef794b29d2ead5dcf34558a7ab1092353dc1396fd26, 0x10f71fab84b726650515e2b7146400a2a0bc62e3ef794b29d2ead5dcf34558a7ab1092353dc1396fd26, 0x4, true⟩
noncomputable def center11_3 : Nat := 0x1f39124a44b26ab37d65031221d408f70ce2e2343c84f3e50062ac296cc530837ccb2c0cf2ac087d60cc14d01000
noncomputable def model11_3 : TM := ⟨0x79c892522593559beb2818910ea047b8671711a1e4279f280315614b6629841be6596067956043eb066, 0x79c892522593559beb2818910ea047b8671711a1e4279f280315614b6629841be6596067956043eb066, 0x79c892522593559beb2818910ea047b8671711a1e4279f280315614b6629841be6596067956043eb066, 0x4, true⟩
noncomputable def center11_4 : Nat := 0x7a7077eb7784b0ae7e3863ec18832c730fb890a25cbc91dac19562d41978c681e849bd3c0eaed2078be14b01000
noncomputable def model11_4 : TM := ⟨0x1d383bf5bbc258573f1c31f60c41963987dc48512e5e48ed60cab16a0cbc6340f424de9e07576903c5f, 0x1d383bf5bbc258573f1c31f60c41963987dc48512e5e48ed60cab16a0cbc6340f424de9e07576903c5f, 0x1d383bf5bbc258573f1c31f60c41963987dc48512e5e48ed60cab16a0cbc6340f424de9e07576903c5f, 0x4, true⟩
noncomputable def center11_5 : Nat := 0x1aba9360eaf50c222c4af17f6f353c9a698221d3df1a7b0be20760da3705ca7bdfca83b1258aa2e3c21a14f01000
noncomputable def model11_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed5d49b0757a8611162578bfb79a9e4d34c110e9ef8d3d85f103b06d1b82e53defe541d892c55171e10d, 0x12a2b64f8a8579eee9da8740486561b2cb3eef161072c27a0efc4f92e47d1ac2101abe276d3aae8e1ef3, 0x12a2b64f8a8579eee9da8740486561b2cb3eef161072c27a0efc4f92e47d1ac2101abe276d3aae8e1ef3, 0x4, true⟩
noncomputable def center11_6 : Nat := 0x1a6117057e600631c60189a4158c869cd426f1d207c86cb1417b3097d54363c3c739f730fa79aa8b9a14d01000
noncomputable def model11_6 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80d308b82bf300318e300c4d20ac6434e6a1378e903e43658a0bd984beaa1b1e1e39cfb987d3cd545cd, 0x7f2cf747d40cffce71cff3b2df539bcb195ec8716fc1bc9a75f4267b4155e4e1e1c63046782c32aba33, 0x7f2cf747d40cffce71cff3b2df539bcb195ec8716fc1bc9a75f4267b4155e4e1e1c63046782c32aba33, 0x4, true⟩
noncomputable def center11_7 : Nat := 0x34a9e98743d877b04bc6d7472c3de731ed800706d664cb4b5b731d81824ea528b81af846f6c9c01ed8b014e01000
noncomputable def model11_7 : TM := ⟨0xa54f4c3a1ec3bd825e36ba3961ef398f6c003836b3265a5adb98ec0c12752945c0d7c237b64e00f6c58, 0xa54f4c3a1ec3bd825e36ba3961ef398f6c003836b3265a5adb98ec0c12752945c0d7c237b64e00f6c58, 0xa54f4c3a1ec3bd825e36ba3961ef398f6c003836b3265a5adb98ec0c12752945c0d7c237b64e00f6c58, 0x4, true⟩
noncomputable def center11_8 : Nat := 0x19ab549855ae84326f7e0ca9fc1fcd39eb6d8e8631c59753a7495b6f5d24a7235f64218b0bd8cc5dcb6a14d01000
noncomputable def model11_8 : TM := ⟨0x4d5aa4c2ad7421937bf0654fe0fe69cf5b6c74318e2cba9d3a4adb7ae925391afb210c585ec662ee5b5, 0x4d5aa4c2ad7421937bf0654fe0fe69cf5b6c74318e2cba9d3a4adb7ae925391afb210c585ec662ee5b5, 0x4d5aa4c2ad7421937bf0654fe0fe69cf5b6c74318e2cba9d3a4adb7ae925391afb210c585ec662ee5b5, 0x4, true⟩
noncomputable def center11_9 : Nat := 0xc0366f8fad740848496751981c514a02669a7bada8afe67d0311bd8dc9646867d8326de88f41c3ee7614801000
noncomputable def model11_9 : TM := ⟨0x201b37c7d6ba042424b3a8cc0e28a501334d3dd6d457f33e8188dec6e4b23433ec1936f447a0e1f73b, 0x201b37c7d6ba042424b3a8cc0e28a501334d3dd6d457f33e8188dec6e4b23433ec1936f447a0e1f73b, 0x201b37c7d6ba042424b3a8cc0e28a501334d3dd6d457f33e8188dec6e4b23433ec1936f447a0e1f73b, 0x4, true⟩
noncomputable def center11_10 : Nat := 0x336b2662fe92f7d2107e3c1ce89d67ee0ce40eb12ffd5be9a69a91046ee03aaf970b8179c4cc1aac72a14a01000
noncomputable def model11_10 : TM := ⟨0x9b593317f497be9083f1e0e744eb3f70672075897feadf4d34d488237701d57cb85c0bce2660d56395, 0x9b593317f497be9083f1e0e744eb3f70672075897feadf4d34d488237701d57cb85c0bce2660d56395, 0x9b593317f497be9083f1e0e744eb3f70672075897feadf4d34d488237701d57cb85c0bce2660d56395, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q09
