import ThomsonNegative.Structure.Packed.IdentityKernel

namespace ThomsonNegative.Certificate.Correction.Source
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

noncomputable def r52n53 : Nat := 0x80e3c08b48000896073c8000005c0c180000000f2d800000000003404000
noncomputable def r52n55 : Nat := 0x80aad0687600021c215b580000065091200000003588800000000003604000
noncomputable def r52n65 : Nat := 0x1ff126efde312ba43f348d9d41e4f8008602221840a00000c22b5f11c0000002d2f1af400000000178918000000000003f06000
noncomputable def r52n67 : Nat := 0x803b6440873b5178196e4c57c3610079fddde7bf600009eea507720000004b4394300000000d0edd000000000003c06000
noncomputable def r52d : Nat := 0x80aad0687600010e10adac00000194244800000006b11000000000003704000
noncomputable def r52n : Nat → Nat
  | 53 => r52n53
  | 55 => r52n55
  | 65 => r52n65
  | 67 => r52n67
  | _ => 0x100000
theorem r52_headers : recordOk 6 63 r52d && allBelow 68 (fun j => recordOk 6 63 (r52n j)) = true := by decide +kernel
noncomputable def r53n57 : Nat := 0x80e3c08b4800112c0e79000001703060000000796c00000000003304000
noncomputable def r53n65 : Nat := 0x201095d664bb3b5103a038988a99800792417c85080000513ec4eec00000011d9ef9000000001adb38000000000003d06000
noncomputable def r53n67 : Nat := 0x7fbda8a66d1312df8bf8eceeacd0086dbe837af800017609d88a000000b89841c00000000a499000000000003a06000
noncomputable def r53d : Nat := 0x80e3c08b48000896073c8000005c0c180000000f2d800000000003404000
noncomputable def r53n : Nat → Nat
  | 57 => r53n57
  | 65 => r53n65
  | 67 => r53n67
  | _ => 0x100000
theorem r53_headers : recordOk 6 61 r53d && allBelow 68 (fun j => recordOk 6 61 (r53n j)) = true := by decide +kernel
noncomputable def r54n60 : Nat := 0x8097d5b2300010c809a6000001a02040000000664800000000003304000
noncomputable def r54n65 : Nat := 0x7fc6ecc7d1ffe287e7c2dbcc6d180085b98ab871000006246c2ab0000000b37324800000000310b8000000000003c06000
noncomputable def r54n67 : Nat := 0x200e44ce0b800770307a486725d007a4675478f00004edc9eaa800000132336e000000019de9000000000003906000
noncomputable def r54d : Nat := 0x8097d5b23000086404d30000006808100000000cc9000000000003404000
noncomputable def r54n : Nat → Nat
  | 60 => r54n60
  | 65 => r54n65
  | 67 => r54n67
  | _ => 0x100000
theorem r54_headers : recordOk 6 60 r54d && allBelow 68 (fun j => recordOk 6 60 (r54n j)) = true := by decide +kernel
noncomputable def r55n52 : Nat := 0x80e3c08b48000896073c8000005c0c180000000f2d800000000003404000
noncomputable def r55n56 : Nat := 0x80aad0687600021c215b580000065091200000003588800000000003604000
noncomputable def r55n65 : Nat := 0x803554e806d1b5a2059c36c9ec7d8007ab3b01f2e4000026f27bc4300000004f1f6a20000000032c078000000000003e06000
noncomputable def r55n67 : Nat := 0x1ff2aac5fe4b929bf4c7926c270500854c4fe0d1c0000c86c21de8000002c38257800000001a7f1000000000003b06000
noncomputable def r55d : Nat := 0x80aad0687600021c215b580000065091200000003588800000000003604000
noncomputable def r55n : Nat → Nat
  | 52 => r55n52
  | 56 => r55n56
  | 65 => r55n65
  | 67 => r55n67
  | _ => 0x100000
theorem r55_headers : recordOk 6 62 r55d && allBelow 68 (fun j => recordOk 6 62 (r55n j)) = true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Source
