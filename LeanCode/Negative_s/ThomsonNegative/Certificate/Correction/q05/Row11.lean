import ThomsonNegative.Certificate.Correction.q05.Input
import ThomsonNegative.Certificate.Correction.SourceData02

namespace ThomsonNegative.Certificate.Correction.q05
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
noncomputable def center11_0 : Nat := 0x18e5150a5332c95dfc1cbd95a13c715dd0841a675beaa72de66f416c9d21183ee7207e882fcafd7e0ba14901000
noncomputable def model11_0 : TM := ⟨0x4728a85299964aefe0e5ecad09e38aee8420d33adf55396f337a0b64e908c1f73903f4417e57ebf05d, 0x4728a85299964aefe0e5ecad09e38aee8420d33adf55396f337a0b64e908c1f73903f4417e57ebf05d, 0x4728a85299964aefe0e5ecad09e38aee8420d33adf55396f337a0b64e908c1f73903f4417e57ebf05d, 0x4, true⟩
noncomputable def center11_1 : Nat := 0xeff90ee08ca6927b575612795684247e27ccad8bb968f62736c5ccb4b8165989abdb3cf4d264dd75c814b01000
noncomputable def model11_1 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe77fc87704653493dabab093cab42123f13e656c5dcb47b139b62e65a5c0b2cc4d5ed9e7a69326ebae4, 0x18803788fb9acb6c25454f6c354bdedc0ec19a93a234b84ec649d19a5a3f4d33b2a12618596cd91451c, 0x18803788fb9acb6c25454f6c354bdedc0ec19a93a234b84ec649d19a5a3f4d33b2a12618596cd91451c, 0x4, true⟩
noncomputable def center11_2 : Nat := 0xf0fa2d7030a1b530fe60011dd53f16e95a8b4ee267f7dc143a3bc93c7cf1fb334da4edd5ef3091571614a01000
noncomputable def model11_2 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff787d16b81850da987f30008eea9f8b74ad45a77133fbee0a1d1de49e3e78fd99a6d276eaf79848ab8b, 0x8782e947e7af256780cfff711560748b52ba588ecc0411f5e2e21b61c1870266592d89150867b75475, 0x8782e947e7af256780cfff711560748b52ba588ecc0411f5e2e21b61c1870266592d89150867b75475, 0x4, true⟩
noncomputable def center11_3 : Nat := 0x195a0e8b919a7b463b221eba1f190216c386dbd4aa1a01ac9525a968580352cd28659ebd23094e679ee014d01000
noncomputable def model11_3 : TM := ⟨0x4ad0745c8cd3da31d910f5d0f8c810b61c36dea550d00d64a92d4b42c01a9669432cf5e9184a733cf70, 0x4ad0745c8cd3da31d910f5d0f8c810b61c36dea550d00d64a92d4b42c01a9669432cf5e9184a733cf70, 0x4ad0745c8cd3da31d910f5d0f8c810b61c36dea550d00d64a92d4b42c01a9669432cf5e9184a733cf70, 0x4, true⟩
noncomputable def center11_4 : Nat := 0x71f84a0f32a7a9664aed9a989a25f0bef795376dadfba175d420138e38079545460cff40c9c41d53e9814b01000
noncomputable def model11_4 : TM := ⟨0x18fc25079953d4b32576cd4c4d12f85f7bca9bb6d6fdd0baea1009c71c03caa2a3067fa064e20ea9f4c, 0x18fc25079953d4b32576cd4c4d12f85f7bca9bb6d6fdd0baea1009c71c03caa2a3067fa064e20ea9f4c, 0x18fc25079953d4b32576cd4c4d12f85f7bca9bb6d6fdd0baea1009c71c03caa2a3067fa064e20ea9f4c, 0x4, true⟩
noncomputable def center11_5 : Nat := 0x7a3ce705eab045aeabe88dbf37d8b602c5cf021dcacbcaf90ee81150b00c4c30f4c304875cad32fa79214d01000
noncomputable def model11_5 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd1e7382f55822d755f446df9bec5b0162e7810ee565e57c877408a8580626187a618243ae56997d3c9, 0x42e18c7d0aa7dd28aa0bb9206413a4fe9d187ef11a9a1a83788bf757a7f9d9e7859e7dbc51a96682c37, 0x42e18c7d0aa7dd28aa0bb9206413a4fe9d187ef11a9a1a83788bf757a7f9d9e7859e7dbc51a96682c37, 0x4, true⟩
noncomputable def center11_6 : Nat := 0x1e3a0e2ebb9251dde311ecd65ad157a5873515aef747ba4601fde4aa249dfd3e819f29ee29b6e4650a414b01000
noncomputable def model11_6 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef1d07175dc928eef188f66b2d68abd2c39a8ad77ba3dd2300fef255124efe9f40cf94f714db7232852, 0x10e2f8e8a236d7110e770994d297542d3c657528845c22dcff010daaedb10160bf306b08eb248dcd7ae, 0x10e2f8e8a236d7110e770994d297542d3c657528845c22dcff010daaedb10160bf306b08eb248dcd7ae, 0x4, true⟩
noncomputable def center11_7 : Nat := 0x3bff30650d345afbdcc757fbc9357a3da47931d926fcdcdf541fa9dedaf7e1f64af0b8d135d68f63c6c14a01000
noncomputable def model11_7 : TM := ⟨0xdff9832869a2d7dee63abfde49abd1ed23c98ec937e6e6faa0fd4ef6d7bf0fb25785c689aeb47b1e36, 0xdff9832869a2d7dee63abfde49abd1ed23c98ec937e6e6faa0fd4ef6d7bf0fb25785c689aeb47b1e36, 0xdff9832869a2d7dee63abfde49abd1ed23c98ec937e6e6faa0fd4ef6d7bf0fb25785c689aeb47b1e36, 0x4, true⟩
noncomputable def center11_8 : Nat := 0x4092101542424a68ad261fe120da4f9741ab3669d56b46c30fe642c14d77d2bc18c9c58e28f84f7f214501000
noncomputable def model11_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa049080aa121253456930ff0906d27cba0d59b34eab5a36187f32160a6bbe95e0c64e2c7147c27bf9, 0x5fb6f7f55ededacba96cf00f6f92d8345f2a64cb154a5c9e780cde9f594416a1f39b1d38eb83d8407, 0x5fb6f7f55ededacba96cf00f6f92d8345f2a64cb154a5c9e780cde9f594416a1f39b1d38eb83d8407, 0x4, true⟩
noncomputable def center11_9 : Nat := 0x35ddf0f830d2592ca734a5f042bbf45808ea9ac0398667d255c620975b614eff52afaa7eadd166ebe814a01000
noncomputable def model11_9 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1aeef87c18692c96539a52f8215dfa2c04754d601cc333e92ae3104badb0a77fa957d53f56e8b375f4, 0xe5110783e796d369ac65ad07dea205d3fb8ab29fe33ccc16d51cefb4524f588056a82ac0a9174c8a0c, 0xe5110783e796d369ac65ad07dea205d3fb8ab29fe33ccc16d51cefb4524f588056a82ac0a9174c8a0c, 0x4, true⟩
noncomputable def center11_10 : Nat := 0xc4108f29dcd2006667819bbab9a28378e5b9766b6b4888e278c4b769e8d52e434a7be0260f0d395f414401000
noncomputable def model11_10 : TM := ⟨0x22084794ee69003333c0cddd5cd141bc72dcbb35b5a444713c625bb4f46a9721a53df01307869cafa, 0x22084794ee69003333c0cddd5cd141bc72dcbb35b5a444713c625bb4f46a9721a53df01307869cafa, 0x22084794ee69003333c0cddd5cd141bc72dcbb35b5a444713c625bb4f46a9721a53df01307869cafa, 0x4, true⟩
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
end ThomsonNegative.Certificate.Correction.q05
