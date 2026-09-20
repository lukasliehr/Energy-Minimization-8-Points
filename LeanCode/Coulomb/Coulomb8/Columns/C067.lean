import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C067

def r0 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1248, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 252096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1720704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 7562976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -22460352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 45321792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -59544768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 43498368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -4929312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -17222400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 9276480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1207968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -174528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 7456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -96608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 744032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3808864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 13591904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -34340352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 60903616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -72727040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 51757024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -12333472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -9605152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 871072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -6048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 3168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -32544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 28704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -920800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 3368128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -9485888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 19323200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -26590912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 21895136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -7237536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -2495264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 316896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -25792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 276480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -242368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 6703744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -17796544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 31596928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -35295936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 20147072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 120192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -5831552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 208128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -800, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 162464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -1045056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 4127808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -10604032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 17888384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -2705216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 10412288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -41248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -329952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 28320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -247360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1139840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -3140160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 5251520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -4763328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 162176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 88128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -93600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 830208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2503808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 633472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -4244608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 1422336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 96960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 9472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -201792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 309760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -27456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -12544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 9408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 47104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -188672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 361600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -281728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 9888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -118688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 822624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -3699264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 11406016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -24705984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 5362880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -38519904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 23940768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -867936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -316512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 301056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 28608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -201344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 102336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -1531648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 289024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1691680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 192160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -283616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 376768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -219520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -13536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 160864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -1027584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 4024576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -10272576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 17315008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -18522624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 10741568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -163104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -267232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 60672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 293120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -107200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -831744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 335456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -422912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 6592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -65600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 337472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -994752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 245184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -223296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 49728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 65856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 42368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 46592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -2944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 152192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -536192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1023104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -1003904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 29824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 43904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -18816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 16736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -140800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 35712, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -1518336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 2199616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -1480704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 891904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -35424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -143104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 909056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -3048448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 5758976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -5719808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 309504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 75264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -4992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 50432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -199424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 360064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -242048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -11264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 17856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -93984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 330720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -773952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 1031040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 84288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -3852768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 1322976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1729728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 1368864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 63360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -8832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 61952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -99904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -16896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 74880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -92160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -144000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 489984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -624, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 126048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -860352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 3781488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -11230176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 22660896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -29772384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 21749184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -2464656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -8611200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 4638240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 603984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -87264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 3728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -48304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 372016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1904432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 6795952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -17170176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 30451808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -36363520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 25878512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -6166736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -4802576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 435536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -3024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 1584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -16272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 14352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -460400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 1684064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -4742944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 9661600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -13295456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 10947568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -3618768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1247632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 158448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -12896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 138240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -121184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 3351872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -8898272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 15798464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -17647968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 10073536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 60096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -2915776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 104064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -400, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 81232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -522528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 2063904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -5302016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 8944192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1352608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 5206144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -20624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -164976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 14160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -123680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 569920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -1570080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 2625760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -2381664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 81088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 44064, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -46800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -77888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 415104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -1251904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 316736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -2122304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 711168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 48480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -288, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 4736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -100896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 154880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -13728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -6272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 4704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 23552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -94336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 180800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -140864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 4944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -59344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 411312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -1849632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 5703008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -12352992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 2681440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -19259952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 11970384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -433968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -158256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 150528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 14304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -100672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 51168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -765824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 144512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -845840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 96080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -141808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 188384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -109760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -6768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 80432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -513792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 2012288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -5136288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 8657504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -9261312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 5370784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -81552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -133616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 30336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 146560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -53600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -415872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 167728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -211456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 3296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -32800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 168736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -497376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 122592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -111648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 24864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 32928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 21184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 23296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -1472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 76096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -268096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 511552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -501952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 14912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 21952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -9408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 8368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -70400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 17856, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -759168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 1099808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -740352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 445952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -17712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -71552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 454528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -1524224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 2879488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -2859904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 154752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 37632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -34624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -14272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 25216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -99712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 180032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -121024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -5632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 8928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -46992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 165360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -386976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 515520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 42144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -1926384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 661488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -864864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 684432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 31680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -4416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 30976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -49952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -8448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 37440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -46080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -72000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 244992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[0,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[0,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[0,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52],[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[0,r74,r75,r76,r77,r78,r79,r80,r81,r82],[0,r83,r84,r85,r86,r87,r88,r89,r90],[0,r91,r92,r93,r94,r95,r96,r97],[],[],[],[],[0,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123],[0,r53,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r134,r135,r54,r136,-1472,r137,r138,r139,r140,r141,14112],[0,r14,r142,r143,r144,r145,r146,r147,r148,r149],[r150,r151,r152,r153,r154,r155,r156,r157,-3136],[],[],[],[],[],[0,0,0,r41,r158,r159,r160,r161,r162,r163,r164,r165],[0,r166,r167,r168,r169,r170,r171,r172,-1920,r173,r174],[],[0,r83,r84,r85,r86,r87,r88,r89,r90],[],[],[],[],[],[0,0,r175,r176,r177,r178,r179,r180,r181,r182],[r28,r183,r184,r185,r186,r187,r188,r189,896],[0,r91,r190,r191,r192,r193,r194,r195],[r196,r197,r198,r199,r200,r201,-1152],[],[r14,r202,r203,r204,256],[],[],[],[],[],[],[],[],[],[],[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,-32928],[0,0,r150,r217,r218,r219,r220,r221,r222,r223,r224,3136],[r134,r135,r54,r136,-1472,r137,r138,r139,r140,r141,14112],[],[r150,r151,r152,r153,r154,r155,r156,r157,-3136],[],[],[],[],[],[],[],[],[],[],[],[],[],[r28,r183,r184,r185,r186,r187,r188,r189,896],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r14,r225,r226,r227,r228,-256],[],[],[],[],[],[],[],[],[r229,r230,r231,r232,r233,r234,-3456],[],[r14,r202,r203,r204,256],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r196,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247]),(⟨0,0,1⟩,[0,r28,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,0,2⟩,[0,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,0,3⟩,[0,r83,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,0,4⟩,[0,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,0,5⟩,[0,r296,r297,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨0,0,6⟩,[0,r113,r306,r307,r308,r309,r310,r311,r312,r313]),(⟨0,0,7⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,0,8⟩,[0,r150,r322,r323,r324,r325,r326,r327]),(⟨0,1,0⟩,[0,r28,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,1,1⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨0,1,2⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨0,1,3⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,1,4⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨0,1,5⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨0,1,6⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨0,2,0⟩,[0,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,2,1⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨0,2,2⟩,[0,0,0,r83,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,2,3⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨0,2,5⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,3,0⟩,[0,r83,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,3,1⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,3,2⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨0,3,3⟩,[0,0,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,3,4⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨0,3,5⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨0,3,6⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨0,3,8⟩,[r28,r430,r431,r432,128]),(⟨0,4,0⟩,[0,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,4,1⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨0,4,3⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨0,5,0⟩,[0,r296,r297,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨0,5,1⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨0,5,2⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,5,3⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨0,6,0⟩,[0,r113,r306,r307,r308,r309,r310,r311,r312,r313]),(⟨0,6,1⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨0,6,3⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨0,7,0⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,8,0⟩,[0,r150,r322,r323,r324,r325,r326,r327]),(⟨0,8,3⟩,[r28,r430,r431,r432,128]),(⟨1,0,0⟩,[0,r28,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨1,0,1⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨1,0,2⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨1,0,3⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨1,0,4⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨1,0,5⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨1,0,6⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨1,1,0⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨1,1,1⟩,[r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,-16464]),(⟨1,1,2⟩,[0,0,r111,r445,r446,r447,r448,r449,r450,r451,r452,1568]),(⟨1,1,3⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨1,1,5⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨1,2,0⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨1,2,1⟩,[0,0,r111,r445,r446,r447,r448,r449,r450,r451,r452,1568]),(⟨1,3,0⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨1,3,1⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨1,3,3⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨1,4,0⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨1,5,0⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨1,5,1⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨1,6,0⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨2,0,0⟩,[0,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨2,0,1⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨2,0,2⟩,[0,0,0,r83,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,0,3⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨2,0,5⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨2,1,0⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨2,1,1⟩,[0,0,r111,r445,r446,r447,r448,r449,r450,r451,r452,1568]),(⟨2,2,0⟩,[0,0,0,r83,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,3,0⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨2,3,3⟩,[0,0,r28,r453,r454,r166,r455,-128]),(⟨2,5,0⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨3,0,0⟩,[0,r83,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨3,0,1⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨3,0,2⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨3,0,3⟩,[0,0,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨3,0,4⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨3,0,5⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨3,0,6⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨3,0,8⟩,[r28,r430,r431,r432,128]),(⟨3,1,0⟩,[0,r285,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨3,1,1⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨3,1,3⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨3,2,0⟩,[0,r394,r395,r396,r397,r398,r399,r400,-960,r401,r402]),(⟨3,2,3⟩,[0,0,r28,r453,r454,r166,r455,-128]),(⟨3,3,0⟩,[0,0,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨3,3,1⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨3,3,2⟩,[0,0,r28,r453,r454,r166,r455,-128]),(⟨3,3,3⟩,[r456,r457,r458,r459,r460,r461,-1728]),(⟨3,3,5⟩,[r28,r430,r431,r432,128]),(⟨3,4,0⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨3,5,0⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨3,5,3⟩,[r28,r430,r431,r432,128]),(⟨3,6,0⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨3,8,0⟩,[r28,r430,r431,r432,128]),(⟨4,0,0⟩,[0,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨4,0,1⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨4,0,3⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨4,1,0⟩,[r364,r365,r286,r366,-736,r367,r368,r369,r370,r371,7056]),(⟨4,3,0⟩,[r261,r411,r412,r413,r414,r415,r416,r417,448]),(⟨5,0,0⟩,[0,r296,r297,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨5,0,1⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨5,0,2⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨5,0,3⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨5,1,0⟩,[0,r28,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨5,1,1⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨5,2,0⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨5,3,0⟩,[0,r150,r418,r419,r420,r421,r422,r423]),(⟨5,3,3⟩,[r28,r430,r431,r432,128]),(⟨6,0,0⟩,[0,r113,r306,r307,r308,r309,r310,r311,r312,r313]),(⟨6,0,1⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨6,0,3⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨6,1,0⟩,[r111,r380,r202,r381,r382,r383,r384,r385,-1568]),(⟨6,3,0⟩,[r424,r425,r426,r427,r428,r429,-576]),(⟨7,0,0⟩,[0,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨8,0,0⟩,[0,r150,r322,r323,r324,r325,r326,r327]),(⟨8,0,3⟩,[r28,r430,r431,r432,128]),(⟨8,3,0⟩,[r28,r430,r431,r432,128])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r462) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r463) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨5,0,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,0,3⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨5,1,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,3,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨5,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨6,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨7,0,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨8,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨8,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨8,3,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9])]

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨0,5,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,5,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,5,3⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,6,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,6,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,7,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,8,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,8,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,-512,14144,-169600,1187008,-5482112,17741632,-41366400,69865088,-83962240,67670720,-29880320,-1195328,8723456,-2850624]),(⟨1,0,1⟩,[0,-256,7872,-101120,734208,-3412416,10832512,-24263424,38630912,-42752640,30383808,-10160640,-2634240,3226944]),(⟨1,0,2⟩,[0,512,-12352,120384,-636864,2093056,-4556800,6654592,-6236928,3075072,279104,-1339072,460992]),(⟨1,0,3⟩,[0,128,-5376,72064,-472960,1828992,-4527744,7381376,-7873664,5146368,-1439872,-338688]),(⟨1,1,0⟩,[0,-256,7872,-101120,734208,-3412416,10832512,-24263424,38630912,-42752640,30383808,-10160640,-2634240,3226944]),(⟨1,1,1⟩,[64,-1344,11904,-62656,220480,-515968,687360,56192,-2568512,6173888,-8072064,6388032,-2612288]),(⟨1,2,0⟩,[0,512,-12352,120384,-636864,2093056,-4556800,6654592,-6236928,3075072,279104,-1339072,460992]),(⟨1,3,0⟩,[0,128,-5376,72064,-472960,1828992,-4527744,7381376,-7873664,5146368,-1439872,-338688]),(⟨1,3,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,5,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,6,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,-256,7872,-102144,758400,-3648704,12111104,-28572544,47978368,-55421696,39676480,-11675520,-4661248,4041408]),(⟨2,0,1⟩,[64,-1344,11904,-63168,234176,-660352,1493504,-2608256,2853568,-384832,-4249728,6613824,-3534272]),(⟨2,0,2⟩,[0,0,0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨2,0,3⟩,[0,0,0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨2,1,0⟩,[64,-1344,11904,-63168,234176,-660352,1493504,-2608256,2853568,-384832,-4249728,6613824,-3534272]),(⟨2,1,1⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨2,2,0⟩,[0,0,0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨2,3,0⟩,[0,0,0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨2,3,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,2048,-51200,536832,-3178112,12035072,-30675584,52849664,-58634112,35150848,-2100096,-9827584,3204096]),(⟨3,0,1⟩,[0,768,-21696,249664,-1582208,6220160,-16017408,27248640,-29171584,16336768,-843584,-3402560]),(⟨3,0,2⟩,[0,-1536,33472,-281856,1223936,-3140352,4870784,-4061952,829696,1317120,-592704]),(⟨3,0,3⟩,[0,-384,15232,-180352,985472,-3018112,5436032,-5363072,2148480,435456]),(⟨3,1,0⟩,[0,768,-21696,249664,-1582208,6220160,-16017408,27248640,-29171584,16336768,-843584,-3402560]),(⟨3,1,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨3,2,0⟩,[0,-1536,33472,-281856,1223936,-3140352,4870784,-4061952,829696,1317120,-592704]),(⟨3,3,0⟩,[0,-384,15232,-180352,985472,-3018112,5436032,-5363072,2148480,435456]),(⟨3,3,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,5,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨3,5,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨4,0,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,0,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,1,0⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,3,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨5,0,0⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨5,0,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,0,3⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,1,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,3,0⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨6,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,0,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨6,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,3,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨8,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨8,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨8,3,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9])]

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨0,0,6⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,0,7⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,0,8⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,1,0⟩,[0,-512,14144,-169600,1187008,-5482112,17741632,-41366400,69865088,-83962240,67670720,-29880320,-1195328,8723456,-2850624]),(⟨0,1,1⟩,[0,-256,7872,-101120,734208,-3412416,10832512,-24263424,38630912,-42752640,30383808,-10160640,-2634240,3226944]),(⟨0,1,2⟩,[0,512,-12352,120384,-636864,2093056,-4556800,6654592,-6236928,3075072,279104,-1339072,460992]),(⟨0,1,3⟩,[0,128,-5376,72064,-472960,1828992,-4527744,7381376,-7873664,5146368,-1439872,-338688]),(⟨0,1,5⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,1,6⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,2,0⟩,[0,-256,7872,-102144,758400,-3648704,12111104,-28572544,47978368,-55421696,39676480,-11675520,-4661248,4041408]),(⟨0,2,1⟩,[64,-1344,11904,-63168,234176,-660352,1493504,-2608256,2853568,-384832,-4249728,6613824,-3534272]),(⟨0,2,2⟩,[0,0,0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨0,2,3⟩,[0,0,0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨0,2,5⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,3,0⟩,[0,2048,-51200,536832,-3178112,12035072,-30675584,52849664,-58634112,35150848,-2100096,-9827584,3204096]),(⟨0,3,1⟩,[0,768,-21696,249664,-1582208,6220160,-16017408,27248640,-29171584,16336768,-843584,-3402560]),(⟨0,3,2⟩,[0,-1536,33472,-281856,1223936,-3140352,4870784,-4061952,829696,1317120,-592704]),(⟨0,3,3⟩,[0,-384,15232,-180352,985472,-3018112,5436032,-5363072,2148480,435456]),(⟨0,3,5⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,3,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨0,4,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨0,4,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,5,0⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨0,5,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,5,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,5,3⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨0,6,0⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨0,6,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,6,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,7,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,8,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,8,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,-512,14144,-169600,1187008,-5482112,17741632,-41366400,69865088,-83962240,67670720,-29880320,-1195328,8723456,-2850624]),(⟨1,0,1⟩,[0,-256,7872,-101120,734208,-3412416,10832512,-24263424,38630912,-42752640,30383808,-10160640,-2634240,3226944]),(⟨1,0,2⟩,[0,512,-12352,120384,-636864,2093056,-4556800,6654592,-6236928,3075072,279104,-1339072,460992]),(⟨1,0,3⟩,[0,128,-5376,72064,-472960,1828992,-4527744,7381376,-7873664,5146368,-1439872,-338688]),(⟨1,0,5⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,0,6⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,1,0⟩,[0,-512,15744,-202240,1468416,-6824832,21665024,-48526848,77261824,-85505280,60767616,-20321280,-5268480,6453888]),(⟨1,1,1⟩,[128,-2688,23808,-125312,440960,-1031936,1374720,112384,-5137024,12347776,-16144128,12776064,-5224576]),(⟨1,1,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,2,0⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨1,2,1⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,3,0⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨1,3,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,3,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,4,0⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,5,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,6,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,-256,7872,-102144,758400,-3648704,12111104,-28572544,47978368,-55421696,39676480,-11675520,-4661248,4041408]),(⟨2,0,1⟩,[64,-1344,11904,-63168,234176,-660352,1493504,-2608256,2853568,-384832,-4249728,6613824,-3534272]),(⟨2,0,2⟩,[0,0,0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨2,0,3⟩,[0,0,0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨2,0,5⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨2,1,0⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨2,1,1⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨2,2,0⟩,[0,0,0,2048,-41216,304384,-1072384,2046208,-2007808,417536,614656,-263424]),(⟨2,3,0⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨2,3,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,2048,-51200,536832,-3178112,12035072,-30675584,52849664,-58634112,35150848,-2100096,-9827584,3204096]),(⟨3,0,1⟩,[0,768,-21696,249664,-1582208,6220160,-16017408,27248640,-29171584,16336768,-843584,-3402560]),(⟨3,0,2⟩,[0,-1536,33472,-281856,1223936,-3140352,4870784,-4061952,829696,1317120,-592704]),(⟨3,0,3⟩,[0,-384,15232,-180352,985472,-3018112,5436032,-5363072,2148480,435456]),(⟨3,0,5⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨3,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨3,1,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨3,1,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,2,0⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨3,2,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[0,-768,30464,-360704,1970944,-6036224,10872064,-10726144,4296960,870912]),(⟨3,3,3⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨3,3,5⟩,[-512,6144,-15360,-18432,60928]),(⟨3,4,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,5,0⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨3,5,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,6,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨4,0,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,0,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,1,0⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,3,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨5,0,0⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨5,0,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,0,3⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,1,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,3,0⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨6,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,0,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨6,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,3,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨8,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨8,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨8,3,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,1536,-42432,504192,-3441408,15125952,-44920704,90643584,-119089536,86996736,-9858624,-34444800,18552960,2415936,-2443392]),(⟨0,0,1⟩,[0,-512,14912,-193216,1488064,-7617728,27183808,-68680704,121807232,-145454080,103514048,-24666944,-19210304,12195008,-84672]),(⟨0,0,2⟩,[0,-256,6336,-65088,401856,-1841600,6736256,-18971776,38646400,-53181824,43790272,-14475072,-4990528,4436544]),(⟨0,0,3⟩,[0,2048,-51584,552960,-3393152,13407488,-35593088,63193856,-70591872,40294144,240384,-11663104,2913792]),(⟨0,0,4⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨0,0,5⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨0,0,6⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨0,0,7⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,0,8⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,1,0⟩,[0,-512,14912,-193216,1488064,-7617728,27183808,-68680704,121807232,-145454080,103514048,-24666944,-19210304,12195008,-84672]),(⟨0,1,1⟩,[0,-704,19776,-237376,1645248,-7398528,22812032,-49411968,75080320,-77039808,47881536,-12151104,-4431168,4214784]),(⟨0,1,2⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨0,1,3⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨0,1,4⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨0,1,5⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,1,6⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,2,0⟩,[0,-256,6336,-65088,401856,-1841600,6736256,-18971776,38646400,-53181824,43790272,-14475072,-4990528,4436544]),(⟨0,2,1⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨0,2,2⟩,[0,0,0,2048,-41216,304384,-1072384,2046208,-2007808,417536,614656,-263424]),(⟨0,2,3⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨0,2,5⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,3,0⟩,[0,2048,-51584,552960,-3393152,13407488,-35593088,63193856,-70591872,40294144,240384,-11663104,2913792]),(⟨0,3,1⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨0,3,2⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨0,3,3⟩,[0,0,17408,-286208,1818112,-6096896,11517952,-11439616,4333056,1053696]),(⟨0,3,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,3,5⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨0,3,6⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,3,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨0,4,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨0,4,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,5,0⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨0,5,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,5,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,5,3⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨0,6,0⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨0,6,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,6,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,7,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,8,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,8,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,-512,14912,-193216,1488064,-7617728,27183808,-68680704,121807232,-145454080,103514048,-24666944,-19210304,12195008,-84672]),(⟨1,0,1⟩,[0,-704,19776,-237376,1645248,-7398528,22812032,-49411968,75080320,-77039808,47881536,-12151104,-4431168,4214784]),(⟨1,0,2⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨1,0,3⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨1,0,4⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,0,5⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,0,6⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,1,0⟩,[0,-704,19776,-237376,1645248,-7398528,22812032,-49411968,75080320,-77039808,47881536,-12151104,-4431168,4214784]),(⟨1,1,1⟩,[192,-4032,35712,-187968,661440,-1547904,2062080,168576,-7705536,18521664,-24216192,19164096,-7836864]),(⟨1,1,2⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,1,3⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,1,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,2,0⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨1,2,1⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,3,0⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨1,3,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,3,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,4,0⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨1,5,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,6,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,-256,6336,-65088,401856,-1841600,6736256,-18971776,38646400,-53181824,43790272,-14475072,-4990528,4436544]),(⟨2,0,1⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨2,0,2⟩,[0,0,0,2048,-41216,304384,-1072384,2046208,-2007808,417536,614656,-263424]),(⟨2,0,3⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨2,0,5⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨2,1,0⟩,[64,-832,-448,57216,-402688,1432704,-3063296,4046336,-3383360,2690240,-3970624,5274752,-3073280]),(⟨2,1,1⟩,[0,0,128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨2,2,0⟩,[0,0,0,2048,-41216,304384,-1072384,2046208,-2007808,417536,614656,-263424]),(⟨2,3,0⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨2,3,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,2048,-51584,552960,-3393152,13407488,-35593088,63193856,-70591872,40294144,240384,-11663104,2913792]),(⟨3,0,1⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨3,0,2⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨3,0,3⟩,[0,0,17408,-286208,1818112,-6096896,11517952,-11439616,4333056,1053696]),(⟨3,0,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,0,5⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨3,0,6⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[0,896,-27072,321728,-2055168,8049152,-20545152,34630016,-37045248,21483136,-2283456,-3741248]),(⟨3,1,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨3,1,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,2,0⟩,[0,-1536,33472,-281600,1214208,-3036672,4399232,-2961408,-456960,1783808,-495936]),(⟨3,2,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[0,0,17408,-286208,1818112,-6096896,11517952,-11439616,4333056,1053696]),(⟨3,3,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,3,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,3⟩,[2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨3,3,5⟩,[-512,6144,-15360,-18432,60928]),(⟨3,4,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,5,0⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨3,5,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,6,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,896,-27200,324928,-2090112,8255616,-21208064,35776768,-37873024,20824576,-577472,-4619328]),(⟨4,0,1⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,0,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,1,0⟩,[-192,3584,-27200,121344,-350336,586240,-214400,-1663488,4696384,-5920768,3358656]),(⟨4,3,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨5,0,0⟩,[0,-2560,56640,-494720,2279680,-6280320,10503040,-9526656,2270464,2996352,-1310400]),(⟨5,0,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,0,3⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,1,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨5,3,0⟩,[0,256,-9984,100864,-398848,720128,-484096,-157696]),(⟨5,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[0,-896,28416,-311552,1660416,-5007616,8868608,-8489216,2844672,1357440]),(⟨6,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,0,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨6,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,3,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨8,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨8,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨8,3,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked0 :
    (Poly.add (Poly.add (Poly.mul chunk0 sourceRight) partial4)
      (Poly.scale (K.ofRat (-1)) partial0)).isZero := by decide +kernel

theorem partial_sound0 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 0)
      sourceRight).eval u v t=partial0.eval u v t := by
  change (Poly.mul (chunk0++(sourceLeft.drop 4))
    sourceRight).eval u v t=partial0.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound4 partial_checked0 u v t


theorem weighted_checked :
    (Poly.add (Poly.scale (K.ofRat r464) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 9).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r462*r463 : ℚ)=r464 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 9 r462 r463 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=9 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 9).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C067

#print axioms Coulomb8.Columns.C067.sound
