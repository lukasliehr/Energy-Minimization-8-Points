import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C126

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1130496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 2441216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -21495808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 867434496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -3487186944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 10033381376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -2757361664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1328971776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 16639574016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -616520007680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1869203505152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -3893270216704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 5654827843584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -5492678672384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 3211483152384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -3137667072, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 13400801280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -770048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 14368768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -147357696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 954908672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -4245766144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 13640515584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -31373262848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 37603426304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 83998392320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -678111166464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 2266197229568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -4853403533312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 6956684886016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -373732261888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 451290529792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -10564730880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1982464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -24461312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 159285248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -82771968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 997048320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 1093713920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -14039515136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 57288622080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -149593931776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 230054969344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -8004599808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -629078556672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 1527005724672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1641125494784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 99757129728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 1523712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -25739264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 222363648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -1133084672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 3689955328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -7672807424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 4877713408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 43903778816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -240945741824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 41017655296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -184524931072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 1503775129600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -926752129024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 21890023424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -753664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 4947968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 7077888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -241696768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 1355513856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -602079232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 7995392000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 6586368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1318617088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 34583773184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -490135093248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 81926619136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -6179225600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 11173888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -74809344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 250724352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -408354816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -147128320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 4405657600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -19307970560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 47272067072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -74366943232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 63084199936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -1310736384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 2621440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -24739840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 113246208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -288030720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 295698432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 89718784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -9640607744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 26270793728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -41631088640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 4605050880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 6094848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -78741504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 577077248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -2814148608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 10425040896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -31671123968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 72080097280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -67716513792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -275384369152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 1482135207936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -3603032735744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 5192553037824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -609766178816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 31612207104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 737280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -12140544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 101744640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -499597312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 1537589248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -2622439424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -2532638720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 38123028480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -146786041856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 323054092288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -8256716800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 166098649088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 35690233856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -5938200576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -6520832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 72581120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -434274304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 1685258240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -4882366464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 9349300224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 220004352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -82006147072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 297043656704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -586806624256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 92758376448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -6399721472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 4980736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -32014336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 158334976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -968949760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 4344774656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -10074521600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 6997147648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 24858951680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -11116740608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 85295104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 19660800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -99942400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 231931904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -64290816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -1291321344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 6277169152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -18672058368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 305004544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -51864928256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 57035128832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -7280590848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 822018048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -9732096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 275316736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -102367232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 7131824128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -19574210560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 34822979584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -46424129536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 40130412544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -669007872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 3604480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -120061952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 387448832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -1041235968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 2032009216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -569901056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -8331067392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 2621702144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -15138816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 8290304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -37486592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 83427328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -124649472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 229179392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 113508352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -1874427904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 364183552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -491520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 90701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -220332032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 21495808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 232521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -2347237376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 22740992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -13631488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 198836224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -1491075072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 7114457088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -20421017600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 732233728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -46558347264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 5607063552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 1212416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -6029312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 123535360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -252051456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 3866624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 1099694080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -61702144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 123535360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 2850816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -8552448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 47579136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -124747776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 67141632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -12075466752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 62221713408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -169214410752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 28887711744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 190479826944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -160286244864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 35139256320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -1203535872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 294912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -26443776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 174686208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -604209152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 778305536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 1808596992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -9751560192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 18025021440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -1352892416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -23860445184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 63288606720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -14539587584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 104660992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -2326528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 118259712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -63045632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 11993088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 1393491968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -6508445696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 7705165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 7478411264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -28053504000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 1577156608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 22216704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 16187392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -62062592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 5242880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -108658688, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 1715863552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 2440888320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -9668788224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 1446313984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 12091392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -8388608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 3735552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 487587840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1997733888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 2501902336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 2267447296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -1625292800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 13271040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -31981568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 226557952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -818610176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 858652672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 4724883456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -21706440704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 35559374848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 962527232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -15117844480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 3626827776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -126156800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 9895936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -38404096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 1341915136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -2772566016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 1481637888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 6882131968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -19259588608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 2414673920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -1310720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 12288000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -63438848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 6094848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 360185856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -2037448704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 3488088064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 1118470144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -1865940992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 16613376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -254803968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -79429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 1972371456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -2297954304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -28311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -10223616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 14548992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -28311552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 991690752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 20447232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -971243520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 15033434112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -539885568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -41680896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 16580608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -74973184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 166854656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -249298944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 458358784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 227016704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -3748855808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 728367104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -983040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 181403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -440664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 42991616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 465043456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -4694474752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 45481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -565248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 1220608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -10747904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 433717248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -1743593472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 5016690688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -1378680832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 664485888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 8319787008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -308260003840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 934601752576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -1946635108352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 2827413921792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -2746339336192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 1605741576192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1568833536, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 6700400640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -385024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 7184384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -73678848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 477454336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -2122883072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 6820257792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -15686631424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 18801713152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 41999196160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -339055583232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1133098614784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -2426701766656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 3478342443008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -186866130944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 225645264896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -5282365440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 991232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -12230656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 79642624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -41385984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 498524160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 546856960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -7019757568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 28644311040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -74796965888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 115027484672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -4002299904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -314539278336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 763502862336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -820562747392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 49878564864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 761856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -12869632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 111181824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -566542336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 1844977664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -3836403712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 2438856704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 21951889408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -120472870912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 20508827648, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -92262465536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 751887564800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -463376064512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 10945011712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 2473984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 3538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -120848384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 677756928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -301039616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 3997696000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 3293184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -659308544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 17291886592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -245067546624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 40963309568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -3089612800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 5586944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -37404672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 125362176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -204177408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -73564160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 2202828800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -9653985280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 23636033536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -37183471616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 31542099968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -655368192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -12369920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 56623104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -144015360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 147849216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 44859392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -4820303872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 13135396864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -20815544320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 2302525440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 3047424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -39370752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 288538624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -1407074304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 5212520448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -15835561984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 36040048640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -33858256896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -137692184576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 741067603968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -1801516367872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 2596276518912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -304883089408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 15806103552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 368640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -6070272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 50872320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -249798656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 768794624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -1311219712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -1266319360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 19061514240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -73393020928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 161527046144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -4128358400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 83049324544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 17845116928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -2969100288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -3260416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 36290560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -217137152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 842629120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -2441183232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 4674650112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 110002176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -41003073536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 148521828352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -293403312128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 46379188224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -3199860736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -16007168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 79167488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -484474880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 2172387328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -5037260800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 3498573824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 12429475840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -5558370304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 42647552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 9830400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -49971200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 115965952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -32145408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -645660672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 3138584576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -9336029184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 152502272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -25932464128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 28517564416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -3640295424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 411009024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -4866048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 1073152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 137658368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -51183616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 3565912064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -9787105280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 17411489792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -23212064768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 20065206272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -334503936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 1802240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -60030976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 193724416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -520617984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 1016004608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -284950528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -4165533696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 1310851072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -7569408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 4145152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -18743296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 41713664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -62324736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 114589696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 56754176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -937213952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 182091776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -245760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -12713984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 45350912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -110166016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 10747904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 116260864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -1173618688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 11370496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 99418112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -745537536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 3557228544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -10210508800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 366116864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -23279173632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 2803531776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 606208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -3014656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 61767680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -126025728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 1933312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 549847040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -30851072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 61767680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 1425408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 245760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -4276224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 23789568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -62373888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 33570816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -6037733376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 31110856704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -84607205376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 14443855872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 95239913472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -80143122432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 17569628160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -601767936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 147456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -13221888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 87343104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -302104576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 389152768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 904298496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -4875780096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 9012510720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := -676446208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -11930222592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 31644303360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -7269793792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 52330496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -1163264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 59129856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -31522816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 5996544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 696745984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -3254222848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 3852582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 3739205632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -14026752000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 788578304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 11108352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 8093696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -31031296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 2621440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -54329344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 857931776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 1220444160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -4834394112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := 723156992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := 6045696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -4194304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 1867776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := 243793920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := -998866944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 1250951168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 1133723648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := -812646400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 6635520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := -15990784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 113278976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -409305088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := 429326336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 2362441728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -10853220352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 17779687424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := 481263616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -7558922240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 1813413888, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -63078400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -19202048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := 670957568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -1386283008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := 740818944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 3441065984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -9629794304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 1207336960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := -655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 6144000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -31719424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 3047424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 180092928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := -1018724352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 1744044032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 559235072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -932970496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 8306688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 2359296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -127401984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -39714816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := 986185728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -1148977152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -14155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := -5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := 7274496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -14155776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 495845376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 10223616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -485621760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := 7516717056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := -269942784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := -20840448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65],[r0,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78],[r18,r66,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89],[0,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100],[],[],[],[],[],[],[0,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130],[0,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143],[0,0,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154],[],[],[],[],[],[],[],[r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168],[r116,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180],[0,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191],[r0,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201],[0,r101,r202,r203,r204,r205,r206,r207,r208,r209],[],[],[],[],[0,r155,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219],[r0,r192,r220,r221,r222,r223,r224,r225,r226,r227,r228],[0,r101,r202,r203,r204,r205,r206,r207,r208,r209],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241],[r35,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254],[r51,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266],[r155,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277],[r0,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287],[],[],[],[],[],[r35,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299],[r155,r300,r301,r182,r302,r303,r304,r305,r306,r307,r308,r309],[r0,r278,r310,r311,r312,r313,r314,r315,r316,r317,r318],[],[],[],[],[],[0,0,r319,r320,r321,r322,r323,r324,r325,r326,393216],[],[r155,r327,r328,r329,r330,r331,r332,r333,65536],[],[],[],[r181,r334,r335,r336,r337,r338,r339,r340,131072],[],[],[],[],[],[0,r319,r341,r342,r343,r344,r345,r346,r347,r348,r349,2752512],[r155,r267,r350,r351,r352,r353,r354,r355,r356,r357,r358],[],[],[],[],[],[0,r359,r360,r361,r362,r363,r364,r365,r366,r367],[r155,r327,r328,r329,r330,r331,r332,r333,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r18,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,0,1⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨0,0,2⟩,[r51,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,0,3⟩,[r116,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨0,0,4⟩,[r18,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,0,5⟩,[r385,r431,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨0,0,6⟩,[0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465]),(⟨0,1,0⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨0,1,1⟩,[0,r90,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479]),(⟨0,1,2⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨0,1,3⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,1,4⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,2,0⟩,[r51,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,2,1⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨0,2,2⟩,[r0,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨0,2,3⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨0,2,4⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨0,2,5⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨0,2,6⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨0,3,0⟩,[r116,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨0,3,1⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,3,2⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨0,3,3⟩,[0,r0,r571,r229,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨0,3,4⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨0,3,5⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨0,4,0⟩,[r18,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,4,1⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,4,2⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨0,4,3⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨0,5,0⟩,[r385,r431,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨0,5,2⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨0,5,3⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨0,6,0⟩,[0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465]),(⟨0,6,2⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨1,0,0⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨1,0,1⟩,[0,r90,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479]),(⟨1,0,2⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨1,0,3⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,0,4⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,1,0⟩,[0,r90,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479]),(⟨1,1,1⟩,[0,0,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨1,1,2⟩,[r51,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611,r612,r613,r614]),(⟨1,1,3⟩,[r116,r615,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626]),(⟨1,1,4⟩,[r0,r192,r627,r628,r629,r630,r631,r632,r633,r634,r635,r636]),(⟨1,1,5⟩,[r18,r210,r637,r638,r639,r640,r641,r642,r643,r644,r645]),(⟨1,2,0⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨1,2,1⟩,[r51,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611,r612,r613,r614]),(⟨1,2,2⟩,[r51,r255,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656]),(⟨1,2,3⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨1,2,4⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨1,3,0⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,3,1⟩,[r116,r615,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626]),(⟨1,3,2⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨1,3,3⟩,[0,0,r675,r676,r677,r678,r679,r680,r681,r682,196608]),(⟨1,3,5⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨1,4,0⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,4,1⟩,[r0,r192,r627,r628,r629,r630,r631,r632,r633,r634,r635,r636]),(⟨1,4,2⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨1,4,4⟩,[r155,r327,r328,r329,r330,r331,r332,r333,65536]),(⟨1,5,1⟩,[r18,r210,r637,r638,r639,r640,r641,r642,r643,r644,r645]),(⟨1,5,3⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨2,0,0⟩,[r51,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨2,0,1⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨2,0,2⟩,[r0,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨2,0,3⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,0,4⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨2,0,5⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨2,0,6⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨2,1,0⟩,[r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨2,1,1⟩,[r51,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611,r612,r613,r614]),(⟨2,1,2⟩,[r51,r255,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656]),(⟨2,1,3⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨2,1,4⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨2,2,0⟩,[r0,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨2,2,1⟩,[r51,r255,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656]),(⟨2,2,2⟩,[0,r675,r690,r691,r692,r693,r694,r695,r696,r697,r698,1376256]),(⟨2,2,3⟩,[r0,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨2,3,0⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,3,1⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨2,3,2⟩,[r0,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨2,3,3⟩,[0,r101,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨2,3,4⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨2,4,0⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨2,4,1⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨2,4,3⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨2,5,0⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨2,6,0⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨3,0,0⟩,[r116,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨3,0,1⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,0,2⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨3,0,3⟩,[0,r0,r571,r229,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨3,0,4⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨3,0,5⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨3,1,0⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,1,1⟩,[r116,r615,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626]),(⟨3,1,2⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨3,1,3⟩,[0,0,r675,r676,r677,r678,r679,r680,r681,r682,196608]),(⟨3,1,5⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨3,2,0⟩,[r480,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨3,2,1⟩,[r0,r657,r67,r300,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨3,2,2⟩,[r0,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨3,2,3⟩,[0,r101,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨3,2,4⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨3,3,0⟩,[0,r0,r571,r229,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨3,3,1⟩,[0,0,r675,r676,r677,r678,r679,r680,r681,r682,196608]),(⟨3,3,2⟩,[0,r101,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨3,4,0⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨3,4,2⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨3,5,0⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨3,5,1⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨4,0,0⟩,[r18,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨4,0,1⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨4,0,2⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨4,0,3⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨4,1,0⟩,[0,0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨4,1,1⟩,[r0,r192,r627,r628,r629,r630,r631,r632,r633,r634,r635,r636]),(⟨4,1,2⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨4,1,4⟩,[r155,r327,r328,r329,r330,r331,r332,r333,65536]),(⟨4,2,0⟩,[0,r155,r300,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨4,2,1⟩,[r18,r210,r666,r667,r668,r669,r670,r671,r672,r673,r674]),(⟨4,2,3⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨4,3,0⟩,[r18,r553,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨4,3,2⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨4,4,1⟩,[r155,r327,r328,r329,r330,r331,r332,r333,65536]),(⟨5,0,0⟩,[r385,r431,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨5,0,2⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨5,0,3⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨5,1,1⟩,[r18,r210,r637,r638,r639,r640,r641,r642,r643,r644,r645]),(⟨5,1,3⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨5,2,0⟩,[r18,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨5,3,0⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨5,3,1⟩,[r0,r683,r684,r685,r686,r687,r688,r689,32768]),(⟨6,0,0⟩,[0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465]),(⟨6,0,2⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨6,2,0⟩,[0,r90,r563,r564,r565,r566,r567,r568,r569,r570])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r699) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r699) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[-8192,294912,-4243456,32423936,-146726912,412827648,-670728192,-255754240,7559847936,-35882729472,103694417920,-196363173888,234067648512,-148056883200,26754416640]),(⟨3,0,1⟩,[0,32768,-983040,11190272,-66256896,236929024,-557711360,597524480,2778333184,-19745144832,63465914368,-123102838784,141155696640,-75107450880]),(⟨3,0,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,0,3⟩,[0,16384,-131072,245760,-3407872,49709056,-372768768,1778614272,-5105254400,8969863168,-11639586816,9812361216]),(⟨3,0,4⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨3,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[0,32768,-983040,11190272,-66256896,236929024,-557711360,597524480,2778333184,-19745144832,63465914368,-123102838784,141155696640,-75107450880]),(⟨3,1,1⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨3,1,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨3,1,3⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨3,2,0⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,2,1⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨3,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,2,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,3,0⟩,[0,16384,-131072,245760,-3407872,49709056,-372768768,1778614272,-5105254400,8969863168,-11639586816,9812361216]),(⟨3,3,1⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨3,3,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨3,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,0,0⟩,[0,32768,-983040,11190272,-66256896,236929024,-557711360,597524480,2778333184,-19745144832,63465914368,-123102838784,141155696640,-75107450880]),(⟨4,0,1⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨4,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,0,3⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,1,0⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨4,1,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,2,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[8192,-278528,3555328,-21512192,62676992,-62423040,-168460288,1178435584,-4434632704,11100536832,-18484019200,16217456640,-2438553600]),(⟨5,0,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨6,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial12 : Poly := [(⟨1,1,0⟩,[0,-32768,983040,-12582912,92536832,-452362240,1636368384,-4700504064,10698096640,-16870375424,7166558208,50977308672,-165983027200,245999370240,-169660710912,31444697088]),(⟨1,1,1⟩,[0,0,131072,-3145728,31916032,-190709760,804192256,-2656567296,6826622976,-11922571264,7032799232,31024742400,-107631935488,153684672512,-88274436096]),(⟨1,1,2⟩,[0,32768,-917504,10223616,-60030976,216432640,-553910272,1062469632,-1217396736,-497188864,7092699136,-18629001216,18663866368,-2866053120]),(⟨1,1,3⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨1,2,0⟩,[0,0,131072,-3145728,31916032,-190709760,804192256,-2656567296,6826622976,-11922571264,7032799232,31024742400,-107631935488,153684672512,-88274436096]),(⟨1,2,1⟩,[0,0,0,196608,-5111808,50921472,-240648192,495845376,173801472,-3399352320,7516717056,-1889599488,-17360093184,19489161216]),(⟨1,3,0⟩,[0,32768,-917504,10223616,-60030976,216432640,-553910272,1062469632,-1217396736,-497188864,7092699136,-18629001216,18663866368,-2866053120]),(⟨1,4,0⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨2,0,0⟩,[-16384,491520,-6094848,40943616,-165494784,424230912,-623214592,-593395712,9059123200,-38916587520,103172538368,-183728488448,216410505216,-147716358144,40571928576,-3567255552]),(⟨2,0,1⟩,[0,65536,-1572864,15171584,-78774272,256081920,-564232192,432996352,3812229120,-22025601024,63192891392,-114101747712,129770979328,-77299482624,10014326784]),(⟨2,0,2⟩,[16384,-458752,4915200,-25083904,60538880,-41533440,-202506240,1321369600,-4754915328,10773561344,-16724590592,15203581952,-4060987392,325140480]),(⟨2,0,3⟩,[-16384,360448,-3227648,16646144,-61603840,200081408,-701661184,2387476480,-5352472576,6310952960,-4728045568,3847749632,97026048]),(⟨2,0,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[0,65536,-1441792,12025856,-46858240,65372160,239960064,-2223570944,10638852096,-33948172288,70225690624,-83077005312,22139043840,76385189888,-78260109312]),(⟨2,1,1⟩,[0,0,98304,-2359296,19169280,-42172416,-223150080,1431699456,-2596995072,-825556992,11178049536,-16392781824,-2173796352,17278205952]),(⟨2,1,3⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,1,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,2,0⟩,[16384,-458752,4915200,-24887296,55427072,9388032,-443154432,1817214976,-4581113856,7374209024,-9207873536,13313982464,-21421080576,19814301696]),(⟨2,2,2⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,2,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,3,0⟩,[-16384,360448,-3227648,16646144,-61603840,200081408,-701661184,2387476480,-5352472576,6310952960,-4728045568,3847749632,97026048]),(⟨2,3,1⟩,[0,131072,-3145728,29589504,-140247040,359006208,-462684160,-117112832,2220621824,-4795400192,3389259776,191070208]),(⟨2,3,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,4,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,4,1⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,0,0⟩,[-8192,360448,-5816320,47595520,-225501184,668909568,-1234960384,177242112,11372077056,-57908330496,166887309312,-310464921600,363838627840,-225356365824,36768743424]),(⟨3,0,1⟩,[0,32768,-884736,8634368,-41975808,143835136,-540213248,1533378560,7536640,-17171349504,67127246848,-137606021120,156341993472,-77318406144]),(⟨3,0,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,0,3⟩,[0,81920,-1572864,12861440,-63438848,243433472,-893386752,2794618880,-5390204928,4804329472,-2463629312,3507044352]),(⟨3,0,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[0,65536,-1802240,18857984,-102006784,360267776,-1094123520,2595848192,-1209860096,-17668538368,74219945984,-156235022336,175005859840,-80184459264]),(⟨3,1,1⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨3,1,2⟩,[32768,-786432,6651904,-18415616,-54198272,505675776,-1444216832,1873936384,935493632,-8999927808,14238056448,-7042301952]),(⟨3,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,2,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,2,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,81920,-1572864,12861440,-63438848,243433472,-893386752,2794618880,-5390204928,4804329472,-2463629312,3507044352]),(⟨3,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,3,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[16384,-425984,3932160,-13893632,-5718016,195395584,-760217600,1918894080,-1976582144,-8971583488,46741323776,-107899256832,137094709248,-74782310400]),(⟨4,0,1⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨4,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,0,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,1,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,1,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,1,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,2,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨5,0,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨6,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-8192,294912,-4243456,32423936,-146726912,412827648,-670728192,-255754240,7559847936,-35882729472,103694417920,-196363173888,234067648512,-148056883200,26754416640]),(⟨0,3,1⟩,[0,32768,-983040,11190272,-66256896,236929024,-557711360,597524480,2778333184,-19745144832,63465914368,-123102838784,141155696640,-75107450880]),(⟨0,3,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨0,3,3⟩,[0,16384,-131072,245760,-3407872,49709056,-372768768,1778614272,-5105254400,8969863168,-11639586816,9812361216]),(⟨0,3,4⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,3,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[0,32768,-983040,11190272,-66256896,236929024,-557711360,597524480,2778333184,-19745144832,63465914368,-123102838784,141155696640,-75107450880]),(⟨0,4,1⟩,[0,0,49152,-1572864,18137088,-88080384,95256576,731381760,-2996600832,3752853504,3401170944,-17065574400,16582164480]),(⟨0,4,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,4,3⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,5,0⟩,[8192,-278528,3555328,-21512192,62676992,-62423040,-168460288,1178435584,-4434632704,11100536832,-18484019200,16217456640,-2438553600]),(⟨0,5,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,6,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨0,6,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[8192,-319488,5316608,-50479104,308649984,-1303633920,3973455872,-8638152704,9659768832,22820773888,-175091589120,576609402880,-1226753056768,1751567785984,-1593712680960,787903463424,-127166054400]),(⟨1,0,1⟩,[0,-65536,2064384,-27475968,209141760,-1048641536,3808641024,-10513989632,20486062080,-13565624320,-84242464768,396041994240,-927173165056,1318304415744,-1076893368320,388436901888]),(⟨1,0,2⟩,[-8192,303104,-4448256,33980416,-147038208,342794240,-133029888,-2343305216,11705622528,-35087589376,71664623616,-88909709312,32647028736,68929380352,-76683780096]),(⟨1,0,3⟩,[0,81920,-2375680,27656192,-175161344,698793984,-1900969984,3141271552,762478592,-23831724032,81394581504,-155797291008,168312324096,-79474769920]),(⟨1,0,4⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨1,1,0⟩,[0,-65536,2064384,-27475968,209141760,-1048641536,3808641024,-10513989632,20486062080,-13565624320,-84242464768,396041994240,-927173165056,1318304415744,-1076893368320,388436901888]),(⟨1,1,1⟩,[0,0,212992,-4571136,39845888,-211501056,994426880,-4669145088,17196908544,-40124973056,40735129600,62771380224,-294632554496,440655265792,-255365332992]),(⟨1,1,2⟩,[0,32768,-917504,10420224,-65142784,267354112,-794558464,1558315008,-1043595264,-3896541184,14609416192,-20518600704,1303773184,16623108096]),(⟨1,1,3⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨1,2,0⟩,[-8192,303104,-4448256,33980416,-147038208,342794240,-133029888,-2343305216,11705622528,-35087589376,71664623616,-88909709312,32647028736,68929380352,-76683780096]),(⟨1,2,1⟩,[0,32768,-917504,10420224,-65142784,267354112,-794558464,1558315008,-1043595264,-3896541184,14609416192,-20518600704,1303773184,16623108096]),(⟨1,3,0⟩,[0,114688,-3358720,38846464,-241418240,935723008,-2458681344,3738796032,3540811776,-43576868864,144860495872,-278900129792,309468020736,-154582220800]),(⟨1,3,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨1,3,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨1,3,3⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,4,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨1,4,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨1,4,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[-16384,458752,-5013504,26050560,-48889856,-172048384,1549058048,-6406881280,18847088640,-35611836416,11763515392,161336197120,-544779632640,924588687360,-866660728832,353424949248]),(⟨2,0,1⟩,[0,65536,-1490944,13746176,-70844416,235290624,-373997568,-1579581440,14182514688,-50228002816,96895221760,-82355109888,-57229639680,209671110656,-157076570112]),(⟨2,0,2⟩,[16384,-458752,4915200,-24887296,55427072,9388032,-443154432,1817214976,-4581113856,7374209024,-9207873536,13313982464,-21421080576,19814301696]),(⟨2,0,3⟩,[-16384,360448,-3227648,16646144,-61603840,200081408,-701661184,2387476480,-5352472576,6310952960,-4728045568,3847749632,97026048]),(⟨2,0,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[0,65536,-1490944,13746176,-70844416,235290624,-373997568,-1579581440,14182514688,-50228002816,96895221760,-82355109888,-57229639680,209671110656,-157076570112]),(⟨2,1,1⟩,[0,0,98304,-2162688,14057472,8749056,-463798272,1927544832,-2423193600,-4224909312,18694766592,-18282381312,-19533889536,36767367168]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[0,131072,-3145728,29589504,-140247040,359006208,-462684160,-117112832,2220621824,-4795400192,3389259776,191070208]),(⟨2,1,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,2,0⟩,[16384,-458752,4915200,-24887296,55427072,9388032,-443154432,1817214976,-4581113856,7374209024,-9207873536,13313982464,-21421080576,19814301696]),(⟨2,2,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,2,2⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨2,2,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,3,0⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨2,3,1⟩,[0,131072,-3145728,29589504,-140247040,359006208,-462684160,-117112832,2220621824,-4795400192,3389259776,191070208]),(⟨2,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,4,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,4,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,0,0⟩,[-16384,663552,-10395648,84721664,-404455424,1202413568,-2172182528,490504192,16251076608,-81073348608,231519133696,-430399373312,504117592064,-310111657984,48359399424]),(⟨3,0,1⟩,[0,65536,-1802240,18857984,-102006784,360267776,-1094123520,2595848192,-1209860096,-17668538368,74219945984,-156235022336,175005859840,-80184459264]),(⟨3,0,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,0,3⟩,[0,81920,-1572864,12861440,-63438848,243433472,-893386752,2794618880,-5390204928,4804329472,-2463629312,3507044352]),(⟨3,0,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[0,65536,-1802240,18857984,-102006784,360267776,-1094123520,2595848192,-1209860096,-17668538368,74219945984,-156235022336,175005859840,-80184459264]),(⟨3,1,1⟩,[-16384,573440,-7946240,55066624,-186515456,126582784,1276477440,-4695228416,5893242880,3993485312,-23055056896,27363065856,-9689989120]),(⟨3,1,2⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,2,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,2,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,32768,-262144,491520,-6815744,99418112,-745537536,3557228544,-10210508800,17939726336,-23279173632,19624722432]),(⟨3,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨4,0,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,0,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,1,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,1,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,1,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,2,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨5,0,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨6,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[8192,-319488,5316608,-50479104,308649984,-1303633920,3973455872,-8638152704,9659768832,22820773888,-175091589120,576609402880,-1226753056768,1751567785984,-1593712680960,787903463424,-127166054400]),(⟨0,1,1⟩,[0,-65536,2064384,-27475968,209141760,-1048641536,3808641024,-10513989632,20486062080,-13565624320,-84242464768,396041994240,-927173165056,1318304415744,-1076893368320,388436901888]),(⟨0,1,2⟩,[-8192,303104,-4448256,33980416,-147038208,342794240,-133029888,-2343305216,11705622528,-35087589376,71664623616,-88909709312,32647028736,68929380352,-76683780096]),(⟨0,1,3⟩,[0,81920,-2375680,27656192,-175161344,698793984,-1900969984,3141271552,762478592,-23831724032,81394581504,-155797291008,168312324096,-79474769920]),(⟨0,1,4⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨0,2,0⟩,[-16384,458752,-5013504,26050560,-48889856,-172048384,1549058048,-6406881280,18847088640,-35611836416,11763515392,161336197120,-544779632640,924588687360,-866660728832,353424949248]),(⟨0,2,1⟩,[0,65536,-1490944,13746176,-70844416,235290624,-373997568,-1579581440,14182514688,-50228002816,96895221760,-82355109888,-57229639680,209671110656,-157076570112]),(⟨0,2,2⟩,[16384,-458752,4915200,-24887296,55427072,9388032,-443154432,1817214976,-4581113856,7374209024,-9207873536,13313982464,-21421080576,19814301696]),(⟨0,2,3⟩,[-16384,360448,-3227648,16646144,-61603840,200081408,-701661184,2387476480,-5352472576,6310952960,-4728045568,3847749632,97026048]),(⟨0,2,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,2,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,2,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,3,0⟩,[-16384,663552,-10395648,84721664,-404455424,1202413568,-2172182528,490504192,16251076608,-81073348608,231519133696,-430399373312,504117592064,-310111657984,48359399424]),(⟨0,3,1⟩,[0,65536,-1802240,18857984,-102006784,360267776,-1094123520,2595848192,-1209860096,-17668538368,74219945984,-156235022336,175005859840,-80184459264]),(⟨0,3,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨0,3,3⟩,[0,81920,-1572864,12861440,-63438848,243433472,-893386752,2794618880,-5390204928,4804329472,-2463629312,3507044352]),(⟨0,3,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨0,3,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨0,4,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨0,4,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,4,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨0,5,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨0,5,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,5,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,6,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨0,6,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[8192,-319488,5316608,-50479104,308649984,-1303633920,3973455872,-8638152704,9659768832,22820773888,-175091589120,576609402880,-1226753056768,1751567785984,-1593712680960,787903463424,-127166054400]),(⟨1,0,1⟩,[0,-65536,2064384,-27475968,209141760,-1048641536,3808641024,-10513989632,20486062080,-13565624320,-84242464768,396041994240,-927173165056,1318304415744,-1076893368320,388436901888]),(⟨1,0,2⟩,[-8192,303104,-4448256,33980416,-147038208,342794240,-133029888,-2343305216,11705622528,-35087589376,71664623616,-88909709312,32647028736,68929380352,-76683780096]),(⟨1,0,3⟩,[0,81920,-2375680,27656192,-175161344,698793984,-1900969984,3141271552,762478592,-23831724032,81394581504,-155797291008,168312324096,-79474769920]),(⟨1,0,4⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨1,1,0⟩,[0,-98304,3145728,-42369024,325746688,-1644920832,5980913664,-16327475200,30274027520,-10260873216,-175651487744,741106679808,-1688363302912,2390609461248,-1984126025728,745429106688]),(⟨1,1,1⟩,[0,0,294912,-5996544,47775744,-232292352,1184661504,-6681722880,27567194112,-68327374848,74437459968,94518018048,-481633173504,727625859072,-422456229888]),(⟨1,1,2⟩,[0,32768,-917504,10616832,-70254592,318275584,-1035206656,2054160384,-869793792,-7295893504,22126133248,-22408200192,-16056320000,36112269312]),(⟨1,1,3⟩,[0,0,-196608,4063232,-34144256,167247872,-579731456,1441005568,-2040659968,-254279680,9028304896,-21843017728,18943246336]),(⟨1,2,0⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨1,2,1⟩,[0,32768,-819200,8060928,-45973504,225181696,-1017708544,2990014464,-3640590336,-4722098176,25787465728,-36911382528,-870023168,33901314048]),(⟨1,2,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨1,2,3⟩,[0,131072,-3145728,29589504,-140247040,359006208,-462684160,-117112832,2220621824,-4795400192,3389259776,191070208]),(⟨1,2,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,3,0⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨1,3,1⟩,[-16384,573440,-8142848,59129856,-220659712,293830656,696745984,-3254222848,3852582912,3739205632,-14026752000,5520048128,9253257216]),(⟨1,3,2⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨1,3,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨1,4,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨1,4,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨1,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[-16384,458752,-5013504,26050560,-48889856,-172048384,1549058048,-6406881280,18847088640,-35611836416,11763515392,161336197120,-544779632640,924588687360,-866660728832,353424949248]),(⟨2,0,1⟩,[0,65536,-1490944,13746176,-70844416,235290624,-373997568,-1579581440,14182514688,-50228002816,96895221760,-82355109888,-57229639680,209671110656,-157076570112]),(⟨2,0,2⟩,[16384,-458752,4915200,-24887296,55427072,9388032,-443154432,1817214976,-4581113856,7374209024,-9207873536,13313982464,-21421080576,19814301696]),(⟨2,0,3⟩,[-16384,360448,-3227648,16646144,-61603840,200081408,-701661184,2387476480,-5352472576,6310952960,-4728045568,3847749632,97026048]),(⟨2,0,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨2,1,1⟩,[0,32768,-819200,8060928,-45973504,225181696,-1017708544,2990014464,-3640590336,-4722098176,25787465728,-36911382528,-870023168,33901314048]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[0,131072,-3145728,29589504,-140247040,359006208,-462684160,-117112832,2220621824,-4795400192,3389259776,191070208]),(⟨2,1,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,2,0⟩,[32768,-917504,9830400,-49971200,115965952,-32145408,-645660672,3138584576,-9336029184,18147770368,-25932464128,28517564416,-25482067968,20139442176]),(⟨2,2,1⟩,[-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨2,2,2⟩,[0,196608,-5111808,50921472,-240648192,495845376,173801472,-3399352320,7516717056,-1889599488,-17360093184,19489161216]),(⟨2,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,3,0⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨2,3,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨2,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,4,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,0,0⟩,[-16384,663552,-10395648,84721664,-404455424,1202413568,-2172182528,490504192,16251076608,-81073348608,231519133696,-430399373312,504117592064,-310111657984,48359399424]),(⟨3,0,1⟩,[0,65536,-1802240,18857984,-102006784,360267776,-1094123520,2595848192,-1209860096,-17668538368,74219945984,-156235022336,175005859840,-80184459264]),(⟨3,0,2⟩,[-8192,180224,-1703936,11026432,-61612032,279412736,-965017600,2541518848,-4567752704,4875993088,-4512612352,4740562944,-192503808]),(⟨3,0,3⟩,[0,81920,-1572864,12861440,-63438848,243433472,-893386752,2794618880,-5390204928,4804329472,-2463629312,3507044352]),(⟨3,0,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨3,1,1⟩,[-16384,573440,-8142848,59129856,-220659712,293830656,696745984,-3254222848,3852582912,3739205632,-14026752000,5520048128,9253257216]),(⟨3,1,2⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨3,2,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,32768,-262144,491520,-6815744,99418112,-745537536,3557228544,-10210508800,17939726336,-23279173632,19624722432]),(⟨3,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨4,0,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,0,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,1,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,1,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,1,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,2,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨5,0,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨6,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-565248,8544256,-75235328,433717248,-1743593472,5016690688,-9650765824,4651401216,58238509056,-308260003840,934601752576,-1946635108352,2827413921792,-2746339336192,1605741576192,-453392891904,46902804480]),(⟨0,0,1⟩,[8192,-385024,7184384,-73678848,477454336,-2122883072,6820257792,-15686631424,18801713152,41999196160,-339055583232,1133098614784,-2426701766656,3478342443008,-3176724226048,1579516854272,-258835906560]),(⟨0,0,2⟩,[-32768,991232,-12230656,79642624,-289701888,498524160,546856960,-7019757568,28644311040,-74796965888,115027484672,-28016099328,-314539278336,763502862336,-820562747392,349149954048]),(⟨0,0,3⟩,[-16384,761856,-12869632,111181824,-566542336,1844977664,-3836403712,2438856704,21951889408,-120472870912,348650070016,-645837258752,751887564800,-463376064512,76615081984]),(⟨0,0,4⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨0,0,5⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨0,0,6⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨0,1,0⟩,[8192,-385024,7184384,-73678848,477454336,-2122883072,6820257792,-15686631424,18801713152,41999196160,-339055583232,1133098614784,-2426701766656,3478342443008,-3176724226048,1579516854272,-258835906560]),(⟨0,1,1⟩,[0,-98304,3047424,-39370752,288538624,-1407074304,5212520448,-15835561984,36040048640,-33858256896,-137692184576,741067603968,-1801516367872,2596276518912,-2134181625856,774499074048]),(⟨0,1,2⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨0,1,3⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨0,1,4⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨0,2,0⟩,[-32768,991232,-12230656,79642624,-289701888,498524160,546856960,-7019757568,28644311040,-74796965888,115027484672,-28016099328,-314539278336,763502862336,-820562747392,349149954048]),(⟨0,2,1⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨0,2,2⟩,[32768,-917504,9830400,-49971200,115965952,-32145408,-645660672,3138584576,-9336029184,18147770368,-25932464128,28517564416,-25482067968,20139442176]),(⟨0,2,3⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨0,2,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,2,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,2,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,3,0⟩,[-16384,761856,-12869632,111181824,-566542336,1844977664,-3836403712,2438856704,21951889408,-120472870912,348650070016,-645837258752,751887564800,-463376064512,76615081984]),(⟨0,3,1⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨0,3,2⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨0,3,3⟩,[0,32768,-262144,491520,-6815744,99418112,-745537536,3557228544,-10210508800,17939726336,-23279173632,19624722432]),(⟨0,3,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨0,3,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨0,4,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨0,4,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,4,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨0,5,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨0,5,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,5,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,6,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨0,6,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[8192,-385024,7184384,-73678848,477454336,-2122883072,6820257792,-15686631424,18801713152,41999196160,-339055583232,1133098614784,-2426701766656,3478342443008,-3176724226048,1579516854272,-258835906560]),(⟨1,0,1⟩,[0,-98304,3047424,-39370752,288538624,-1407074304,5212520448,-15835561984,36040048640,-33858256896,-137692184576,741067603968,-1801516367872,2596276518912,-2134181625856,774499074048]),(⟨1,0,2⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨1,0,3⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨1,0,4⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨1,1,0⟩,[0,-98304,3047424,-39370752,288538624,-1407074304,5212520448,-15835561984,36040048640,-33858256896,-137692184576,741067603968,-1801516367872,2596276518912,-2134181625856,774499074048]),(⟨1,1,1⟩,[0,0,245760,-4276224,23789568,-62373888,570703872,-6037733376,31110856704,-84607205376,101106991104,95239913472,-561001857024,860911779840,-501272690688]),(⟨1,1,2⟩,[-32768,1032192,-13221888,87343104,-302104576,389152768,904298496,-4875780096,9012510720,-4735123456,-11930222592,31644303360,-50888556544,43591303168]),(⟨1,1,3⟩,[-16384,573440,-8142848,59129856,-220659712,293830656,696745984,-3254222848,3852582912,3739205632,-14026752000,5520048128,9253257216]),(⟨1,1,4⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨1,1,5⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨1,2,0⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨1,2,1⟩,[-32768,1032192,-13221888,87343104,-302104576,389152768,904298496,-4875780096,9012510720,-4735123456,-11930222592,31644303360,-50888556544,43591303168]),(⟨1,2,2⟩,[-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨1,2,3⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨1,2,4⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨1,3,0⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨1,3,1⟩,[-16384,573440,-8142848,59129856,-220659712,293830656,696745984,-3254222848,3852582912,3739205632,-14026752000,5520048128,9253257216]),(⟨1,3,2⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨1,3,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨1,4,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨1,4,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨1,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[-32768,991232,-12230656,79642624,-289701888,498524160,546856960,-7019757568,28644311040,-74796965888,115027484672,-28016099328,-314539278336,763502862336,-820562747392,349149954048]),(⟨2,0,1⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨2,0,2⟩,[32768,-917504,9830400,-49971200,115965952,-32145408,-645660672,3138584576,-9336029184,18147770368,-25932464128,28517564416,-25482067968,20139442176]),(⟨2,0,3⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨2,0,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-8192,368640,-6070272,50872320,-249798656,768794624,-1311219712,-1266319360,19061514240,-73393020928,161527046144,-202289561600,83049324544,124915818496,-145485914112]),(⟨2,1,1⟩,[-32768,1032192,-13221888,87343104,-302104576,389152768,904298496,-4875780096,9012510720,-4735123456,-11930222592,31644303360,-50888556544,43591303168]),(⟨2,1,2⟩,[-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨2,1,3⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨2,1,4⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨2,2,0⟩,[32768,-917504,9830400,-49971200,115965952,-32145408,-645660672,3138584576,-9336029184,18147770368,-25932464128,28517564416,-25482067968,20139442176]),(⟨2,2,1⟩,[-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨2,2,2⟩,[0,196608,-5111808,50921472,-240648192,495845376,173801472,-3399352320,7516717056,-1889599488,-17360093184,19489161216]),(⟨2,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,3,0⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨2,3,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨2,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,4,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,0,0⟩,[-16384,761856,-12869632,111181824,-566542336,1844977664,-3836403712,2438856704,21951889408,-120472870912,348650070016,-645837258752,751887564800,-463376064512,76615081984]),(⟨3,0,1⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨3,0,2⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨3,0,3⟩,[0,32768,-262144,491520,-6815744,99418112,-745537536,3557228544,-10210508800,17939726336,-23279173632,19624722432]),(⟨3,0,4⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[0,114688,-3260416,36290560,-217137152,842629120,-2441183232,4674650112,770015232,-41003073536,148521828352,-293403312128,324654317568,-156793176064]),(⟨3,1,1⟩,[-16384,573440,-8142848,59129856,-220659712,293830656,696745984,-3254222848,3852582912,3739205632,-14026752000,5520048128,9253257216]),(⟨3,1,2⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,81920,327680,-4866048,1073152,137658368,-870121472,3565912064,-9787105280,17411489792,-23212064768,20065206272,-2341527552]),(⟨3,2,1⟩,[32768,-720896,4947968,-1441792,-134414336,670957568,-1386283008,740818944,3441065984,-9629794304,8451358720,-545914880]),(⟨3,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,32768,-262144,491520,-6815744,99418112,-745537536,3557228544,-10210508800,17939726336,-23279173632,19624722432]),(⟨3,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[16384,-376832,2473984,3538944,-120848384,677756928,-2107277312,3997696000,3293184,-32306118656,121043206144,-245067546624,286743166976,-151391027200]),(⟨4,0,1⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,0,3⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,1,0⟩,[0,0,-147456,2490368,-16007168,79167488,-484474880,2172387328,-5037260800,3498573824,12429475840,-38908592128,35525410816]),(⟨4,1,1⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,1,2⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨4,2,1⟩,[16384,-524288,6144000,-31719424,51806208,180092928,-1018724352,1744044032,559235072,-6530793472,6919471104]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-376832,5586944,-37404672,125362176,-204177408,-73564160,2202828800,-9653985280,23636033536,-37183471616,31542099968,-4587577344]),(⟨5,0,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-49152,1310720,-12369920,56623104,-144015360,147849216,762609664,-4820303872,13135396864,-20815544320,16117678080]),(⟨6,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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
    (Poly.add (Poly.scale (K.ofRat r700) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 7 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r699*r699 : ℚ)=r700 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 7 11 r699 r699 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 7=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 7 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C126

#print axioms Coulomb8.Columns.C126.sound
