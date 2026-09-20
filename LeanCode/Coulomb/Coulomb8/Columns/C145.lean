import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C145

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 20545536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -212533248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1510965248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -7911931904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 32158679040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -106076504064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 291732422656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -661348384768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1157177180160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -1344653819904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 565735358464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 60441001984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1962510286848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 1341949673472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -48988422144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 27179089920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 10977280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -151781376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1277493248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -7443415040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 32620052480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -114381815808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 6765281280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -781079052288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1389092438016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1584394665984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 551940849664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 1378187444224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -325189206016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1295255863296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -25810698240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 2326528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -35160064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 303890432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -1693646848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 6515294208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -18198593536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 5403901952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -51435995136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -4159012864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 238340177920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -580446650368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 551648952320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 86632988672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -548404035584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 40749957120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 884736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -24412160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 294387712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -2089549824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 10024747008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -2112126976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 102931628032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -235525636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 384064061440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -321357447168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -136579121152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 591618637824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -450326921216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 64957612032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 12910592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -63176704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 36667392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 1202651136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1100349440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 28642902016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -77469351936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 145769693184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -144858349568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -20792999936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 193842413568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -18632998912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 13172736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -134742016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 762249216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -2795503616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 7648968704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -16594763776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 23585488896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -6863454208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -33160364032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 38300811264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -770375680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -33161216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 244842496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -156762112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 3538157568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -8532000768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1858600960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -5943853056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -12567314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 14599716864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -37814272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 395575296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2567766016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 12313493504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -49479680000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 171703271424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -476599418880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 133907152896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -1087222382592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 40812937216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1053873864704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -1427889258496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 86124134400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -10387456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 128581632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -132972544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 4551180288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -16505470976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 46471315456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -97913536512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 18539577344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -40381284352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -25561006080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 39688798208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -14570520576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -823296000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 48824320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -427163648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 334036992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -9780854784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 34215690240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -5478547456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 166323945472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -138988617728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -61692116992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 224550584320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -19169738752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 43646976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -372768768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 1502085120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -2323906560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -2786328576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 14707851264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -13578534912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -8989310976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 126222336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 262144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1089273856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -3329753088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 1103101952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -15260188672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 21148401664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -4042391552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -5457051648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 959315968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -6225920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 19660800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -66322432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 489684992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -313524224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 7076315136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -17064001536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 3717201920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -11887706112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -25134628864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 29199433728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 589824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -107937792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 1164902400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -958464000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 21383479296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -29858070528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -29412163584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 186456342528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -263300382720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 663552000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 37515755520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -232980480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -30867456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 247922688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -1201537024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 3367895040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -77463552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -6692143104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 29253369856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -34791948288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -266010624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 32707903488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -21140602880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 19660800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -11993088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 127467520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -701825024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 117833728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1815478272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -5591924736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 17931042816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -14547746816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -9965862912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 20189609984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -54984704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 26935296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -176422912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 594149376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -685768704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1697251328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 6177685504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -629997568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -828375040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1162412032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -1310720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 14548992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 500695040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -774635520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -928776192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 4902617088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -4526178304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -2996436992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 42074112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -9437184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 30539776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2485256192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 7486570496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -13007585280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 4368629760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 40369782784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -108307546112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 2428502016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -33457307648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -211419136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 15400960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -75497472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 113901568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 864026624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -5862195200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 2043674624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -6689587200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -39122894848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 11649220608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -61865984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -4063232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 6815744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -274202624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 834404352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -1273233408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -12058624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 315097088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -1717698560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 7200702464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 28311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -101711872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 362807296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -881328128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 85983232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 930086912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -9388949504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 90963968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -18874368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -509607936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -158859264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 3944742912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4595908608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -56623104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -34603008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 43253760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -1440743424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 4649385984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -12494831616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 24384110592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -6838812672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -99972808704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 31460425728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -181665792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 34734080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -187695104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 654573568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -1517813760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 598999040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 8343519232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -16689528832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -468451328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 24772608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -606208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 10272768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -106266624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 755482624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -3955965952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 16079339520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -53038252032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 145866211328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -330674192384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 578588590080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -672326909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 282867679232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 30220500992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -981255143424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 670974836736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -24494211072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 13589544960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 5488640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -75890688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 638746624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -3721707520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 16310026240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -57190907904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 3382640640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -390539526144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 694546219008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -792197332992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 275970424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 689093722112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -162594603008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 647627931648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -12905349120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 1163264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -17580032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 151945216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -846823424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 3257647104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -9099296768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 2701950976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -25717997568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -2079506432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 119170088960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -290223325184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 275824476160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 43316494336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -274202017792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 20374978560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 442368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -12206080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 147193856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -1044774912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 5012373504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -1056063488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 51465814016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -117762818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 192032030720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -160678723584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -68289560576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 295809318912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -225163460608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 32478806016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 6455296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -31588352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 18333696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 601325568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -550174720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 14321451008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -38734675968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 72884846592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -72429174784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -10396499968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 96921206784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -9316499456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 6586368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -67371008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 381124608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -1397751808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 3824484352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -8297381888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 11792744448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -3431727104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -16580182016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 19150405632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -385187840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -16580608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 122421248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -78381056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 1769078784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -4266000384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 929300480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -2971926528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -6283657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 7299858432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -18907136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 197787648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -1283883008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 6156746752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -24739840000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 85851635712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -238299709440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 66953576448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -543611191296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 20406468608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 526936932352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -713944629248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 43062067200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -5193728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 64290816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -66486272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 2275590144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -8252735488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 23235657728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -48956768256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 9269788672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -20190642176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -12780503040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 19844399104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -7285260288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -411648000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -1245184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 24412160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -213581824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 167018496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -4890427392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 17107845120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -2739273728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 83161972736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -69494308864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -30846058496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 112275292160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -9584869376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 21823488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -186384384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 751042560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -1161953280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -1393164288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 7353925632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -6789267456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -4494655488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 63111168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 131072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -118292480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 544636928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -1664876544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 551550976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -7630094336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 10574200832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -2021195776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -2728525824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 479657984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -3112960, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 9830400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 294912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -53968896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 582451200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -479232000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 10691739648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -14929035264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -14706081792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 93228171264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -131650191360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 331776000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 18757877760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -116490240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -15433728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 123961344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -600768512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 1683947520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -38731776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -3346071552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 14626684928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -17395974144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -133005312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 16353951744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -10570301440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 9830400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -5996544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 63733760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -350912512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 58916864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -907739136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -2795962368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 8965521408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -7273873408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -4982931456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 10094804992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -27492352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 13467648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -88211456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 297074688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -342884352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -848625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 3088842752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -314998784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -414187520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 581206016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 250347520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -387317760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -464388096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 2451308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -2263089152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -1498218496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 21037056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -4718592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 15269888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -1242628096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 3743285248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -6503792640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 2184314880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 20184891392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -54153773056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 1214251008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -16728653824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -105709568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 7700480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -37748736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 56950784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 432013312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -2931097600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 1021837312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -3344793600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -19561447424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 5824610304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -30932992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 3407872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -137101312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 417202176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -636616704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -6029312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 157548544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -858849280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 3600351232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 14155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 181403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -440664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 42991616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 465043456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -4694474752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 45481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -254803968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -79429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 1972371456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -2297954304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -28311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -17301504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 21626880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -720371712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 2324692992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -6247415808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 12192055296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -3419406336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -49986404352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 15730212864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -90832896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 17367040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -93847552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 327286784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -758906880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 299499520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 4171759616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -8344764416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -234225664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 12386304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[0,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33],[r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49],[0,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[r0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[0,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[0,0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98],[],[],[],[],[],[],[0,0,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[0,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,0,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138],[0,0,0,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[],[],[],[],[],[],[],[r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162],[0,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[],[],[],[],[],[],[],[0,0,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184],[r34,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197],[0,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209],[r149,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220],[0,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230],[],[],[],[],[],[r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243],[r149,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254],[r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265],[0,r266,r267,r268,r269,r270,r271,r272,r273,r274],[],[],[],[],[0,0,r275,r276,r277,r278,r279,r280,r281,r282,786432],[],[],[],[],[],[],[],[],[],[],[],[0,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293],[r255,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303],[0,r266,r267,r268,r269,r270,r271,r272,r273,r274],[],[],[],[],[],[r304,r305,r306,r307,r308,r309,r310,r311,262144],[],[],[],[],[],[],[],[r275,r276,r277,r278,r279,r280,r281,r282,786432],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329]),(⟨0,0,1⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345]),(⟨0,0,2⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361]),(⟨0,0,3⟩,[0,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,0,4⟩,[r312,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,0,5⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨0,0,6⟩,[0,0,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,1,0⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345]),(⟨0,1,1⟩,[0,0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨0,1,2⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨0,1,3⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨0,1,4⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,2,0⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361]),(⟨0,2,1⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨0,2,2⟩,[r0,r64,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨0,2,3⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨0,3,0⟩,[0,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,3,1⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨0,3,2⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨0,3,3⟩,[0,0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98]),(⟨0,4,0⟩,[r312,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,4,1⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,5,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨0,6,0⟩,[0,0,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨1,0,0⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345]),(⟨1,0,1⟩,[0,0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨1,0,2⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨1,0,3⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨1,0,4⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,1,0⟩,[0,0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨1,1,1⟩,[0,0,0,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨1,1,2⟩,[r346,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨1,1,3⟩,[0,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509]),(⟨1,1,4⟩,[r0,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨1,1,5⟩,[0,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,2,0⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨1,2,1⟩,[r346,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨1,2,2⟩,[r34,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨1,2,3⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨1,2,4⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨1,2,5⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨1,3,0⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨1,3,1⟩,[0,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509]),(⟨1,3,2⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨1,3,3⟩,[0,0,r572,r573,r574,r575,r576,r577,r578,r579,393216]),(⟨1,4,0⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,4,1⟩,[r0,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨1,4,2⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨1,5,1⟩,[0,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,5,2⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,0,0⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361]),(⟨2,0,1⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨2,0,2⟩,[r0,r64,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨2,0,3⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨2,1,0⟩,[0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨2,1,1⟩,[r346,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨2,1,2⟩,[r34,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨2,1,3⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨2,1,4⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨2,1,5⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,2,0⟩,[r0,r64,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨2,2,1⟩,[r34,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨2,2,2⟩,[0,r275,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589]),(⟨2,2,3⟩,[r149,r590,r591,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨2,2,4⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,3,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨2,3,1⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨2,3,2⟩,[r149,r590,r591,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨2,3,4⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨2,4,1⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨2,4,2⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,4,3⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨2,5,1⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨3,0,0⟩,[0,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨3,0,1⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨3,0,2⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨3,0,3⟩,[0,0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98]),(⟨3,1,0⟩,[0,0,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨3,1,1⟩,[0,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509]),(⟨3,1,2⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨3,1,3⟩,[0,0,r572,r573,r574,r575,r576,r577,r578,r579,393216]),(⟨3,2,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨3,2,1⟩,[r0,r266,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552]),(⟨3,2,2⟩,[r149,r590,r591,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨3,2,4⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨3,3,0⟩,[0,0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98]),(⟨3,3,1⟩,[0,0,r572,r573,r574,r575,r576,r577,r578,r579,393216]),(⟨3,3,3⟩,[r572,r573,r574,r575,r576,r577,r578,r579,393216]),(⟨3,4,2⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨4,0,0⟩,[r312,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨4,0,1⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨4,1,0⟩,[0,0,0,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨4,1,1⟩,[r0,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨4,1,2⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨4,2,1⟩,[r149,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562]),(⟨4,2,2⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨4,2,3⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨4,3,2⟩,[r255,r600,r601,r602,r603,r604,r605,r606,131072]),(⟨5,0,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400]),(⟨5,1,1⟩,[0,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨5,1,2⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨5,2,1⟩,[0,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨6,0,0⟩,[0,0,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r607) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r607) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

noncomputable def partial12 : Poly := [(⟨1,2,1⟩,[-32768,1081344,-15532032,127107072,-641171456,1948581888,-2789081088,-2317418496,17172561920,-26662502400,6481969152,25051889664,-22775627776,2807562240]),(⟨1,2,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨1,2,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,3,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨1,4,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,5,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,0,0⟩,[-16384,573440,-8863744,80674816,-485343232,2060173312,-6514262016,16266559488,-33228701696,51994968064,-46526676992,-10833559552,77705494528,-69504385024,17010769920,-1238630400]),(⟨2,0,1⟩,[0,114688,-3227648,38469632,-261423104,1157939200,-3690086400,9269673984,-19147259904,29759586304,-25036963840,-8761835520,42946068480,-33175224320,4756684800]),(⟨2,0,2⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨2,0,3⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨2,1,0⟩,[0,114688,-3227648,38469632,-261423104,1157939200,-3690086400,9269673984,-19147259904,29759586304,-25036963840,-8761835520,42946068480,-33175224320,4756684800]),(⟨2,1,1⟩,[-32768,1081344,-15532032,127107072,-641171456,1948581888,-2789081088,-2317418496,17172561920,-26662502400,6481969152,25051889664,-22775627776,2807562240]),(⟨2,1,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,1,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,1,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,2,0⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨2,2,1⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,3,0⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨2,3,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,4,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,212992,-5947392,73007104,-530022400,2598060032,-9378545664,26413498368,-58198130688,91302510592,-74068869120,-32593412096,136200617984,-101735743488,12943441920]),(⟨3,0,1⟩,[0,0,-688128,14319616,-134905856,781615104,-3197960192,9856417792,-22665035776,35100622848,-25747292160,-16578478080,50789580800,-31439421440]),(⟨3,0,2⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨3,0,3⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨3,1,0⟩,[0,0,-688128,14319616,-134905856,781615104,-3197960192,9856417792,-22665035776,35100622848,-25747292160,-16578478080,50789580800,-31439421440]),(⟨3,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨3,2,0⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨3,2,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨3,2,2⟩,[65536,-1703936,16580608,-74973184,166854656,-249298944,458358784,227016704,-3748855808,5098569728,-818872320]),(⟨3,3,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨3,3,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[16384,-557056,7110656,-44826624,137412608,-50823168,-1267531776,6041370624,-17377935360,34090024960,-35297132544,-4826857472,47640821760,-31198576640]),(⟨4,1,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,2⟩,[65536,-1703936,16580608,-74973184,166854656,-249298944,458358784,227016704,-3748855808,5098569728,-818872320]),(⟨4,2,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨5,1,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨5,2,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨6,0,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,-65536,2031616,-29130752,257916928,-1593704448,7411564544,-27383267328,82610159616,-200214118400,363024220160,-418404597760,140097978368,386591096832,-624862724096,341916745728,-38149816320]),(⟨1,0,1⟩,[0,0,360448,-7831552,75595776,-451280896,2116616192,-9447047168,38742196224,-122625982464,260096360448,-311799349248,81145593856,301046300672,-391135756288,154928578560]),(⟨1,0,2⟩,[0,65536,-1966080,25821184,-203980800,1117650944,-4562649088,13965983744,-29809508352,35128934400,4846321664,-80701685760,95964725248,-17821597696,-24927436800]),(⟨1,0,3⟩,[0,0,-557056,10092544,-78675968,387514368,-1692467200,7251427328,-23902617600,48061349888,-43747016704,-14267580416,61485711360,-35654664192]),(⟨1,0,4⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,1,0⟩,[0,0,360448,-7831552,75595776,-451280896,2116616192,-9447047168,38742196224,-122625982464,260096360448,-311799349248,81145593856,301046300672,-391135756288,154928578560]),(⟨1,1,1⟩,[0,0,0,1376256,-35979264,388300800,-2236416000,7127826432,-9952690176,-9804054528,62152114176,-87766794240,10838016000,87536762880,-64690913280]),(⟨1,1,2⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,1,3⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,1,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,1,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,2,0⟩,[0,65536,-1966080,25821184,-203980800,1117650944,-4562649088,13965983744,-29809508352,35128934400,4846321664,-80701685760,95964725248,-17821597696,-24927436800]),(⟨1,2,1⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,2,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,2,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,3,0⟩,[0,0,-557056,10092544,-78675968,387514368,-1692467200,7251427328,-23902617600,48061349888,-43747016704,-14267580416,61485711360,-35654664192]),(⟨1,3,1⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,3,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,4,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,4,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,4,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,5,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,0,0⟩,[-16384,573440,-8404992,69599232,-363151360,1227571200,-2474131456,973766656,13880737792,-63678758912,162051997696,-242645401600,139405180928,156386246656,-305798103040,145267261440]),(⟨2,0,1⟩,[0,114688,-3227648,39157760,-279412736,1352089600,-4808294400,12833587200,-24123604992,24857559040,6039093248,-52645232640,48365076480,10593157120,-27588771840]),(⟨2,0,2⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨2,0,3⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨2,1,0⟩,[0,114688,-3227648,39157760,-279412736,1352089600,-4808294400,12833587200,-24123604992,24857559040,6039093248,-52645232640,48365076480,10593157120,-27588771840]),(⟨2,1,1⟩,[-32768,1081344,-15532032,127107072,-641171456,1948581888,-2789081088,-2317418496,17172561920,-26662502400,6481969152,25051889664,-22775627776,2807562240]),(⟨2,1,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,1,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,1,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,2,0⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨2,2,1⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,2,2⟩,[0,262144,-5767168,50462720,-240123904,774897664,-2082471936,4064018432,-1139802112,-16662134784,36703830016,-25221267456]),(⟨2,2,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨2,3,0⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨2,3,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,3,2⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,278528,-7913472,98140160,-716013568,3521560576,-12822986752,36815568896,-83031293952,131333472256,-100298604544,-69411700736,226746335232,-163325722624,20361461760]),(⟨3,0,1⟩,[0,0,-589824,11173888,-94502912,516980736,-2306736128,8827764736,-25210912768,44367151104,-32362266624,-25276416000,62994907136,-33077166080]),(⟨3,0,2⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨3,0,3⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨3,1,0⟩,[0,0,-589824,11173888,-94502912,516980736,-2306736128,8827764736,-25210912768,44367151104,-32362266624,-25276416000,62994907136,-33077166080]),(⟨3,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨3,1,2⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,1,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,2,0⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨3,2,1⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,2,2⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨3,3,1⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,3,3⟩,[393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨4,0,1⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,2⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨5,1,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨5,2,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨6,0,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-65536,2031616,-29130752,257916928,-1593704448,7411564544,-27383267328,82610159616,-200214118400,363024220160,-418404597760,140097978368,386591096832,-624862724096,341916745728,-38149816320]),(⟨0,1,1⟩,[0,0,360448,-7831552,75595776,-451280896,2116616192,-9447047168,38742196224,-122625982464,260096360448,-311799349248,81145593856,301046300672,-391135756288,154928578560]),(⟨0,1,2⟩,[0,65536,-1966080,25821184,-203980800,1117650944,-4562649088,13965983744,-29809508352,35128934400,4846321664,-80701685760,95964725248,-17821597696,-24927436800]),(⟨0,1,3⟩,[0,0,-557056,10092544,-78675968,387514368,-1692467200,7251427328,-23902617600,48061349888,-43747016704,-14267580416,61485711360,-35654664192]),(⟨0,1,4⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨0,2,0⟩,[-16384,573440,-8404992,69599232,-363151360,1227571200,-2474131456,973766656,13880737792,-63678758912,162051997696,-242645401600,139405180928,156386246656,-305798103040,145267261440]),(⟨0,2,1⟩,[0,114688,-3227648,39157760,-279412736,1352089600,-4808294400,12833587200,-24123604992,24857559040,6039093248,-52645232640,48365076480,10593157120,-27588771840]),(⟨0,2,2⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨0,2,3⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨0,3,0⟩,[0,278528,-7913472,98140160,-716013568,3521560576,-12822986752,36815568896,-83031293952,131333472256,-100298604544,-69411700736,226746335232,-163325722624,20361461760]),(⟨0,3,1⟩,[0,0,-589824,11173888,-94502912,516980736,-2306736128,8827764736,-25210912768,44367151104,-32362266624,-25276416000,62994907136,-33077166080]),(⟨0,3,2⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨0,3,3⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨0,4,0⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨0,4,1⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨0,5,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨0,6,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨1,0,0⟩,[0,-65536,2031616,-29130752,257916928,-1593704448,7411564544,-27383267328,82610159616,-200214118400,363024220160,-418404597760,140097978368,386591096832,-624862724096,341916745728,-38149816320]),(⟨1,0,1⟩,[0,0,360448,-7831552,75595776,-451280896,2116616192,-9447047168,38742196224,-122625982464,260096360448,-311799349248,81145593856,301046300672,-391135756288,154928578560]),(⟨1,0,2⟩,[0,65536,-1966080,25821184,-203980800,1117650944,-4562649088,13965983744,-29809508352,35128934400,4846321664,-80701685760,95964725248,-17821597696,-24927436800]),(⟨1,0,3⟩,[0,0,-557056,10092544,-78675968,387514368,-1692467200,7251427328,-23902617600,48061349888,-43747016704,-14267580416,61485711360,-35654664192]),(⟨1,0,4⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,1,0⟩,[0,0,819200,-18907136,197787648,-1283883008,6156746752,-24739840000,85851635712,-238299709440,468675035136,-543611191296,142845280256,526936932352,-713944629248,301434470400]),(⟨1,1,1⟩,[0,0,0,2064384,-53968896,582451200,-3354624000,10691739648,-14929035264,-14706081792,93228171264,-131650191360,16257024000,131305144320,-97036369920]),(⟨1,1,2⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,1,3⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,1,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,1,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,2,0⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨1,2,1⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,2,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,2,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,3,0⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨1,3,1⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,3,2⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨1,3,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨1,4,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,4,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,4,2⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨1,5,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,5,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,0,0⟩,[-16384,573440,-8404992,69599232,-363151360,1227571200,-2474131456,973766656,13880737792,-63678758912,162051997696,-242645401600,139405180928,156386246656,-305798103040,145267261440]),(⟨2,0,1⟩,[0,114688,-3227648,39157760,-279412736,1352089600,-4808294400,12833587200,-24123604992,24857559040,6039093248,-52645232640,48365076480,10593157120,-27588771840]),(⟨2,0,2⟩,[16384,-557056,7798784,-59146240,272318464,-832438272,1930428416,-3815047168,5287100416,-1010597888,-9549840384,11751620608,-3148759040,240844800]),(⟨2,0,3⟩,[0,-163840,3964928,-38502400,201424896,-660668416,1619329024,-3462332416,5564465152,-3445915648,-4472799232,6869385216,-1104445440]),(⟨2,1,0⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨2,1,1⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨2,1,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,1,3⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,1,4⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,2,0⟩,[32768,-1114112,15597568,-118292480,544636928,-1664876544,3860856832,-7630094336,10574200832,-2021195776,-19099680768,23503241216,-6297518080,481689600]),(⟨2,2,1⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,2,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨2,2,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨2,3,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨2,3,1⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨2,3,2⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨2,4,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨3,0,0⟩,[0,278528,-7913472,98140160,-716013568,3521560576,-12822986752,36815568896,-83031293952,131333472256,-100298604544,-69411700736,226746335232,-163325722624,20361461760]),(⟨3,0,1⟩,[0,0,-589824,11173888,-94502912,516980736,-2306736128,8827764736,-25210912768,44367151104,-32362266624,-25276416000,62994907136,-33077166080]),(⟨3,0,2⟩,[0,-98304,2621440,-28868608,179699712,-737083392,2205155328,-4835049472,6228279296,14188544,-12107382784,12281020416,-1591869440]),(⟨3,0,3⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨3,1,0⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨3,1,1⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨3,1,2⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,1,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,2,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨3,2,1⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,2,2⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,0,1966080,-33161216,244842496,-1097334784,3538157568,-8532000768,13010206720,-5943853056,-12567314432,14599716864]),(⟨3,3,1⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,3,3⟩,[393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨4,0,1⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,2⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨5,1,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨5,2,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨6,0,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-606208,10272768,-106266624,755482624,-3955965952,16079339520,-53038252032,145866211328,-330674192384,578588590080,-672326909952,282867679232,513748516864,-981255143424,670974836736,-171459477504,13589544960]),(⟨0,0,1⟩,[0,-180224,5488640,-75890688,638746624,-3721707520,16310026240,-57190907904,165749391360,-390539526144,694546219008,-792197332992,275970424832,689093722112,-1138162221056,647627931648,-90337443840]),(⟨0,0,2⟩,[-32768,1163264,-17580032,151945216,-846823424,3257647104,-9099296768,18913656832,-25717997568,-2079506432,119170088960,-290223325184,275824476160,43316494336,-274202017792,142624849920]),(⟨0,0,3⟩,[0,442368,-12206080,147193856,-1044774912,5012373504,-17953079296,51465814016,-117762818048,192032030720,-160678723584,-68289560576,295809318912,-225163460608,32478806016]),(⟨0,0,4⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨0,0,5⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨0,0,6⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨0,1,0⟩,[0,-180224,5488640,-75890688,638746624,-3721707520,16310026240,-57190907904,165749391360,-390539526144,694546219008,-792197332992,275970424832,689093722112,-1138162221056,647627931648,-90337443840]),(⟨0,1,1⟩,[0,0,819200,-18907136,197787648,-1283883008,6156746752,-24739840000,85851635712,-238299709440,468675035136,-543611191296,142845280256,526936932352,-713944629248,301434470400]),(⟨0,1,2⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨0,1,3⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨0,1,4⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨0,2,0⟩,[-32768,1163264,-17580032,151945216,-846823424,3257647104,-9099296768,18913656832,-25717997568,-2079506432,119170088960,-290223325184,275824476160,43316494336,-274202017792,142624849920]),(⟨0,2,1⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨0,2,2⟩,[32768,-1114112,15597568,-118292480,544636928,-1664876544,3860856832,-7630094336,10574200832,-2021195776,-19099680768,23503241216,-6297518080,481689600]),(⟨0,2,3⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨0,3,0⟩,[0,442368,-12206080,147193856,-1044774912,5012373504,-17953079296,51465814016,-117762818048,192032030720,-160678723584,-68289560576,295809318912,-225163460608,32478806016]),(⟨0,3,1⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨0,3,2⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨0,3,3⟩,[0,0,1966080,-33161216,244842496,-1097334784,3538157568,-8532000768,13010206720,-5943853056,-12567314432,14599716864]),(⟨0,4,0⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨0,4,1⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨0,5,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨0,6,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432]),(⟨1,0,0⟩,[0,-180224,5488640,-75890688,638746624,-3721707520,16310026240,-57190907904,165749391360,-390539526144,694546219008,-792197332992,275970424832,689093722112,-1138162221056,647627931648,-90337443840]),(⟨1,0,1⟩,[0,0,819200,-18907136,197787648,-1283883008,6156746752,-24739840000,85851635712,-238299709440,468675035136,-543611191296,142845280256,526936932352,-713944629248,301434470400]),(⟨1,0,2⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨1,0,3⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨1,0,4⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,1,0⟩,[0,0,819200,-18907136,197787648,-1283883008,6156746752,-24739840000,85851635712,-238299709440,468675035136,-543611191296,142845280256,526936932352,-713944629248,301434470400]),(⟨1,1,1⟩,[0,0,0,2064384,-53968896,582451200,-3354624000,10691739648,-14929035264,-14706081792,93228171264,-131650191360,16257024000,131305144320,-97036369920]),(⟨1,1,2⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,1,3⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,1,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,1,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,2,0⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨1,2,1⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨1,2,2⟩,[-65536,2293760,-33030144,259588096,-1242628096,3743285248,-6503792640,2184314880,20184891392,-54153773056,59498299392,-16728653824,-12579438592]),(⟨1,2,3⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨1,2,4⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨1,2,5⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨1,3,0⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨1,3,1⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨1,3,2⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨1,3,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨1,4,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨1,4,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,4,2⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨1,5,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,5,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,0,0⟩,[-32768,1163264,-17580032,151945216,-846823424,3257647104,-9099296768,18913656832,-25717997568,-2079506432,119170088960,-290223325184,275824476160,43316494336,-274202017792,142624849920]),(⟨2,0,1⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨2,0,2⟩,[32768,-1114112,15597568,-118292480,544636928,-1664876544,3860856832,-7630094336,10574200832,-2021195776,-19099680768,23503241216,-6297518080,481689600]),(⟨2,0,3⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨2,1,0⟩,[0,180224,-5193728,64290816,-465403904,2275590144,-8252735488,23235657728,-48956768256,64888520704,-20190642176,-89463521280,138910793728,-50996822016,-20170752000]),(⟨2,1,1⟩,[-32768,1081344,-15433728,123961344,-600768512,1683947520,-1897857024,-3346071552,14626684928,-17395974144,-133005312,16353951744,-10570301440,1169817600]),(⟨2,1,2⟩,[-65536,2293760,-33030144,259588096,-1242628096,3743285248,-6503792640,2184314880,20184891392,-54153773056,59498299392,-16728653824,-12579438592]),(⟨2,1,3⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨2,1,4⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨2,1,5⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,2,0⟩,[32768,-1114112,15597568,-118292480,544636928,-1664876544,3860856832,-7630094336,10574200832,-2021195776,-19099680768,23503241216,-6297518080,481689600]),(⟨2,2,1⟩,[-65536,2293760,-33030144,259588096,-1242628096,3743285248,-6503792640,2184314880,20184891392,-54153773056,59498299392,-16728653824,-12579438592]),(⟨2,2,2⟩,[0,786432,-17301504,151388160,-720371712,2324692992,-6247415808,12192055296,-3419406336,-49986404352,110111490048,-75663802368]),(⟨2,2,3⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨2,2,4⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,3,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨2,3,1⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨2,3,2⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨2,4,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨3,0,0⟩,[0,442368,-12206080,147193856,-1044774912,5012373504,-17953079296,51465814016,-117762818048,192032030720,-160678723584,-68289560576,295809318912,-225163460608,32478806016]),(⟨3,0,1⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨3,0,2⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨3,0,3⟩,[0,0,1966080,-33161216,244842496,-1097334784,3538157568,-8532000768,13010206720,-5943853056,-12567314432,14599716864]),(⟨3,1,0⟩,[0,0,-1245184,24412160,-213581824,1169129472,-4890427392,17107845120,-46567653376,83161972736,-69494308864,-30846058496,112275292160,-67094085632]),(⟨3,1,1⟩,[0,229376,-5996544,63733760,-350912512,1001586688,-907739136,-2795962368,8965521408,-7273873408,-4982931456,10094804992,-3271589888]),(⟨3,1,2⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,1,3⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,2,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨3,2,1⟩,[32768,-786432,7700480,-37748736,56950784,432013312,-2931097600,7152861184,-3344793600,-19561447424,40772272128,-25767182336]),(⟨3,2,2⟩,[65536,-1703936,17367040,-93847552,327286784,-758906880,299499520,4171759616,-8344764416,-1639579648,10317791232]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,0,1966080,-33161216,244842496,-1097334784,3538157568,-8532000768,13010206720,-5943853056,-12567314432,14599716864]),(⟨3,3,1⟩,[0,0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,3,3⟩,[393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[16384,-557056,6455296,-31588352,18333696,601325568,-3851223040,14321451008,-38734675968,72884846592,-72429174784,-10396499968,96921206784,-65215496192]),(⟨4,0,1⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,0⟩,[0,0,0,-983040,21823488,-186384384,751042560,-1161953280,-1393164288,7353925632,-6789267456,-4494655488,7510228992]),(⟨4,1,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,2⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,1⟩,[65536,-2031616,23855104,-137101312,417202176,-636616704,-6029312,2678325248,-6011944960,3600351232,1684537344]),(⟨4,2,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[0,-262144,6586368,-67371008,381124608,-1397751808,3824484352,-8297381888,11792744448,-3431727104,-16580182016,19150405632,-2696314880]),(⟨5,1,1⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨5,2,1⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨6,0,0⟩,[0,0,983040,-16580608,122421248,-548667392,1769078784,-4266000384,6505103360,-2971926528,-6283657216,7299858432])]


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
    (Poly.add (Poly.scale (K.ofRat r608) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 11 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r607*r607 : ℚ)=r608 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 11 12 r607 r607 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 11=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 11 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C145

#print axioms Coulomb8.Columns.C145.sound
