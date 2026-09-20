import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C100

def r0 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -17154048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 334462976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -552714240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 29734273024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -160965902336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 633449562112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -262268108800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 3901987635200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -5919555272704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 5964544606208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -3183902375936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -251967733760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1394041667584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -524359090176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -14468595712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 1325481984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 487047168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -5507219456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 41168470016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -30785028096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 813563658240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -2238106910720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 4448119619584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -6161210769408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 5392414687232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2047242534912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -129989804032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 1115607744512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -12089540608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -2453618688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 22495232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -368918528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 3410034688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -19530252288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 71189839872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -158080942080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 159332564992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 23127457792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -785645125632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 1094172098560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -568803917824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1261830144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 3750445056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 656130048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 6373376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -792428544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 8016625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -51512934400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 221660233728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -652735873024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 1305999704064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -241070866432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 1193315287040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -135414513664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -353818509312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 14451736576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 592330752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -61947904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 71827456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -11221286912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 60168863744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -202109124608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 432101130240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -564445380608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 374522642432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -14307180544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -13417316352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -130105344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -2801664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 321388544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2829271040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 14708703232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -46810955776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 90733150208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -97816444928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 35305521152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 3691528192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -276955136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -31997952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -5341184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 107937792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -1107165184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 6466633728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -22531080192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 393478144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -53443166208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 22744760320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 902922240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 5308416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 7012352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -123715584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1331036160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -9872031744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 3149463552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -217129631744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 657595891712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -1457361207296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 2249464020992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -2122539089920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 616981331968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 1041135648768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -158405951488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 1598767104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 5144903680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 3719168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -46809088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 262160384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -10338304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -6780944384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 47904800768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -177406574592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 3597615104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -724302512128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 18205392896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -114763710464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 563658752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -1113620480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -2489532416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 311296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -1540096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 23265280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -1445445632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 505790464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -36688871424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 114379456512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -255009587200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 383913574400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -338024464384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 83898597376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 15251062784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -780845056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -894681088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -5783552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 5455872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -804798464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 4194271232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -13518536704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 24785485824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -10584752128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -68330242048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 188954755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -32040173568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1952628736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 31653888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 4079616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -50987008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 46546944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -1102577664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 234455040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 932708352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -27033600, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 1726349312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -113295360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -66977792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 2408448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -27590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 228196352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -986382336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 2053570560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -456392704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -7065174016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 822575104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -1162379264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 7028736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -73302016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 630800384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -4059234304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 17626841088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -49000808448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 11772968960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -68935843840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -92946432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 851148800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 756137984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -2440560640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 1691533312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1982464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 19398656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -2113536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -1102643200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 554532864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -38607257600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 92109570048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -130982150144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 100738580480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4075028480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -147243008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 254607360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -5210112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 31522816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -933888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 208535552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 23003136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -1294336000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 3393208320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -66387968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -69697536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 16056320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1867776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -3473408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 229670912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -263585792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 10977607680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -5996412928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 95993790464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -119427891200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 8424882176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 161021952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -6651904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -4423680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 47120384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -251527168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 677838848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -546897920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -1807745024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 5223612416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3931996160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -203718656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 2424832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -98435072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -175374336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 2982936576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -493879296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 851968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1310720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 19398656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -680656896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -286785536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 3031171072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -425197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -2424832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -165281792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -3407872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 161873920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -2505572352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 89980928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 6946816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 12926976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -210026496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 1964015616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -11845976064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 48474341376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -134634848256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 230421626880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -111745548288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -581688311808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 1819276984320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -53618638848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 38568345600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -4539924480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -508182528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 933888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -8192000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -29163520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 1622786048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -6376177664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 15015608320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -18213470208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -5716885504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 9879928832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -3009085440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 3949854720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -4099981312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 162971648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -1179648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 131760128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1140981760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 5920899072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -18800181248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 32989184000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -9208332288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -101495947264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 254387814400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -39806730240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 2082340864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 48513024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -10420224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 63045632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -1867776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 417071104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 46006272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -2588672000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 6786416640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -132775936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -139395072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 32112640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -1130496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -19464192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -894042112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1664188416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -361627648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -90193920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 1261633536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -10764288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 205979648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -11239424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 19529728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -308543488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1506672640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -2264137728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -1841561600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 10051780608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1366097920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 17301504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -3932160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 58195968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -2041970688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -860356608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 9093513216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -1275592704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -589824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -8577024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 167231488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -276357120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 14867136512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -80482951168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 316724781056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -131134054400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 1950993817600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -2959777636352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 2982272303104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -1591951187968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -125983866880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 697020833792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -262179545088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -7234297856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 662740992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -12713984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 243523584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -2753609728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 20584235008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -15392514048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 406781829120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -1119053455360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 2224059809792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -3080605384704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 2696207343616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1023621267456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -64994902016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 557803872256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -6044770304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -1226809344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 11247616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -184459264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1705017344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -9765126144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 35594919936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -79040471040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 79666282496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 11563728896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -392822562816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 547086049280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -284401958912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -630915072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 1875222528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 328065024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -540672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 3186688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -396214272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 4008312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -25756467200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 110830116864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -326367936512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 652999852032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -120535433216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 596657643520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -67707256832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -176909254656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 7225868288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 296165376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -30973952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 35913728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -5610643456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 30084431872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -101054562304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 216050565120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -282222690304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 187261321216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -7153590272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -6708658176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -65052672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 245760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -1400832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 160694272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -1414635520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 7354351616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -23405477888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 45366575104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -48908222464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 17652760576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 1845764096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -138477568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -15998976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -2670592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 53968896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -553582592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 3233316864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -11265540096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 196739072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -26721583104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 11372380160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 451461120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 2654208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -90112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 3506176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -61857792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 665518080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -4936015872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 1574731776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -108564815872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 328797945856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -728680603648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 1124732010496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -1061269544960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 308490665984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 520567824384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -79202975744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 799383552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 2572451840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 1859584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -23404544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 131080192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -5169152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -3390472192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 23952400384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -88703287296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 1798807552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -362151256064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 9102696448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -57381855232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 281829376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -556810240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -1244766208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 155648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -770048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 11632640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -722722816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 252895232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -18344435712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 57189728256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -127504793600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 191956787200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -169012232192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 41949298688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 7625531392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -390422528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -447340544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -2891776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 2727936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -402399232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 2097135616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -6759268352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 12392742912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -5292376064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -34165121024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 94477377536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -16020086784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 976314368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 15826944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 2039808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -25493504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 23273472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -551288832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 117227520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 466354176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -13516800, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 863174656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -56647680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -33488896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 1204224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -13795328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 114098176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -493191168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 1026785280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -228196352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -3532587008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 411287552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -581189632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -245760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 3514368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -36651008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 315400192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -2029617152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 8813420544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -24500404224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 5886484480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -34467921920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -46473216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 425574400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 378068992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -1220280320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 845766656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -991232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 9699328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -1056768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -551321600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 277266432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -19303628800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 46054785024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -65491075072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 50369290240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -2037514240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -73621504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 127303680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -2605056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 15761408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -466944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 104267776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 11501568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -647168000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 1696604160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -33193984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -34848768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 8028160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 933888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -1736704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 114835456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -131792896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 5488803840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -2998206464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 47996895232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -59713945600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 4212441088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 80510976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -3325952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -2211840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 23560192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -125763584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 338919424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -273448960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -903872512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 2611806208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -1965998080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -101859328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 1212416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -31064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -49217536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -87687168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 1491468288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -246939648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 425984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 458752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -655360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 9699328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := -340328448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -143392768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 1515585536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -212598784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -1212416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 2359296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -82640896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -1703936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 80936960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -1252786176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 44990464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 3473408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := 6463488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -105013248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 982007808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -5922988032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 24237170688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -67317424128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 115210813440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := -55872774144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -290844155904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 909638492160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -26809319424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 19284172800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -2269962240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := -254091264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 466944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -4096000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -14581760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 811393024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -3188088832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 7507804160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -9106735104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -2858442752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := 4939964416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -1504542720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 1974927360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -2049990656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 81485824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 106496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := -589824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 65880064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -570490880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 2960449536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := -9400090624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 16494592000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := -4604166144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -50747973632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 127193907200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := -19903365120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := 1041170432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 24256512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -565248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -9732096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := 15335424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -447021056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := 832094208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := -180813824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := -45096960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := 630816768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := -5382144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 102989824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -5619712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := -1409024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := 9764864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -154271744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 753336320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := -1132068864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -920780800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := 5025890304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := -683048960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := 327680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := 8650752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := -1966080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := 29097984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := -1020985344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := -430178304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := 4546756608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := -637796352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := -294912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[0,0,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[0,0,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[0,0,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[0,0,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74],[0,0,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86],[0,0,r62,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96],[],[],[],[],[],[],[0,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[0,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[0,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141],[0,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154],[0,r63,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165],[0,r166,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176],[],[],[],[],[],[r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191],[0,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204],[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,-802816],[],[],[],[],[],[],[0,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228],[0,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239],[0,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249],[0,r240,r250,r251,r252,r253,r254,r255,r256,r257],[],[],[],[r217,r258,r259,r260,r261,r262,r263,r264,r265,r266,-458752],[],[r192,r267,r268,r269,r270,r271,r272,r273,65536],[],[],[],[],[],[],[0,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288],[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303],[0,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316],[r166,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,-1605632],[],[],[],[],[],[],[],[r205,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339],[],[],[],[],[],[],[0,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350],[r217,r258,r259,r260,r261,r262,r263,r264,r265,r266,-458752],[],[r192,r267,r268,r269,r270,r271,r272,r273,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249],[],[],[],[],[],[],[],[],[0,r33,r351,r352,r353,r354,r355,r356,r357,r358],[r340,r359,r360,r361,r362,r363,r364,r365,131072],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨0,0,1⟩,[0,0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,0,2⟩,[0,0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨0,0,3⟩,[0,0,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨0,0,4⟩,[0,0,r428,r217,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨0,0,5⟩,[0,0,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,0,6⟩,[0,0,r428,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461]),(⟨0,1,0⟩,[0,0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,1,1⟩,[0,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477]),(⟨0,1,2⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨0,1,3⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨0,1,4⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨0,1,5⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,1,6⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨0,2,0⟩,[0,0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨0,2,1⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨0,2,2⟩,[r541,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨0,2,3⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨0,2,4⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨0,3,0⟩,[0,0,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨0,3,1⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨0,3,2⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨0,3,3⟩,[0,r166,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨0,3,4⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨0,3,5⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨0,3,6⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨0,4,0⟩,[0,0,r428,r217,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨0,4,1⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨0,4,2⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨0,4,3⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨0,4,4⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨0,4,6⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨0,5,0⟩,[0,0,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,5,1⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,5,3⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨0,6,0⟩,[0,0,r428,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461]),(⟨0,6,1⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨0,6,3⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨0,6,4⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨1,0,0⟩,[0,0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,0,1⟩,[0,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477]),(⟨1,0,2⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨1,0,3⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨1,0,4⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨1,0,5⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,0,6⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨1,1,0⟩,[0,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477]),(⟨1,1,1⟩,[0,r636,r637,r638,r639,r640,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650]),(⟨1,1,2⟩,[r177,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663,r664]),(⟨1,1,3⟩,[0,r665,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677]),(⟨1,1,4⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,-802816]),(⟨1,2,0⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨1,2,1⟩,[r177,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663,r664]),(⟨1,2,3⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨1,3,0⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨1,3,1⟩,[0,r665,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677]),(⟨1,3,2⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨1,3,3⟩,[0,r192,r689,r690,r691,r692,r693,r694,r695,r696,r697,r698]),(⟨1,3,4⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨1,3,6⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨1,4,0⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨1,4,1⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,-802816]),(⟨1,4,3⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨1,5,0⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,6,0⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨1,6,3⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨2,0,0⟩,[0,0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨2,0,1⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨2,0,2⟩,[r541,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨2,0,3⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨2,0,4⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨2,1,0⟩,[0,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨2,1,1⟩,[r177,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663,r664]),(⟨2,1,3⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨2,2,0⟩,[r541,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨2,3,0⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨2,3,1⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨2,3,3⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨2,4,0⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨3,0,0⟩,[0,0,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨3,0,1⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨3,0,2⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨3,0,3⟩,[0,r166,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨3,0,4⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨3,0,5⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨3,0,6⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨3,1,0⟩,[0,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨3,1,1⟩,[0,r665,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677]),(⟨3,1,2⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨3,1,3⟩,[0,r192,r689,r690,r691,r692,r693,r694,r695,r696,r697,r698]),(⟨3,1,4⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨3,1,6⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨3,2,0⟩,[0,r289,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨3,2,1⟩,[r568,r229,r678,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688]),(⟨3,2,3⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨3,3,0⟩,[0,r166,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨3,3,1⟩,[0,r192,r689,r690,r691,r692,r693,r694,r695,r696,r697,r698]),(⟨3,3,2⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨3,3,3⟩,[0,r399,r699,r700,r701,r702,r703,r704,r705,r706]),(⟨3,3,4⟩,[r192,r267,r268,r269,r270,r271,r272,r273,65536]),(⟨3,4,0⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨3,4,1⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨3,4,3⟩,[r192,r267,r268,r269,r270,r271,r272,r273,65536]),(⟨3,5,0⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨3,6,0⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨3,6,1⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨4,0,0⟩,[0,0,r428,r217,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨4,0,1⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨4,0,2⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨4,0,3⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨4,0,4⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨4,0,6⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨4,1,0⟩,[0,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨4,1,1⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,-802816]),(⟨4,1,3⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨4,2,0⟩,[r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,-401408]),(⟨4,3,0⟩,[0,r591,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨4,3,1⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨4,3,3⟩,[r192,r267,r268,r269,r270,r271,r272,r273,65536]),(⟨4,4,0⟩,[r166,r620,r621,r622,r623,r624,r625,r626,r627,r628,-229376]),(⟨4,6,0⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨5,0,0⟩,[0,0,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨5,0,1⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨5,0,3⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨5,1,0⟩,[0,r217,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨5,3,0⟩,[0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨6,0,0⟩,[0,0,r428,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461]),(⟨6,0,1⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨6,0,3⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨6,0,4⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨6,1,0⟩,[0,r205,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540]),(⟨6,1,3⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨6,3,0⟩,[0,r602,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨6,3,1⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768]),(⟨6,4,0⟩,[r289,r629,r630,r631,r632,r633,r634,r635,32768])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r707) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r707) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,0,-196608,7856128,-135454720,1333673984,-8370757632,35366445056,-102965231616,205398310912,-267821137920,197064663040,-35550814208,-47640985600,18595110912,1094639616]),(⟨3,0,1⟩,[0,65536,-2367488,37634048,-351772672,2177269760,-9448439808,29268344832,-63825002496,93325426688,-80563576832,22560129024,22151684096,-12719128576,-7442104320]),(⟨3,0,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,0,3⟩,[0,-65536,2088960,-28164096,216883200,-1104871424,4053909504,-10799185920,19505594368,-20679360512,8596643840,1519271936,1133174784]),(⟨3,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,0⟩,[0,65536,-2367488,37634048,-351772672,2177269760,-9448439808,29268344832,-63825002496,93325426688,-80563576832,22560129024,22151684096,-12719128576,-7442104320]),(⟨3,1,1⟩,[0,90112,-3293184,50364416,-423182336,2142494720,-6588235776,10760486912,-492863488,-38288285696,84413693952,-82980667392,24013029376,15046778880]),(⟨3,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,0⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,3,0⟩,[0,-65536,2088960,-28164096,216883200,-1104871424,4053909504,-10799185920,19505594368,-20679360512,8596643840,1519271936,1133174784]),(⟨3,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,3,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,0,-98304,4235264,-77783040,803381248,-5188444160,22010609664,-62477025280,117469888512,-137923215360,81798635520,2609553408,-23830388736,-1239146496]),(⟨4,0,1⟩,[0,57344,-2056192,30859264,-255090688,1279180800,-3947413504,6658637824,-1181073408,-21705433088,51697164288,-55797719040,20835082240,8024948736]),(⟨4,0,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,1,0⟩,[0,57344,-2056192,30859264,-255090688,1279180800,-3947413504,6658637824,-1181073408,-21705433088,51697164288,-55797719040,20835082240,8024948736]),(⟨4,1,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨4,2,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨5,0,0⟩,[0,0,196608,-7168000,108068864,-877633536,4204527616,-12272779264,21635792896,-20775518208,5284364288,7119773696,-3034644480,-177020928]),(⟨5,0,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,1,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨6,0,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨6,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,0,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[0,65536,-2269184,33398784,-273989632,1373888512,-4259995648,7257735168,-1347977216,-24144461824,57359638528,-59238506496,19542130688,11111260160,-6202957824]),(⟨1,0,4⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨1,0,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,0,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-65536,2400256,-38395904,356671488,-2155659264,8925700096,-25394946048,45683417088,-29355638784,-96212721664,342969016320,-539536613376,442642546688,-108369436672,-90184736768,43420704768]),(⟨1,1,1⟩,[0,-32768,1302528,-22208512,215760896,-1336033280,5544091648,-15426691072,26001244160,-10753671168,-70699704320,208695975936,-286559551488,189614702592,-8201969664,-49152811008]),(⟨1,1,2⟩,[0,65536,-2170880,30031872,-228179968,1055571968,-3063570432,5033852928,-905084928,-17119412224,42204667904,-46206074880,15145123840,13492928512,-7021830144]),(⟨1,1,3⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨1,1,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨1,2,0⟩,[0,-32768,1302528,-22208512,215760896,-1336033280,5544091648,-15426691072,26001244160,-10753671168,-70699704320,208695975936,-286559551488,189614702592,-8201969664,-49152811008]),(⟨1,2,1⟩,[8192,-245760,3121152,-22577152,105324544,-325730304,585998336,-59703296,-3071451136,9549889536,-13421649920,1282899968,31012380672,-58180878336,39790370816]),(⟨1,2,3⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,3,0⟩,[0,131072,-4440064,63430656,-502169600,2429460480,-7323566080,12291588096,-2253062144,-41263874048,99564306432,-105444581376,34687254528,24604188672,-13224787968]),(⟨1,3,1⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨1,3,2⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,3,3⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨1,4,1⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨1,4,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,5,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,6,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,0,-196608,7725056,-131964928,1295843328,-8158584832,34755141632,-102505512960,208066641920,-276866088960,205758832640,-25013755904,-80178184192,41089785856,5780676608,-5108318208]),(⟨2,0,1⟩,[0,0,-98304,4169728,-75833344,780492800,-5053587456,21622358016,-62270488576,119454941184,-143524347904,85385846784,11571388416,-42122551296,6431760384,5782683648]),(⟨2,0,2⟩,[0,0,196608,-7036928,105037824,-851943424,4113711104,-12220350464,22138421248,-22008905728,5572231168,9785122816,-6243500032,-806428672,826097664]),(⟨2,0,3⟩,[0,32768,-1187840,16867328,-115466240,326311936,509001728,-7030849536,24418992128,-44715556864,45084925952,-21382373376,-572809216,6414901248]),(⟨2,0,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,1,0⟩,[0,-32768,1204224,-18038784,139927552,-555540480,490504192,6195666944,-36269244416,108701270016,-214224052224,294081822720,-274988163072,147492151296,-1770209280,-43370127360]),(⟨2,1,1⟩,[8192,-221184,2318336,-11550720,20783104,81551360,-710516736,2533654528,-5130199040,4711079936,5796732928,-28799418368,50613936128,-55761592320,35109150720]),(⟨2,1,3⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,2,0⟩,[8192,-245760,3317760,-29614080,210362368,-1177673728,4699709440,-12280053760,19066970112,-12459016192,-7849418752,11068022784,24768880640,-58987307008,40616468480]),(⟨2,3,0⟩,[0,32768,-1187840,16867328,-115466240,326311936,509001728,-7030849536,24418992128,-44715556864,45084925952,-21382373376,-572809216,6414901248]),(⟨2,3,1⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,3,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,4,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨3,0,0⟩,[0,0,-294912,12025856,-211288064,2114166784,-13424345088,56988803072,-165235720192,324853252096,-411345485824,282450509824,-23979425792,-89763536896,25026871296,6877323264]),(⟨3,0,1⟩,[0,90112,-3170304,48660480,-436314112,2584551424,-10744954880,31861702656,-65883750400,88486617088,-61345193984,-7522189312,41753239552,-10299842560,-12123324416]),(⟨3,0,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,0,3⟩,[0,-131072,4128768,-53657600,379797504,-1656160256,4874502144,-10332831744,15599239168,-14637137920,5820907520,-121683968,2136293376]),(⟨3,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,0⟩,[0,155648,-5341184,78692352,-664494080,3640123392,-13808525312,36895555584,-66788835328,71367204864,-19140526080,-53728264192,56898363392,3193085952,-19145154560]),(⟨3,1,1⟩,[0,90112,-3293184,50364416,-423182336,2142494720,-6588235776,10760486912,-492863488,-38288285696,84413693952,-82980667392,24013029376,15046778880]),(⟨3,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,0⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,3,0⟩,[0,-131072,4128768,-53657600,379797504,-1656160256,4874502144,-10332831744,15599239168,-14637137920,5820907520,-121683968,2136293376]),(⟨3,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,3,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,0,98304,-2801664,27254784,-48562176,-1074733056,9790259200,-40338604032,95460982784,-132350984192,91583758336,-3633946624,-24636817408,-413048832]),(⟨4,0,1⟩,[0,57344,-2056192,30859264,-255090688,1279180800,-3947413504,6658637824,-1181073408,-21705433088,51697164288,-55797719040,20835082240,8024948736]),(⟨4,0,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,0,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,1,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨4,1,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,2,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,3,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,0⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨5,0,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,0,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨5,1,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,3,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨6,0,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨6,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,0,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,0,-196608,7856128,-135454720,1333673984,-8370757632,35366445056,-102965231616,205398310912,-267821137920,197064663040,-35550814208,-47640985600,18595110912,1094639616]),(⟨0,3,1⟩,[0,65536,-2367488,37634048,-351772672,2177269760,-9448439808,29268344832,-63825002496,93325426688,-80563576832,22560129024,22151684096,-12719128576,-7442104320]),(⟨0,3,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨0,3,3⟩,[0,-65536,2088960,-28164096,216883200,-1104871424,4053909504,-10799185920,19505594368,-20679360512,8596643840,1519271936,1133174784]),(⟨0,3,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,4,0⟩,[0,0,-98304,4235264,-77783040,803381248,-5188444160,22010609664,-62477025280,117469888512,-137923215360,81798635520,2609553408,-23830388736,-1239146496]),(⟨0,4,1⟩,[0,57344,-2056192,30859264,-255090688,1279180800,-3947413504,6658637824,-1181073408,-21705433088,51697164288,-55797719040,20835082240,8024948736]),(⟨0,4,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨0,5,0⟩,[0,0,196608,-7168000,108068864,-877633536,4204527616,-12272779264,21635792896,-20775518208,5284364288,7119773696,-3034644480,-177020928]),(⟨0,5,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,6,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨0,6,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,6,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨0,6,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,0,0⟩,[0,0,196608,-8118272,148725760,-1608302592,11517730816,-57961652224,211384418304,-564643135488,1094534316032,-1482528858112,1266578350080,-458415980544,-223684321280,253645791232,-17151131648,-23352311808]),(⟨1,0,1⟩,[0,-65536,2498560,-42762240,441499648,-3114131456,15985033216,-61311016960,175707021312,-367380185088,527012110336,-434191155200,30661902336,329405407232,-264734310400,-11452571648,69855830016]),(⟨1,0,2⟩,[0,-32768,1105920,-14778368,95338496,-230072320,-871849984,9342492672,-38835159040,102473744384,-192378560512,266129424384,-261918375936,151526301696,-4841381888,-45376364544]),(⟨1,0,3⟩,[0,131072,-4489216,66166784,-560398336,3088556032,-11859476480,32585760768,-62969020416,79325708288,-50307399680,-9767018496,31167610880,2280398848,-15999320064]),(⟨1,0,4⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨1,0,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,0,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-65536,2498560,-42762240,441499648,-3114131456,15985033216,-61311016960,175707021312,-367380185088,527012110336,-434191155200,30661902336,329405407232,-264734310400,-11452571648,69855830016]),(⟨1,1,1⟩,[0,-90112,3457024,-57212928,543096832,-3310362624,13623148544,-37865832448,64404848640,-29377929216,-167647756288,511908806656,-724445102080,504589524992,-45278019584,-119705485312]),(⟨1,1,2⟩,[8192,-180224,950272,7454720,-122855424,729841664,-2477572096,4974149632,-3976536064,-7569522688,28783017984,-44923174912,46157504512,-44687949824,32768540672]),(⟨1,1,3⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨1,1,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨1,2,0⟩,[0,-32768,1105920,-14778368,95338496,-230072320,-871849984,9342492672,-38835159040,102473744384,-192378560512,266129424384,-261918375936,151526301696,-4841381888,-45376364544]),(⟨1,2,1⟩,[8192,-180224,950272,7454720,-122855424,729841664,-2477572096,4974149632,-3976536064,-7569522688,28783017984,-44923174912,46157504512,-44687949824,32768540672]),(⟨1,2,3⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,3,0⟩,[0,131072,-4587520,70402048,-638181376,3891937280,-17047920640,54596370432,-125446045696,196795596800,-188230615040,72031617024,33777164288,-21549989888,-17238466560]),(⟨1,3,1⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨1,3,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨1,3,3⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨1,3,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨1,4,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,4,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,5,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,6,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,0,-98304,3358720,-47136768,337371136,-1099251712,-1160929280,27518091264,-129957904384,346358743040,-571401338880,545184759808,-193415323648,-115275087872,84512841728,21326807040]),(⟨2,0,1⟩,[0,-57344,2056192,-30834688,251502592,-1193836544,3025469440,-816783360,-23866884096,100830683136,-240472399872,388598677504,-426314162176,272852271104,-30644289536,-64769990656]),(⟨2,0,2⟩,[8192,-245760,3317760,-29614080,210362368,-1177673728,4699709440,-12280053760,19066970112,-12459016192,-7849418752,11068022784,24768880640,-58987307008,40616468480]),(⟨2,0,3⟩,[0,32768,-1187840,16867328,-115466240,326311936,509001728,-7030849536,24418992128,-44715556864,45084925952,-21382373376,-572809216,6414901248]),(⟨2,0,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,1,0⟩,[0,-57344,2056192,-30834688,251502592,-1193836544,3025469440,-816783360,-23866884096,100830683136,-240472399872,388598677504,-426314162176,272852271104,-30644289536,-64769990656]),(⟨2,1,1⟩,[16384,-466944,5439488,-34127872,126107648,-244178944,-124518400,2473951232,-8201650176,14260969472,-7624916992,-27516518400,81626316800,-113942470656,74899521536]),(⟨2,1,3⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,2,0⟩,[8192,-245760,3317760,-29614080,210362368,-1177673728,4699709440,-12280053760,19066970112,-12459016192,-7849418752,11068022784,24768880640,-58987307008,40616468480]),(⟨2,3,0⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨2,3,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,3,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,4,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨3,0,0⟩,[0,0,-491520,19456000,-331710464,3220127744,-19840286720,81757986816,-230072123392,438080667648,-533024342016,339883958272,661749760,-127851937792,28387459072,10653769728]),(⟨3,0,1⟩,[0,155648,-5341184,78692352,-664494080,3640123392,-13808525312,36895555584,-66788835328,71367204864,-19140526080,-53728264192,56898363392,3193085952,-19145154560]),(⟨3,0,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,0,3⟩,[0,-131072,4128768,-53657600,379797504,-1656160256,4874502144,-10332831744,15599239168,-14637137920,5820907520,-121683968,2136293376]),(⟨3,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,0⟩,[0,155648,-5341184,78692352,-664494080,3640123392,-13808525312,36895555584,-66788835328,71367204864,-19140526080,-53728264192,56898363392,3193085952,-19145154560]),(⟨3,1,1⟩,[0,90112,-3293184,50364416,-423182336,2142494720,-6588235776,10760486912,-492863488,-38288285696,84413693952,-82980667392,24013029376,15046778880]),(⟨3,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,0⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,3,0⟩,[0,-131072,4177920,-56328192,433766400,-2209742848,8107819008,-21598371840,39011188736,-41358721024,17193287680,3038543872,2266349568]),(⟨3,3,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨3,3,3⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨3,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨4,0,1⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,0,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,0,3⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,0,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,1,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨4,1,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,2,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,3,0⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,3,1⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,0⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨5,0,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,0,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨5,1,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,3,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨6,0,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨6,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,0,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,0,196608,-8118272,148725760,-1608302592,11517730816,-57961652224,211384418304,-564643135488,1094534316032,-1482528858112,1266578350080,-458415980544,-223684321280,253645791232,-17151131648,-23352311808]),(⟨0,1,1⟩,[0,-65536,2498560,-42762240,441499648,-3114131456,15985033216,-61311016960,175707021312,-367380185088,527012110336,-434191155200,30661902336,329405407232,-264734310400,-11452571648,69855830016]),(⟨0,1,2⟩,[0,-32768,1105920,-14778368,95338496,-230072320,-871849984,9342492672,-38835159040,102473744384,-192378560512,266129424384,-261918375936,151526301696,-4841381888,-45376364544]),(⟨0,1,3⟩,[0,131072,-4489216,66166784,-560398336,3088556032,-11859476480,32585760768,-62969020416,79325708288,-50307399680,-9767018496,31167610880,2280398848,-15999320064]),(⟨0,1,4⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨0,1,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,1,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,2,0⟩,[0,0,-98304,3358720,-47136768,337371136,-1099251712,-1160929280,27518091264,-129957904384,346358743040,-571401338880,545184759808,-193415323648,-115275087872,84512841728,21326807040]),(⟨0,2,1⟩,[0,-57344,2056192,-30834688,251502592,-1193836544,3025469440,-816783360,-23866884096,100830683136,-240472399872,388598677504,-426314162176,272852271104,-30644289536,-64769990656]),(⟨0,2,2⟩,[8192,-245760,3317760,-29614080,210362368,-1177673728,4699709440,-12280053760,19066970112,-12459016192,-7849418752,11068022784,24768880640,-58987307008,40616468480]),(⟨0,2,3⟩,[0,32768,-1187840,16867328,-115466240,326311936,509001728,-7030849536,24418992128,-44715556864,45084925952,-21382373376,-572809216,6414901248]),(⟨0,2,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨0,3,0⟩,[0,0,-491520,19456000,-331710464,3220127744,-19840286720,81757986816,-230072123392,438080667648,-533024342016,339883958272,661749760,-127851937792,28387459072,10653769728]),(⟨0,3,1⟩,[0,155648,-5341184,78692352,-664494080,3640123392,-13808525312,36895555584,-66788835328,71367204864,-19140526080,-53728264192,56898363392,3193085952,-19145154560]),(⟨0,3,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨0,3,3⟩,[0,-131072,4128768,-53657600,379797504,-1656160256,4874502144,-10332831744,15599239168,-14637137920,5820907520,-121683968,2136293376]),(⟨0,3,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,4,0⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨0,4,1⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨0,4,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨0,4,3⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨0,4,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨0,4,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨0,5,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,5,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨0,6,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨0,6,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,6,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨0,6,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,0,0⟩,[0,0,196608,-8118272,148725760,-1608302592,11517730816,-57961652224,211384418304,-564643135488,1094534316032,-1482528858112,1266578350080,-458415980544,-223684321280,253645791232,-17151131648,-23352311808]),(⟨1,0,1⟩,[0,-65536,2498560,-42762240,441499648,-3114131456,15985033216,-61311016960,175707021312,-367380185088,527012110336,-434191155200,30661902336,329405407232,-264734310400,-11452571648,69855830016]),(⟨1,0,2⟩,[0,-32768,1105920,-14778368,95338496,-230072320,-871849984,9342492672,-38835159040,102473744384,-192378560512,266129424384,-261918375936,151526301696,-4841381888,-45376364544]),(⟨1,0,3⟩,[0,131072,-4489216,66166784,-560398336,3088556032,-11859476480,32585760768,-62969020416,79325708288,-50307399680,-9767018496,31167610880,2280398848,-15999320064]),(⟨1,0,4⟩,[0,49152,-2072576,35020800,-315400192,1681268736,-5452677120,9835954176,-3423092736,-29042540544,75496742912,-83525836800,30182268928,12180725760]),(⟨1,0,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,0,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-65536,2596864,-47128576,526327808,-4072603648,23044366336,-97227087872,305730625536,-705404731392,1150236942336,-1211351326720,600860418048,216168267776,-421099184128,67279593472,96290955264]),(⟨1,1,1⟩,[0,-147456,5611520,-92217344,870432768,-5284691968,21702205440,-60304973824,102808453120,-48002187264,-264595808256,815121637376,-1162330652672,819564347392,-82354069504,-190258159616]),(⟨1,1,2⟩,[16384,-425984,4071424,-15122432,-17530880,404111360,-1891573760,4914446336,-7047987200,1980366848,15361368064,-43640274944,77169885184,-102868828160,72558911488]),(⟨1,1,3⟩,[0,81920,-3309568,54525952,-483491840,2544582656,-8093499392,13937803264,-2734882816,-45625393152,108213272576,-110708785152,33360216064,19202555904]),(⟨1,1,4⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,2,0⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨1,2,1⟩,[16384,-401408,3268608,-4096000,-102072320,811393024,-3188088832,7507804160,-9106735104,-2858442752,34579750912,-73722593280,96771440640,-100449542144,67877691392]),(⟨1,2,3⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨1,3,0⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨1,3,1⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨1,3,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨1,3,3⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨1,3,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨1,4,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,4,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,5,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,6,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,0,-98304,3358720,-47136768,337371136,-1099251712,-1160929280,27518091264,-129957904384,346358743040,-571401338880,545184759808,-193415323648,-115275087872,84512841728,21326807040]),(⟨2,0,1⟩,[0,-57344,2056192,-30834688,251502592,-1193836544,3025469440,-816783360,-23866884096,100830683136,-240472399872,388598677504,-426314162176,272852271104,-30644289536,-64769990656]),(⟨2,0,2⟩,[8192,-245760,3317760,-29614080,210362368,-1177673728,4699709440,-12280053760,19066970112,-12459016192,-7849418752,11068022784,24768880640,-58987307008,40616468480]),(⟨2,0,3⟩,[0,32768,-1187840,16867328,-115466240,326311936,509001728,-7030849536,24418992128,-44715556864,45084925952,-21382373376,-572809216,6414901248]),(⟨2,0,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,1,0⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨2,1,1⟩,[16384,-401408,3268608,-4096000,-102072320,811393024,-3188088832,7507804160,-9106735104,-2858442752,34579750912,-73722593280,96771440640,-100449542144,67877691392]),(⟨2,1,3⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,2,0⟩,[8192,-245760,3514368,-36651008,315400192,-2029617152,8813420544,-24500404224,41205391360,-34467921920,-2277187584,20853145600,18525380608,-59793735680,41442566144]),(⟨2,3,0⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨2,3,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,3,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,4,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨3,0,0⟩,[0,0,-491520,19456000,-331710464,3220127744,-19840286720,81757986816,-230072123392,438080667648,-533024342016,339883958272,661749760,-127851937792,28387459072,10653769728]),(⟨3,0,1⟩,[0,155648,-5341184,78692352,-664494080,3640123392,-13808525312,36895555584,-66788835328,71367204864,-19140526080,-53728264192,56898363392,3193085952,-19145154560]),(⟨3,0,2⟩,[0,32768,-1040384,12337152,-60022784,-14319616,1563705344,-8170930176,22324002816,-37358370816,38000893952,-20063174656,143302656,6844809216]),(⟨3,0,3⟩,[0,-131072,4128768,-53657600,379797504,-1656160256,4874502144,-10332831744,15599239168,-14637137920,5820907520,-121683968,2136293376]),(⟨3,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,0⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨3,1,1⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨3,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,1,3⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨3,1,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨3,1,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨3,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,2,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,3,0⟩,[0,-131072,4177920,-56328192,433766400,-2209742848,8107819008,-21598371840,39011188736,-41358721024,17193287680,3038543872,2266349568]),(⟨3,3,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨3,3,3⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨3,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,0⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨3,4,1⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨3,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,6,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨4,0,1⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,0,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,0,3⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,0,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,1,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨4,1,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,2,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,3,0⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,3,1⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,0⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨5,0,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,0,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨5,1,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,3,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨6,0,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨6,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,0,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,196608,-8577024,167231488,-1934499840,14867136512,-80482951168,316724781056,-917938380800,1950993817600,-2959777636352,2982272303104,-1591951187968,-125983866880,697020833792,-262179545088,-50640084992,32474308608]),(⟨0,0,1⟩,[0,0,294912,-12713984,243523584,-2753609728,20584235008,-107747598336,406781829120,-1119053455360,2224059809792,-3080605384704,2696207343616,-1023621267456,-454964314112,557803872256,-42313392128,-60113657856]),(⟨0,0,2⟩,[0,0,-294912,11247616,-184459264,1705017344,-9765126144,35594919936,-79040471040,79666282496,80946102272,-392822562816,547086049280,-284401958912,-75078893568,91885903872,16075186176]),(⟨0,0,3⟩,[0,0,-540672,22306816,-396214272,4008312832,-25756467200,110830116864,-326367936512,652999852032,-843748032512,596657643520,-67707256832,-176909254656,50581078016,14512103424]),(⟨0,0,4⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨0,0,5⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨0,0,6⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨0,1,0⟩,[0,0,294912,-12713984,243523584,-2753609728,20584235008,-107747598336,406781829120,-1119053455360,2224059809792,-3080605384704,2696207343616,-1023621267456,-454964314112,557803872256,-42313392128,-60113657856]),(⟨0,1,1⟩,[0,-90112,3506176,-61857792,665518080,-4936015872,26770440192,-108564815872,328797945856,-728680603648,1124732010496,-1061269544960,308490665984,520567824384,-554420830208,39169794048,126050140160]),(⟨0,1,2⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨0,1,3⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨0,1,4⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨0,1,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,1,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,2,0⟩,[0,0,-294912,11247616,-184459264,1705017344,-9765126144,35594919936,-79040471040,79666282496,80946102272,-392822562816,547086049280,-284401958912,-75078893568,91885903872,16075186176]),(⟨0,2,1⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨0,2,2⟩,[8192,-245760,3514368,-36651008,315400192,-2029617152,8813420544,-24500404224,41205391360,-34467921920,-2277187584,20853145600,18525380608,-59793735680,41442566144]),(⟨0,2,3⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨0,2,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨0,3,0⟩,[0,0,-540672,22306816,-396214272,4008312832,-25756467200,110830116864,-326367936512,652999852032,-843748032512,596657643520,-67707256832,-176909254656,50581078016,14512103424]),(⟨0,3,1⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨0,3,2⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨0,3,3⟩,[0,-32768,933888,-12156928,114835456,-922550272,5488803840,-20987445248,47996895232,-59713945600,29487087616,3945037824,-162971648]),(⟨0,3,4⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨0,3,5⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨0,3,6⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨0,4,0⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨0,4,1⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨0,4,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨0,4,3⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨0,4,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨0,4,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨0,5,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,5,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨0,6,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨0,6,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,6,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨0,6,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,0,0⟩,[0,0,294912,-12713984,243523584,-2753609728,20584235008,-107747598336,406781829120,-1119053455360,2224059809792,-3080605384704,2696207343616,-1023621267456,-454964314112,557803872256,-42313392128,-60113657856]),(⟨1,0,1⟩,[0,-90112,3506176,-61857792,665518080,-4936015872,26770440192,-108564815872,328797945856,-728680603648,1124732010496,-1061269544960,308490665984,520567824384,-554420830208,39169794048,126050140160]),(⟨1,0,2⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨1,0,3⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨1,0,4⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨1,0,5⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,0,6⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-90112,3506176,-61857792,665518080,-4936015872,26770440192,-108564815872,328797945856,-728680603648,1124732010496,-1061269544960,308490665984,520567824384,-554420830208,39169794048,126050140160]),(⟨1,1,1⟩,[0,-172032,6463488,-105013248,982007808,-5922988032,24237170688,-67317424128,115210813440,-55872774144,-290844155904,909638492160,-1313656651776,944924467200,-111228149760,-211658022912]),(⟨1,1,2⟩,[16384,-401408,3268608,-4096000,-102072320,811393024,-3188088832,7507804160,-9106735104,-2858442752,34579750912,-73722593280,96771440640,-100449542144,67877691392]),(⟨1,1,3⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨1,1,4⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,2,0⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨1,2,1⟩,[16384,-401408,3268608,-4096000,-102072320,811393024,-3188088832,7507804160,-9106735104,-2858442752,34579750912,-73722593280,96771440640,-100449542144,67877691392]),(⟨1,2,3⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨1,3,0⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨1,3,1⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨1,3,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨1,3,3⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨1,3,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨1,4,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,4,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨1,5,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,6,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,0,-294912,11247616,-184459264,1705017344,-9765126144,35594919936,-79040471040,79666282496,80946102272,-392822562816,547086049280,-284401958912,-75078893568,91885903872,16075186176]),(⟨2,0,1⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨2,0,2⟩,[8192,-245760,3514368,-36651008,315400192,-2029617152,8813420544,-24500404224,41205391360,-34467921920,-2277187584,20853145600,18525380608,-59793735680,41442566144]),(⟨2,0,3⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨2,0,4⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨2,1,0⟩,[0,-57344,1859584,-23404544,131080192,-87875584,-3390472192,23952400384,-88703287296,214058098688,-362151256064,446032125952,-401672986624,234763870208,-27283701760,-60993544192]),(⟨2,1,1⟩,[16384,-401408,3268608,-4096000,-102072320,811393024,-3188088832,7507804160,-9106735104,-2858442752,34579750912,-73722593280,96771440640,-100449542144,67877691392]),(⟨2,1,3⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,2,0⟩,[8192,-245760,3514368,-36651008,315400192,-2029617152,8813420544,-24500404224,41205391360,-34467921920,-2277187584,20853145600,18525380608,-59793735680,41442566144]),(⟨2,3,0⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨2,3,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,3,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,4,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨3,0,0⟩,[0,0,-540672,22306816,-396214272,4008312832,-25756467200,110830116864,-326367936512,652999852032,-843748032512,596657643520,-67707256832,-176909254656,50581078016,14512103424]),(⟨3,0,1⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨3,0,2⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨3,0,3⟩,[0,-32768,933888,-12156928,114835456,-922550272,5488803840,-20987445248,47996895232,-59713945600,29487087616,3945037824,-162971648]),(⟨3,0,4⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨3,0,5⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,0,6⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,1,0⟩,[0,155648,-5390336,81428480,-722722816,4299218944,-18344435712,57189728256,-127504793600,191956787200,-169012232192,41949298688,53378719744,-19130703872,-21919686656]),(⟨3,1,1⟩,[0,106496,-4128768,65880064,-570490880,2960449536,-9400090624,16494592000,-4604166144,-50747973632,127193907200,-139323555840,51017351168,20205674496]),(⟨3,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,1,3⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨3,1,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨3,1,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,32768,-991232,9699328,-7397376,-551321600,4713529344,-19303628800,46054785024,-65491075072,50369290240,-14262599680,-3607453696,6237880320]),(⟨3,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨3,2,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,3,0⟩,[0,-32768,933888,-12156928,114835456,-922550272,5488803840,-20987445248,47996895232,-59713945600,29487087616,3945037824,-162971648]),(⟨3,3,1⟩,[0,65536,-1409024,9764864,-11665408,-154271744,753336320,-1132068864,-920780800,5025890304,-4781342720,272957440]),(⟨3,3,2⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,3,3⟩,[0,-294912,8650752,-96337920,494665728,-1020985344,-430178304,4546756608,-4464574464,-245661696]),(⟨3,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,0⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨3,4,1⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨3,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,6,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,0,49152,-65536,-30973952,610533376,-5610643456,30084431872,-101054562304,216050565120,-282222690304,187261321216,-7153590272,-46960607232,-3187580928]),(⟨4,0,1⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,0,2⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,0,3⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,0,4⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,73728,-2891776,46374912,-402399232,2097135616,-6759268352,12392742912,-5292376064,-34165121024,94477377536,-112140607488,47839404032,13183844352]),(⟨4,1,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨4,1,3⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,2,0⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨4,3,0⟩,[0,81920,-2211840,23560192,-125763584,338919424,-273448960,-903872512,2611806208,-1965998080,-713015296,1009942528]),(⟨4,3,1⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,0⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨4,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,0,245760,-9805824,160694272,-1414635520,7354351616,-23405477888,45366575104,-48908222464,17652760576,12920348672,-6785400832,-783949824]),(⟨5,0,1⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,0,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨5,1,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨5,3,0⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨6,0,0⟩,[0,0,49152,-2670592,53968896,-553582592,3233316864,-11265540096,23411949568,-26721583104,11372380160,3160227840,130056192]),(⟨6,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,0,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨6,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨6,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648])]


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
    (Poly.add (Poly.scale (K.ofRat r708) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 9).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r707*r707 : ℚ)=r708 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 9 r707 r707 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=9 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 9).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C100

#print axioms Coulomb8.Columns.C100.sound
