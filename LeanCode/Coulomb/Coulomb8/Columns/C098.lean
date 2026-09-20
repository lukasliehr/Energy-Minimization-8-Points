import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C098

def r0 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 3883008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -67076096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 666206208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -4181934080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 16854679552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -39351042048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 15592341504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 254632689664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -1069407059968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 2403852484608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -3424486293504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 3005547266048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -185423593472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -69514379264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 35728244736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1035304960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 5816320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -99680256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 977616896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -862355456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 23826251776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -3179823104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 2696495104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 338876612608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -193367261184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 2874220904448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -540243705856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 2900931182592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -869194579968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -42409705472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 3551477760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -4849664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 65126400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -63864832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 1480359936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -166625280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -18474467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 75552063488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -8133984256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 56947703808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 297846030336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -700721627136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 639505006592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1210810368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1776910336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -10698752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 161316864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -187334656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 6125322240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -2131968000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 2169700352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 6712131584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -417189167104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 792118378496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -855532666880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 59715715072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 4878761984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -1123631104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -868352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 26099712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -319045632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 2012856320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -6544588800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 6374981632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 30518902784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -139695521792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 277016199168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -288899252224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 16304783360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 506904576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 4882432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -62865408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 390070272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -1077968896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -7929856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 9623535616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -4345954304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 48684515328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -35849601024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -18989056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 95551488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -3751936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 3670016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -559251456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 122159104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 4607213568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -15685124096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 25219186688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -145489920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -19906560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -1163264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 2703360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -190447616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1323630592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -6510559232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 21750431744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -41440608256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -498368512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 293841125376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -983089856512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 1786294370304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -267292114944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 121449267200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 272285696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -6115393536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 4292608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -8159232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -121962496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 908460032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -2097463296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -3195994112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 34072576000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -6292045824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 200516304896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -262946193408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 286413455360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -41313239040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 3754115072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 2015232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -26509312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 200802304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -984055808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 3103670272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -663420928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -163053568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 9074900992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -172426444800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 261911314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -200182333440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 3171647488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 931512320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 1130496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -15400960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 15417344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -414580736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 738492416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 655622144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -6998884352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 16090234880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -11606278144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -3469934592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 1526448128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -79364096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 8093696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -31031296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 2621440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -54329344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 857931776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1220444160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -4834394112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 723156992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 6045696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -4194304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 1867776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 243793920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -998866944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 1250951168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 1133723648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -812646400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 6635520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 7864320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -93257728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 545193984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -1495203840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 358875136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 10209591296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -34939994112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 60246851584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -49112416256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1659699200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1245642752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -952827904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -6356992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 37945344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -133513216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 8650752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -224657408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 4807852032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -12546129920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 30569922560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -50012028928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 6457458688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -490192896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 54329344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -320077824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 997392384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -177471488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1808793600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 508821504, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -9587752960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -347340800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 9895936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -31064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -49217536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -87687168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 1491468288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -246939648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 425984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 458752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -655360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 9699328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -340328448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -143392768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 1515585536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -212598784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 13828096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -39878656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -108396544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1169620992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -4203347968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 9578938368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -16640573440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 22853812224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -2541682688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 1409024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -20316160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 109543424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -129695744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -74285056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 1489633280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -16465920, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -396328960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 3194880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -1818624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 28360704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -249200640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 1386135552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -5075386368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 11481956352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -9001697280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -37537431552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 156940615680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -261732679680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 88614469632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 4159291392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -19809681408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 750403584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -6553600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 17530880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 52854784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -487555072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 201326592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -1255997440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -287277056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 17764777984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -21461467136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -876969984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 1405190144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -96567296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 164560896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -619233280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 953155584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 37486592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -12425494528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 3568582656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -11365646336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -7249395712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 2433155072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -110903296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 4849664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 330563584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 6815744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -323747840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 5011144704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -179961856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -13893632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 3375104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 23298048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -44892160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 1309343744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -2165899264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -950861824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 9870409728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -14422147072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 375816192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 9011200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -1212416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 2359296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -82640896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -1703936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 80936960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -1252786176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 44990464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 3473408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -4882432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 21495808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -101777408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 429654016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -864616448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 2897313792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -798621696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 5472256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -98435072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -175374336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 2982936576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -493879296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 851968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1310720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 19398656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -680656896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -286785536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 3031171072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -425197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -127401984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -39714816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 986185728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -1148977152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -14155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 1941504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -33538048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 333103104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -2090967040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 8427339776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -19675521024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 7796170752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 127316344832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -534703529984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 1201926242304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -1712243146752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 1502773633024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -92711796736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -34757189632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 17864122368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -517652480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 2908160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -49840128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 488808448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -431177728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 11913125888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -1589911552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 1348247552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 169438306304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -96683630592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 1437110452224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -270121852928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 1450465591296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -434597289984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -21204852736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 1775738880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -2424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 32563200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -31932416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 740179968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -83312640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -9237233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 37776031744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -4066992128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 28473851904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 148923015168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -350360813568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 319752503296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -605405184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -888455168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -5349376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 80658432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -93667328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 3062661120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -1065984000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 1084850176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 3356065792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -208594583552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 396059189248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -427766333440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 29857857536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 2439380992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -561815552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -434176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 13049856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -159522816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 1006428160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -3272294400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 3187490816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 15259451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -69847760896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 138508099584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -144449626112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 8152391680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 253452288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 2441216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -31432704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 195035136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -538984448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -3964928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 4811767808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -2172977152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 24342257664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -17924800512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -9494528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 47775744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -1875968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 1835008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -279625728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 61079552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 2303606784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -7842562048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 12609593344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -72744960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -9953280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -581632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 1351680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -95223808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 661815296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -3255279616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 10875215872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -20720304128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -249184256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 146920562688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -491544928256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 893147185152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -133646057472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 60724633600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 136142848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -3057696768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -4079616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -60981248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 454230016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -1048731648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -1597997056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 17036288000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -3146022912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 100258152448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -131473096704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 143206727680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -20656619520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 1877057536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 1007616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -13254656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 100401152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -492027904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 1551835136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -331710464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -81526784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 4537450496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -86213222400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 130955657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -100091166720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 1585823744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 465756160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 565248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -7700480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 7708672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -207290368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 369246208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 327811072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -3499442176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 8045117440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -5803139072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -1734967296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 763224064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -39682048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 4046848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -15515648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 2916352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 1310720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -27164672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 428965888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 610222080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -2417197056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 361578496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -442368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 3022848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 933888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 121896960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -499433472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 625475584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 566861824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -406323200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 3317760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -46628864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 272596992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -747601920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 179437568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 5104795648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -17469997056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 30123425792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -24556208128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -829849600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 622821376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -476413952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -3178496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 18972672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -66756608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 4325376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -112328704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 2403926016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -6273064960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 15284961280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -25006014464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 3228729344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -245096448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 27164672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -160038912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 498696192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -88735744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -904396800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 254410752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -4793876480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -173670400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 4947968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 1409024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -15532032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -24608768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -43843584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 745734144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -123469824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 212992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 229376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -327680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 4849664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -170164224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -71696384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 757792768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -106299392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 6914048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -19939328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -54198272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 584810496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -2101673984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 4789469184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -8320286720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 11426906112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -1270841344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 704512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 188416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -10158080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 54771712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -64847872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -37142528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 744816640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -8232960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -198164480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 1597440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 196608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -10616832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -3309568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 82182144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -95748096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -1179648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -909312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 14180352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -124600320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 693067776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -2537693184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 5740978176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -4500848640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -18768715776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 78470307840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -130866339840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 44307234816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 2079645696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -9904840704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 375201792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -3276800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 8765440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 26427392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -243777536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 100663296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -627998720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -143638528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 8882388992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -10730733568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -438484992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 702595072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -48283648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := -98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 82280448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -309616640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 476577792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 18743296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := -6212747264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 1784291328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -5682823168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -3624697856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 1216577536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -55451648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := 2424832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 165281792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := 3407872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := -161873920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 2505572352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -89980928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -6946816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 1687552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := 11649024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := -22446080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 654671872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := -1082949632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -475430912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 4935204864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := -7211073536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 187908096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 4505600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -606208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 1179648, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := -41320448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := -851968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 40468480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -626393088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := 22495232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := 1736704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -2441216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 10747904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := -50888704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := 214827008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := -432308224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := 1448656896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := -399310848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := 2736128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -63700992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := -19857408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 493092864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -574488576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := -7077888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[0,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[0,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[0,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[0,0,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[0,r17,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[0,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95],[],[],[],[],[],[],[r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111],[r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140],[r141,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153],[r96,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164],[r112,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174],[],[],[],[],[],[0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187],[r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200],[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211],[0,r0,r212,r213,r214,r215,r216,r217,r218,r219,r220],[0,r0,r221,r222,r223,r224,r225,r226,r227,r228],[],[],[],[],[r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240],[r188,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250],[0,r0,r221,r222,r223,r224,r225,r226,r227,r228],[r96,r251,r252,r253,r254,r255,r256,r257,32768],[],[],[],[],[r96,r251,r252,r253,r254,r255,r256,r257,32768],[],[],[],[],[],[],[],[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272],[r141,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285],[r85,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297],[0,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,917504],[],[],[],[],[],[],[],[r96,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318],[r141,r319,r320,r321,r322,r323,r324,r325,r326,r327,-229376],[],[r96,r251,r252,r253,r254,r255,r256,r257,32768],[],[],[],[r141,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337],[],[r96,r251,r252,r253,r254,r255,r256,r257,32768],[],[],[],[],[],[],[],[],[],[],[0,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347],[],[],[],[],[],[0,r338,r348,r349,r350,r351,r352,r353,r354,r355],[r96,r251,r252,r253,r254,r255,r256,r257,32768],[],[],[],[],[],[],[],[r356,r202,r321,r357,r358,r359,r360,r361,196608],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r85,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377]),(⟨0,0,1⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,0,2⟩,[0,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨0,0,3⟩,[0,r33,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,0,4⟩,[0,0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433]),(⟨0,0,5⟩,[0,r378,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,0,6⟩,[0,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,1,0⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,1,1⟩,[r112,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨0,1,2⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,1,3⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,1,4⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨0,1,5⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,1,6⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,2,0⟩,[0,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨0,2,1⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,2,2⟩,[0,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨0,2,3⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨0,2,4⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨0,2,5⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨0,2,6⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,3,0⟩,[0,r33,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,3,1⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,3,2⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨0,3,3⟩,[r96,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595]),(⟨0,3,4⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨0,3,5⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,3,6⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨0,4,0⟩,[0,0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433]),(⟨0,4,1⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨0,4,2⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨0,4,3⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨0,4,5⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨0,5,0⟩,[0,r378,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,5,1⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,5,2⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨0,5,3⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,5,4⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨0,6,0⟩,[0,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,6,1⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,6,2⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,6,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨1,0,0⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨1,0,1⟩,[r112,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨1,0,2⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,0,3⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,0,4⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨1,0,5⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,0,6⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,1,0⟩,[r112,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨1,1,1⟩,[r613,r614,r615,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨1,1,2⟩,[r188,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨1,1,3⟩,[r445,r319,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651]),(⟨1,1,4⟩,[0,r229,r652,r653,r654,r655,r656,r657,r658,r659,r660,458752]),(⟨1,2,0⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,2,1⟩,[r188,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨1,2,3⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨1,2,4⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨1,2,6⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨1,3,0⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,3,1⟩,[r445,r319,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651]),(⟨1,3,2⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨1,3,3⟩,[r188,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨1,3,5⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨1,4,0⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨1,4,1⟩,[0,r229,r652,r653,r654,r655,r656,r657,r658,r659,r660,458752]),(⟨1,4,2⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨1,5,0⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,5,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨1,6,0⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,6,2⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨2,0,0⟩,[0,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨2,0,1⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,0,2⟩,[0,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,0,3⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨2,0,4⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨2,0,5⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨2,0,6⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨2,1,0⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,1,1⟩,[r188,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨2,1,3⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,1,4⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨2,1,6⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨2,2,0⟩,[0,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,2,3⟩,[0,r0,r212,r213,r214,r215,r216,r217,r218,r219,r220]),(⟨2,3,0⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨2,3,1⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,3,2⟩,[0,r0,r212,r213,r214,r215,r216,r217,r218,r219,r220]),(⟨2,3,3⟩,[0,r0,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨2,3,4⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨2,4,0⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨2,4,1⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨2,4,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨2,5,0⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨2,6,0⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨2,6,1⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,0,0⟩,[0,r33,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨3,0,1⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,0,2⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨3,0,3⟩,[r96,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595]),(⟨3,0,4⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨3,0,5⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,0,6⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,1,0⟩,[r141,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,1,1⟩,[r445,r319,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651]),(⟨3,1,2⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨3,1,3⟩,[r188,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨3,1,5⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,2,0⟩,[r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨3,2,1⟩,[r112,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨3,2,2⟩,[0,r0,r212,r213,r214,r215,r216,r217,r218,r219,r220]),(⟨3,2,3⟩,[0,r0,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨3,2,4⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,3,0⟩,[r96,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595]),(⟨3,3,1⟩,[r188,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨3,3,2⟩,[0,r0,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨3,3,3⟩,[r691,r558,r674,r692,r693,r694,r695,r696,98304]),(⟨3,4,0⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨3,4,2⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,5,0⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,5,1⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨3,6,0⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨4,0,0⟩,[0,0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433]),(⟨4,0,1⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨4,0,2⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨4,0,3⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨4,0,5⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨4,1,0⟩,[r188,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨4,1,1⟩,[0,r229,r652,r653,r654,r655,r656,r657,r658,r659,r660,458752]),(⟨4,1,2⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨4,2,0⟩,[0,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨4,2,1⟩,[r188,r672,r673,r674,r675,r676,r677,r678,r679,r680,-114688]),(⟨4,2,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨4,3,0⟩,[r544,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605]),(⟨4,3,2⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨4,5,0⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨5,0,0⟩,[0,r378,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨5,0,1⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨5,0,2⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨5,0,3⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨5,0,4⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨5,1,0⟩,[r112,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨5,1,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨5,2,0⟩,[0,r85,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨5,3,0⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨5,3,1⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨5,4,0⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨6,0,0⟩,[0,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨6,0,1⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨6,0,2⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨6,0,3⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨6,1,0⟩,[r471,r175,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨6,1,2⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨6,2,0⟩,[0,r85,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨6,2,1⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384]),(⟨6,3,0⟩,[r112,r606,r607,r608,r609,r610,r611,r612,16384])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r697) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r697) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,49152,-1761280,26337280,-213557248,1005084672,-2535522304,939573248,16849944576,-65100218368,127489155072,-144320012288,82586165248,-11642380288,-854999040]),(⟨3,0,1⟩,[-16384,524288,-7192576,56090624,-274104320,828710912,-1128366080,-2259894272,16016523264,-41872506880,63111905280,-52612997120,14602076160,7163125760]),(⟨3,0,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,0,3⟩,[16384,-450560,4964352,-28647424,92831744,-123650048,-400719872,2732572672,-7232339968,10192396288,-6125600768,-856203264]),(⟨3,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,1,0⟩,[-16384,524288,-7192576,56090624,-274104320,828710912,-1128366080,-2259894272,16016523264,-41872506880,63111905280,-52612997120,14602076160,7163125760]),(⟨3,1,1⟩,[-16384,573440,-8093696,59719680,-243220480,463962112,286326784,-3735126016,8309915648,-5282480128,-12952633344,34175074304,-26845364224]),(⟨3,1,2⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,1,3⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,2,0⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,2,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,2,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[16384,-450560,4964352,-28647424,92831744,-123650048,-400719872,2732572672,-7232339968,10192396288,-6125600768,-856203264]),(⟨3,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,3,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,3,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,4,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,24576,-991232,16449536,-146038784,746725376,-2089369600,1673003008,9689972736,-41865994240,81970749440,-86890840064,39611342848,2318131200]),(⟨4,0,1⟩,[-8192,286720,-4096000,31399936,-140894208,356630528,-304283648,-1021820928,3864993792,-5402796032,275480576,11960754176,-13709287424]),(⟨4,0,2⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨4,1,0⟩,[-8192,286720,-4096000,31399936,-140894208,356630528,-304283648,-1021820928,3864993792,-5402796032,275480576,11960754176,-13709287424]),(⟨4,1,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨4,2,0⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨5,0,0⟩,[0,-49152,1540096,-18694144,107888640,-262766592,-161480704,2621931520,-7378337792,11240095744,-8398929920,774488064,65028096]),(⟨5,0,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,0,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨6,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,0,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,2,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,3,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824])]


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

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[-16384,499712,-6201344,39641088,-128065536,81985536,961003520,-3932897280,6326550528,-6512640,-18858844160,34277842944,-25009266688,4844994560]),(⟨1,0,4⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨1,0,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,0,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-532480,7315456,-55541760,250757120,-615604224,99426304,5281005568,-20919369728,40189894656,-25440034816,-71949942784,225576861696,-294808428544,184754855936,-33914961920]),(⟨1,1,1⟩,[8192,-303104,4628480,-38322176,186949632,-510222336,340336640,3143204864,-14005805056,27762663424,-17645707264,-49512759296,150161514496,-181772394496,91952537600]),(⟨1,1,2⟩,[-16384,458752,-5013504,26591232,-62275584,-41533440,753336320,-2444394496,3480305664,634880000,-11636998144,22350970880,-18454331392,2579447808]),(⟨1,1,3⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨1,1,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨1,2,0⟩,[8192,-303104,4628480,-38322176,186949632,-510222336,340336640,3143204864,-14005805056,27762663424,-17645707264,-49512759296,150161514496,-181772394496,91952537600]),(⟨1,2,1⟩,[0,-32768,917504,-10420224,63045632,-222265344,417071104,46006272,-2588672000,6786416640,-6506020864,-6830358528,26749829120,-22737354752]),(⟨1,2,3⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,2,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-32768,958464,-11214848,66232320,-190341120,40452096,1714339840,-6377291776,9806856192,628367360,-30495842304,56628813824,-43463598080,7424442368]),(⟨1,3,1⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨1,3,2⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,3,3⟩,[0,-98304,1802240,-9306112,-9568256,229310464,-715587584,624558080,1291190272,-4241850368,3903291392]),(⟨1,3,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨1,4,1⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨1,4,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,5,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,5,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,6,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,6,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[0,49152,-1728512,25600000,-207314944,982949888,-2535112704,1198702592,16047292416,-64674332672,130462457856,-151568375808,85819727872,-166813696,-17963810816,3989995520]),(⟨2,0,1⟩,[0,24576,-974848,16007168,-141713408,728883200,-2079358976,1848934400,9094643712,-41518424064,84092526592,-92028977152,41326157824,11157938176,-10817945600]),(⟨2,0,2⟩,[0,-49152,1507328,-18104320,104775680,-262668288,-118816768,2529394688,-7440662528,11668504576,-9025093632,510705664,1884209152,-303464448]),(⟨2,0,3⟩,[-8192,262144,-3096576,15581184,-15179776,-168886272,684687360,-523468800,-3387580416,13222477824,-22753984512,21373370368,-10860093440]),(⟨2,0,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,1,0⟩,[8192,-278528,3653632,-22315008,45236224,218660864,-1739022336,4992139264,-4911161344,-13755760640,66446819328,-141541736448,191487672320,-170614456320,81134592000]),(⟨2,1,1⟩,[0,-32768,819200,-7405568,25657344,20021248,-465764352,1770389504,-3333488640,1461092352,7412285440,-18590007296,26131660800,-20062371840]),(⟨2,1,3⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,2,0⟩,[0,-81920,2424832,-28524544,167821312,-484933632,298254336,2575400960,-10029334528,18454921216,-15531114496,-6319652864,28634038272,-23040819200]),(⟨2,2,3⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,3,0⟩,[-8192,262144,-3096576,15581184,-15179776,-168886272,684687360,-523468800,-3387580416,13222477824,-22753984512,21373370368,-10860093440]),(⟨2,3,1⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,3,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,4,0⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨3,0,0⟩,[0,73728,-2736128,42344448,-355270656,1733967872,-4614881280,2788507648,25944588288,-106618642432,211581681664,-236348989440,123912323072,-484442112,-11672944640]),(⟨3,0,1⟩,[-16384,524288,-7290880,59105280,-311492608,1070997504,-2011201536,-535511040,15271706624,-47197831168,77030211584,-64372645888,13983907840,9838108672]),(⟨3,0,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,0,3⟩,[32768,-876544,9011200,-44163072,95748096,32325632,-862519296,3161538560,-6622117888,7775199232,-3594551296,-1224695808]),(⟨3,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,0,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-32768,983040,-12304384,85696512,-373768192,1029464064,-1257865216,-2979905536,18752012288,-46562951168,65393213440,-42021675008,-4470423552,12417556480]),(⟨3,1,1⟩,[-16384,573440,-8093696,59719680,-243220480,463962112,286326784,-3735126016,8309915648,-5282480128,-12952633344,34175074304,-26845364224]),(⟨3,1,2⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,1,3⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,2,0⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,2,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,2,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[32768,-876544,9011200,-44163072,95748096,32325632,-862519296,3161538560,-6622117888,7775199232,-3594551296,-1224695808]),(⟨3,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,3,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,0⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,6,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,-24576,516096,-1654784,-41263104,484057088,-2208186368,4202397696,2249310208,-30197489664,72945655808,-86380134400,41495552000,2014666752]),(⟨4,0,1⟩,[-8192,286720,-4096000,31399936,-140894208,356630528,-304283648,-1021820928,3864993792,-5402796032,275480576,11960754176,-13709287424]),(⟨4,0,2⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨4,0,3⟩,[8192,-311296,4431872,-30212096,96092160,-50364416,-543277056,1371209728,-297426944,-2833825792,2954764288]),(⟨4,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,1,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,1,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨4,1,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,0⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨4,2,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,3,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,0,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨5,0,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,0,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,0,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,3,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨6,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,0,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,2,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,3,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,49152,-1761280,26337280,-213557248,1005084672,-2535522304,939573248,16849944576,-65100218368,127489155072,-144320012288,82586165248,-11642380288,-854999040]),(⟨0,3,1⟩,[-16384,524288,-7192576,56090624,-274104320,828710912,-1128366080,-2259894272,16016523264,-41872506880,63111905280,-52612997120,14602076160,7163125760]),(⟨0,3,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨0,3,3⟩,[16384,-450560,4964352,-28647424,92831744,-123650048,-400719872,2732572672,-7232339968,10192396288,-6125600768,-856203264]),(⟨0,3,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,4,0⟩,[0,24576,-991232,16449536,-146038784,746725376,-2089369600,1673003008,9689972736,-41865994240,81970749440,-86890840064,39611342848,2318131200]),(⟨0,4,1⟩,[-8192,286720,-4096000,31399936,-140894208,356630528,-304283648,-1021820928,3864993792,-5402796032,275480576,11960754176,-13709287424]),(⟨0,4,2⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨0,5,0⟩,[0,-49152,1540096,-18694144,107888640,-262766592,-161480704,2621931520,-7378337792,11240095744,-8398929920,774488064,65028096]),(⟨0,5,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,5,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,5,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨0,6,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,6,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,6,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,0,0⟩,[0,-49152,1826816,-29384704,269295616,-1543233536,5552832512,-10589880320,-4873043968,100936155136,-342057033728,669645938688,-826978361344,596531159040,-166888030208,-48083173376,18239979520]),(⟨1,0,1⟩,[16384,-557056,8339456,-73662464,430612480,-1720451072,4370194432,-4006690816,-18761482240,98839855104,-242467405824,354646523904,-278888931328,24224858112,143478874112,-83368427520]),(⟨1,0,2⟩,[8192,-253952,3022848,-16875520,36659200,61022208,-542695424,1196556288,192077824,-10358071296,42142031872,-103725957120,169549471744,-175747604480,90565271552]),(⟨1,0,3⟩,[-32768,983040,-12165120,80936960,-308600832,562823168,650231808,-7392198656,22816997376,-39021903872,35066601472,-1440677888,-27892408320,17828937728]),(⟨1,0,4⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨1,0,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,0,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-557056,8339456,-73662464,430612480,-1720451072,4370194432,-4006690816,-18761482240,98839855104,-242467405824,354646523904,-278888931328,24224858112,143478874112,-83368427520]),(⟨1,1,1⟩,[16384,-606208,9355264,-79855616,417972224,-1356120064,2253996032,1642921984,-20262043648,53919432704,-61267820544,-34743681024,232654127104,-343551459328,196133568512]),(⟨1,1,2⟩,[-16384,425984,-4096000,16171008,770048,-263798784,1170407424,-2398388224,891633664,7421296640,-18143019008,15520612352,8295497728,-20157906944]),(⟨1,1,3⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨1,1,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨1,2,0⟩,[8192,-253952,3022848,-16875520,36659200,61022208,-542695424,1196556288,192077824,-10358071296,42142031872,-103725957120,169549471744,-175747604480,90565271552]),(⟨1,2,1⟩,[-16384,425984,-4096000,16171008,770048,-263798784,1170407424,-2398388224,891633664,7421296640,-18143019008,15520612352,8295497728,-20157906944]),(⟨1,2,3⟩,[16384,-376832,2539520,3162112,-117014528,572030976,-1111916544,91127808,3682418688,-6896140288,4208705536,504971264]),(⟨1,2,4⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,2,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-32768,1007616,-13156352,97386496,-454639616,1309548544,-1439137792,-5719195648,32506970112,-80887898112,117037350912,-88331517952,11718934528,20147068928]),(⟨1,3,1⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨1,3,2⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨1,3,3⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨1,3,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨1,4,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨1,4,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,5,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,5,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,6,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,6,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[0,24576,-704512,7479296,-27459584,-121896960,1735655424,-8088993792,18205179904,-6024372224,-86564913152,275028090880,-418646065152,318866472960,-59239792640,-45463470080]),(⟨2,0,1⟩,[8192,-278528,3751936,-25526272,89309184,-117014528,-165699584,348651520,2838405120,-15361654784,40470413312,-77259898880,123818770432,-150621126656,93363085312]),(⟨2,0,2⟩,[0,-81920,2424832,-28524544,167821312,-484933632,298254336,2575400960,-10029334528,18454921216,-15531114496,-6319652864,28634038272,-23040819200]),(⟨2,0,3⟩,[-8192,262144,-3096576,15581184,-15179776,-168886272,684687360,-523468800,-3387580416,13222477824,-22753984512,21373370368,-10860093440]),(⟨2,0,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,1,0⟩,[8192,-278528,3751936,-25526272,89309184,-117014528,-165699584,348651520,2838405120,-15361654784,40470413312,-77259898880,123818770432,-150621126656,93363085312]),(⟨2,1,1⟩,[0,-65536,1736704,-17825792,88702976,-202244096,-48693248,1816395776,-5922160640,8247508992,906264576,-25420365824,52881489920,-42799726592]),(⟨2,1,3⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,2,0⟩,[0,-81920,2424832,-28524544,167821312,-484933632,298254336,2575400960,-10029334528,18454921216,-15531114496,-6319652864,28634038272,-23040819200]),(⟨2,2,3⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,3,0⟩,[-8192,212992,-1556480,-3112960,92708864,-431652864,523206656,2098462720,-10765918208,24462573568,-31152914432,22147858432,-10795065344]),(⟨2,3,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨2,3,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,3,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,4,0⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,6,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,6,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,122880,-4341760,63791104,-505561088,2305212416,-5497913344,841859072,40142471168,-144739377152,271369420800,-290562187264,143300280320,5540347904,-13060210688]),(⟨3,0,1⟩,[-32768,983040,-12304384,85696512,-373768192,1029464064,-1257865216,-2979905536,18752012288,-46562951168,65393213440,-42021675008,-4470423552,12417556480]),(⟨3,0,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,0,3⟩,[32768,-827392,7503872,-25485312,-24182784,448380928,-1512636416,2823700480,-3549921280,3296256000,-1916895232,-351232000]),(⟨3,0,4⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,0,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-32768,983040,-12304384,85696512,-373768192,1029464064,-1257865216,-2979905536,18752012288,-46562951168,65393213440,-42021675008,-4470423552,12417556480]),(⟨3,1,1⟩,[-16384,573440,-8093696,59719680,-243220480,463962112,286326784,-3735126016,8309915648,-5282480128,-12952633344,34175074304,-26845364224]),(⟨3,1,2⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,1,3⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,2,0⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,2,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,2,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[32768,-851968,8421376,-38617088,65732608,168755200,-1451556864,5127307264,-11392483328,15905849344,-10573545472,-838942720]),(⟨3,3,1⟩,[0,-98304,1802240,-9306112,-9568256,229310464,-715587584,624558080,1291190272,-4241850368,3903291392]),(⟨3,3,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,3,3⟩,[81920,-1966080,16711680,-53084160,-16547840,410910720,-478740480,-701890560,1160069120]),(⟨3,4,0⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,6,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨4,0,1⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,0,2⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,0,3⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,1,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,1,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨4,1,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,0⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,2,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,3,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,0,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨5,0,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,0,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,0,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,3,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨6,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,0,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,2,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,3,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-49152,1826816,-29384704,269295616,-1543233536,5552832512,-10589880320,-4873043968,100936155136,-342057033728,669645938688,-826978361344,596531159040,-166888030208,-48083173376,18239979520]),(⟨0,1,1⟩,[16384,-557056,8339456,-73662464,430612480,-1720451072,4370194432,-4006690816,-18761482240,98839855104,-242467405824,354646523904,-278888931328,24224858112,143478874112,-83368427520]),(⟨0,1,2⟩,[8192,-253952,3022848,-16875520,36659200,61022208,-542695424,1196556288,192077824,-10358071296,42142031872,-103725957120,169549471744,-175747604480,90565271552]),(⟨0,1,3⟩,[-32768,983040,-12165120,80936960,-308600832,562823168,650231808,-7392198656,22816997376,-39021903872,35066601472,-1440677888,-27892408320,17828937728]),(⟨0,1,4⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨0,1,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,1,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,2,0⟩,[0,24576,-704512,7479296,-27459584,-121896960,1735655424,-8088993792,18205179904,-6024372224,-86564913152,275028090880,-418646065152,318866472960,-59239792640,-45463470080]),(⟨0,2,1⟩,[8192,-278528,3751936,-25526272,89309184,-117014528,-165699584,348651520,2838405120,-15361654784,40470413312,-77259898880,123818770432,-150621126656,93363085312]),(⟨0,2,2⟩,[0,-81920,2424832,-28524544,167821312,-484933632,298254336,2575400960,-10029334528,18454921216,-15531114496,-6319652864,28634038272,-23040819200]),(⟨0,2,3⟩,[-8192,262144,-3096576,15581184,-15179776,-168886272,684687360,-523468800,-3387580416,13222477824,-22753984512,21373370368,-10860093440]),(⟨0,2,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨0,3,0⟩,[0,122880,-4341760,63791104,-505561088,2305212416,-5497913344,841859072,40142471168,-144739377152,271369420800,-290562187264,143300280320,5540347904,-13060210688]),(⟨0,3,1⟩,[-32768,983040,-12304384,85696512,-373768192,1029464064,-1257865216,-2979905536,18752012288,-46562951168,65393213440,-42021675008,-4470423552,12417556480]),(⟨0,3,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨0,3,3⟩,[32768,-827392,7503872,-25485312,-24182784,448380928,-1512636416,2823700480,-3549921280,3296256000,-1916895232,-351232000]),(⟨0,3,4⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨0,3,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,4,0⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨0,4,1⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨0,4,2⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨0,4,3⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨0,4,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,5,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨0,5,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,5,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨0,5,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,5,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨0,6,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,6,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,6,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,0,0⟩,[0,-49152,1826816,-29384704,269295616,-1543233536,5552832512,-10589880320,-4873043968,100936155136,-342057033728,669645938688,-826978361344,596531159040,-166888030208,-48083173376,18239979520]),(⟨1,0,1⟩,[16384,-557056,8339456,-73662464,430612480,-1720451072,4370194432,-4006690816,-18761482240,98839855104,-242467405824,354646523904,-278888931328,24224858112,143478874112,-83368427520]),(⟨1,0,2⟩,[8192,-253952,3022848,-16875520,36659200,61022208,-542695424,1196556288,192077824,-10358071296,42142031872,-103725957120,169549471744,-175747604480,90565271552]),(⟨1,0,3⟩,[-32768,983040,-12165120,80936960,-308600832,562823168,650231808,-7392198656,22816997376,-39021903872,35066601472,-1440677888,-27892408320,17828937728]),(⟨1,0,4⟩,[-16384,565248,-7602176,50880512,-168722432,119947264,1222705152,-5190926336,8625045504,-280027136,-25648365568,47651545088,-32481935360]),(⟨1,0,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,0,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-581632,9363456,-91783168,610467840,-2825297920,8640962560,-13294387200,-16603594752,157489815552,-459494776832,781242990592,-783354724352,343258144768,102202892288,-132821893120]),(⟨1,1,1⟩,[24576,-909312,14082048,-121389056,648994816,-2202017792,4167655424,142639104,-26518282240,80076201984,-104889933824,-19974602752,315146739712,-505330524160,300314599424]),(⟨1,1,2⟩,[-16384,393216,-3178496,5750784,63815680,-486064128,1587478528,-2352381952,-1697038336,14207713280,-24649039872,8690253824,35045326848,-42895261696]),(⟨1,1,3⟩,[-24576,851968,-11599872,79200256,-271048704,227278848,1813315584,-7904231424,13069967360,-159711232,-38876479488,69865865216,-45618012160]),(⟨1,1,4⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨1,2,0⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨1,2,1⟩,[-16384,393216,-3276800,8765440,26427392,-243777536,704643072,-627998720,-2441854976,8882388992,-10730733568,-3069394944,34427158528,-40220278784]),(⟨1,2,3⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨1,2,4⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,2,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨1,3,1⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨1,3,2⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨1,3,3⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨1,3,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨1,4,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨1,4,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,5,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,5,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,6,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,6,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[0,24576,-704512,7479296,-27459584,-121896960,1735655424,-8088993792,18205179904,-6024372224,-86564913152,275028090880,-418646065152,318866472960,-59239792640,-45463470080]),(⟨2,0,1⟩,[8192,-278528,3751936,-25526272,89309184,-117014528,-165699584,348651520,2838405120,-15361654784,40470413312,-77259898880,123818770432,-150621126656,93363085312]),(⟨2,0,2⟩,[0,-81920,2424832,-28524544,167821312,-484933632,298254336,2575400960,-10029334528,18454921216,-15531114496,-6319652864,28634038272,-23040819200]),(⟨2,0,3⟩,[-8192,262144,-3096576,15581184,-15179776,-168886272,684687360,-523468800,-3387580416,13222477824,-22753984512,21373370368,-10860093440]),(⟨2,0,4⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨2,1,0⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨2,1,1⟩,[-16384,393216,-3276800,8765440,26427392,-243777536,704643072,-627998720,-2441854976,8882388992,-10730733568,-3069394944,34427158528,-40220278784]),(⟨2,1,3⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨2,1,4⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨2,1,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-131072,3932160,-46628864,272596992,-747601920,179437568,5104795648,-17469997056,30123425792,-24556208128,-5808947200,30518247424,-23344283648]),(⟨2,2,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,3,0⟩,[-8192,212992,-1556480,-3112960,92708864,-431652864,523206656,2098462720,-10765918208,24462573568,-31152914432,22147858432,-10795065344]),(⟨2,3,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨2,3,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,3,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,4,0⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨2,4,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨2,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,6,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,6,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,122880,-4341760,63791104,-505561088,2305212416,-5497913344,841859072,40142471168,-144739377152,271369420800,-290562187264,143300280320,5540347904,-13060210688]),(⟨3,0,1⟩,[-32768,983040,-12304384,85696512,-373768192,1029464064,-1257865216,-2979905536,18752012288,-46562951168,65393213440,-42021675008,-4470423552,12417556480]),(⟨3,0,2⟩,[-8192,237568,-2457600,9625600,5562368,-155435008,429129728,-91373568,-2933415936,11360411648,-21627043840,22988808192,-13071048704]),(⟨3,0,3⟩,[32768,-827392,7503872,-25485312,-24182784,448380928,-1512636416,2823700480,-3549921280,3296256000,-1916895232,-351232000]),(⟨3,0,4⟩,[-8192,163840,-1220608,5373952,-25444352,107413504,-216154112,-917504,724328448,-1397587968,1139597312]),(⟨3,0,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨3,1,1⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨3,1,2⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨3,1,3⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨3,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,2,0⟩,[-8192,212992,-1556480,-3112960,92708864,-431652864,523206656,2098462720,-10765918208,24462573568,-31152914432,22147858432,-10795065344]),(⟨3,2,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨3,2,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨3,2,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[32768,-802816,6914048,-19939328,-54198272,584810496,-2101673984,4789469184,-8320286720,11426906112,-8895889408,34521088]),(⟨3,3,1⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨3,3,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,3,3⟩,[98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨3,4,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨3,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,6,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨4,0,1⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,0,2⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,0,3⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,1,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,1,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨4,1,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,0⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,2,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,3,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,0,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨5,0,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,0,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,0,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,3,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨6,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,0,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,2,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,3,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-49152,1941504,-33538048,333103104,-2090967040,8427339776,-19675521024,7796170752,127316344832,-534703529984,1201926242304,-1712243146752,1502773633024,-648982577152,-34757189632,125048856576,-25364971520]),(⟨0,0,1⟩,[0,-73728,2908160,-49840128,488808448,-3018244096,11913125888,-27028496384,9437732864,169438306304,-676785414144,1437110452224,-1890852970496,1450465591296,-434597289984,-148433969152,87011205120]),(⟨0,0,2⟩,[0,73728,-2424832,32563200,-223526912,740179968,-83312640,-9237233664,37776031744,-69138866176,28473851904,148923015168,-350360813568,319752503296,-72043216896,-43534303232]),(⟨0,0,3⟩,[0,147456,-5349376,80658432,-655671296,3062661120,-7461888000,1084850176,57053118464,-208594583552,396059189248,-427766333440,209005002752,17075666944,-27528962048]),(⟨0,0,4⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨0,0,5⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨0,0,6⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨0,1,0⟩,[0,-73728,2908160,-49840128,488808448,-3018244096,11913125888,-27028496384,9437732864,169438306304,-676785414144,1437110452224,-1890852970496,1450465591296,-434597289984,-148433969152,87011205120]),(⟨0,1,1⟩,[16384,-581632,9461760,-95223808,661815296,-3255279616,10875215872,-20720304128,-1744289792,146920562688,-491544928256,893147185152,-935522402304,425072435200,113406992384,-149827141632]),(⟨0,1,2⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨0,1,3⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨0,1,4⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨0,1,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,1,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,2,0⟩,[0,73728,-2424832,32563200,-223526912,740179968,-83312640,-9237233664,37776031744,-69138866176,28473851904,148923015168,-350360813568,319752503296,-72043216896,-43534303232]),(⟨0,2,1⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨0,2,2⟩,[0,-131072,3932160,-46628864,272596992,-747601920,179437568,5104795648,-17469997056,30123425792,-24556208128,-5808947200,30518247424,-23344283648]),(⟨0,2,3⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨0,2,4⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨0,2,5⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨0,2,6⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,3,0⟩,[0,147456,-5349376,80658432,-655671296,3062661120,-7461888000,1084850176,57053118464,-208594583552,396059189248,-427766333440,209005002752,17075666944,-27528962048]),(⟨0,3,1⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨0,3,2⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨0,3,3⟩,[32768,-802816,6914048,-19939328,-54198272,584810496,-2101673984,4789469184,-8320286720,11426906112,-8895889408,34521088]),(⟨0,3,4⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨0,3,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,3,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,4,0⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨0,4,1⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨0,4,2⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨0,4,3⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨0,4,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,5,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨0,5,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,5,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨0,5,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,5,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨0,6,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,6,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,6,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,0,0⟩,[0,-73728,2908160,-49840128,488808448,-3018244096,11913125888,-27028496384,9437732864,169438306304,-676785414144,1437110452224,-1890852970496,1450465591296,-434597289984,-148433969152,87011205120]),(⟨1,0,1⟩,[16384,-581632,9461760,-95223808,661815296,-3255279616,10875215872,-20720304128,-1744289792,146920562688,-491544928256,893147185152,-935522402304,425072435200,113406992384,-149827141632]),(⟨1,0,2⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨1,0,3⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨1,0,4⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨1,0,5⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,0,6⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-581632,9461760,-95223808,661815296,-3255279616,10875215872,-20720304128,-1744289792,146920562688,-491544928256,893147185152,-935522402304,425072435200,113406992384,-149827141632]),(⟨1,1,1⟩,[24576,-909312,14180352,-124600320,693067776,-2537693184,5740978176,-4500848640,-18768715776,78470307840,-130866339840,44307234816,247477837824,-485337194496,312543092736]),(⟨1,1,2⟩,[-16384,393216,-3276800,8765440,26427392,-243777536,704643072,-627998720,-2441854976,8882388992,-10730733568,-3069394944,34427158528,-40220278784]),(⟨1,1,3⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨1,1,4⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨1,2,0⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨1,2,1⟩,[-16384,393216,-3276800,8765440,26427392,-243777536,704643072,-627998720,-2441854976,8882388992,-10730733568,-3069394944,34427158528,-40220278784]),(⟨1,2,3⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨1,2,4⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,2,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨1,3,1⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨1,3,2⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨1,3,3⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨1,3,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨1,4,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨1,4,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,5,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,5,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,6,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,6,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[0,73728,-2424832,32563200,-223526912,740179968,-83312640,-9237233664,37776031744,-69138866176,28473851904,148923015168,-350360813568,319752503296,-72043216896,-43534303232]),(⟨2,0,1⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨2,0,2⟩,[0,-131072,3932160,-46628864,272596992,-747601920,179437568,5104795648,-17469997056,30123425792,-24556208128,-5808947200,30518247424,-23344283648]),(⟨2,0,3⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨2,0,4⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨2,0,5⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,0,6⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,1,0⟩,[8192,-229376,2146304,-4079616,-60981248,454230016,-1048731648,-1597997056,17036288000,-53482389504,100258152448,-131473096704,143206727680,-144596336640,91975819264]),(⟨2,1,1⟩,[-16384,393216,-3276800,8765440,26427392,-243777536,704643072,-627998720,-2441854976,8882388992,-10730733568,-3069394944,34427158528,-40220278784]),(⟨2,1,3⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨2,1,4⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨2,1,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-131072,3932160,-46628864,272596992,-747601920,179437568,5104795648,-17469997056,30123425792,-24556208128,-5808947200,30518247424,-23344283648]),(⟨2,2,3⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,3,0⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨2,3,1⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨2,3,2⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨2,3,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨2,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,4,0⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨2,4,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨2,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,6,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,6,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,147456,-5349376,80658432,-655671296,3062661120,-7461888000,1084850176,57053118464,-208594583552,396059189248,-427766333440,209005002752,17075666944,-27528962048]),(⟨3,0,1⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨3,0,2⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨3,0,3⟩,[32768,-802816,6914048,-19939328,-54198272,584810496,-2101673984,4789469184,-8320286720,11426906112,-8895889408,34521088]),(⟨3,0,4⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨3,0,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,0,6⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-32768,1007616,-13254656,100401152,-492027904,1551835136,-2321973248,-3994812416,31762153472,-86213222400,130955657216,-100091166720,11100766208,22822051840]),(⟨3,1,1⟩,[-24576,851968,-11698176,82280448,-309616640,476577792,918421504,-6212747264,12490039296,-5682823168,-25372884992,59612299264,-46191222784]),(⟨3,1,2⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨3,1,3⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨3,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,2,0⟩,[-8192,262144,-3178496,18972672,-66756608,211943424,-786300928,2403926016,-6273064960,15284961280,-25006014464,22601105408,-12009725952]),(⟨3,2,1⟩,[16384,-344064,1687552,11649024,-157122560,654671872,-1082949632,-475430912,4935204864,-7211073536,1315356672,3753164800]),(⟨3,2,2⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨3,2,3⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[32768,-802816,6914048,-19939328,-54198272,584810496,-2101673984,4789469184,-8320286720,11426906112,-8895889408,34521088]),(⟨3,3,1⟩,[-16384,327680,-2441216,10747904,-50888704,214827008,-432308224,-1835008,1448656896,-2795175936,2279194624]),(⟨3,3,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨3,3,3⟩,[98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨3,4,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨3,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,6,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,0,-434176,13049856,-159522816,1006428160,-3272294400,3187490816,15259451392,-69847760896,138508099584,-144449626112,57066741760,12419162112]),(⟨4,0,1⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,0,2⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,0,3⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,1,0⟩,[-16384,565248,-7700480,53960704,-207290368,369246208,327811072,-3499442176,8045117440,-5803139072,-12144771072,37397979136,-33055145984]),(⟨4,1,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨4,1,2⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,0⟩,[0,81920,-2359296,27164672,-160038912,498696192,-621150208,-904396800,4324982784,-4793876480,-1215692800,4121657344]),(⟨4,2,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨4,2,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[-8192,114688,188416,-10158080,54771712,-64847872,-259997696,744816640,-139960320,-1387151360,1330667520]),(⟨4,3,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,0,0⟩,[0,-73728,2441216,-31432704,195035136,-538984448,-67403776,4811767808,-15210840064,24342257664,-17924800512,-66461696,2341011456]),(⟨5,0,1⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,0,2⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,0,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨5,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨5,3,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-24576,917504,-13131776,89915392,-279625728,61079552,2303606784,-7842562048,12609593344,-8656650240,-487710720]),(⟨6,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,0,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨6,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,2,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨6,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,3,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824])]


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
    (Poly.add (Poly.scale (K.ofRat r698) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 7).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r697*r697 : ℚ)=r698 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 7 r697 r697 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=7 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 7).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C098

#print axioms Coulomb8.Columns.C098.sound
