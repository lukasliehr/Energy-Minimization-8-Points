import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C066

def r0 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -2208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 26400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1339488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 6701472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -24657216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 9785280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -143748288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 223156608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -14370528, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 168743520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -47812320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -21306720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 17734272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1839744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -66400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 527808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -2976544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 12604864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -41163968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 104483584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -204822400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 304218496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -330111328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 243572032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -102120096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 8560192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 1125504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 50560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -360608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 2092896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -9023360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 1693824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -67552736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 16327392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -135859072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 108096512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -51528544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 11528096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 212288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1400576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 6418592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -3095168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 54978048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -104164992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 143297248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -135336960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 11008320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -16648320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -4137632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -6176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 85024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -650016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 3291584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -11906752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 4516416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -61800384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 87625632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -5115168, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 55255584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -2551776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 22656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -202656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 151936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -3798464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 1371264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -16999872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 20180864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -14327840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 4072960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 1439584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 8576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -5760, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 609408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2517120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 7270272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -14571392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 2823808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -16728192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 7308544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -8320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 59264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -234624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 617216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1004928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 849024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -247168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -37184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -3712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -163456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 531840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -1113984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 1334656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -881536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -44736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 392512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -2257792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 9372864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -29718656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 73708416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -142587456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 211075968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -231334080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 177342272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -86101504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 3028288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -5280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -326432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 1344992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -3838144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 432256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -8322752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 1876768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 11119456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -2933760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 17605600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -973088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 84576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -641248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 460864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -11643584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 30908480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -60417856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 85687712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -84946208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 53828960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -2484512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 51200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -299008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 780288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -706560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -1337344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 4861952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -6113280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -31616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 211840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -912896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 390912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -5720192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 8092800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -7196096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 477376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -4096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 116736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -206848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 708608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -17536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 135168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -83968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 1703680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3244288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 218112, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -2192384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -26240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 74368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 14272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -124064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 622592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -2093376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 4834688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1053632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 6643200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1970208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -2145088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 2052832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 37248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -76416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -30336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 322944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -356736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 46464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -203264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 599296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1074176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1025152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -446976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -21952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 12160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -18944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 795136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -3208448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 9067776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -17702400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 23347712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -2723456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 7933824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -58368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 420864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -1523712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 2856960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -1456128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -6260736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 2605056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -24830976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 2786304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 145408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -239616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -83968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 915456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -1439744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 13200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -669744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 3350736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -12328608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 4892640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -71874144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 111578304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -7185264, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 84371760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -23906160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -10653360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 8867136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -919872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -33200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 263904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1488272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 6302432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -20581984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 52241792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -102411200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 152109248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -165055664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 121786016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -51060048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 4280096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 562752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 25280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -180304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 1046448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -4511680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 846912, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -33776368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 8163696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -67929536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 54048256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -25764272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 5764048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 106144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -700288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 3209296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -1547584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 27489024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -52082496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 71648624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -67668480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 5504160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -8324160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -2068816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -3088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 42512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -325008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1645792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -5953376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 2258208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -30900192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 43812816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -2557584, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 27627792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -1275888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 11328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -101328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 75968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -1899232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 685632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -8499936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 10090432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -7163920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 2036480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 719792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 4288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -2880, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 304704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -1258560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 3635136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -7285696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1411904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -8364096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 3654272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -4160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 29632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -117312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 308608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -502464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 424512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -123584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -18592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 16960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -81728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 265920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -556992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 667328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -440768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -22368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 196256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -1128896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 4686432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -14859328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 36854208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -71293728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 105537984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -115667040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 88671136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -43050752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1514144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -2640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -163216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 672496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -1919072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 216128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -4161376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 938384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 5559728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -1466880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 8802800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -486544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 42288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -320624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 230432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -5821792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 15454240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -30208928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 42843856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -42473104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 26914480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -1242256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 25600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -149504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 390144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -353280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -668672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 2430976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -3056640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 1248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -15808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 105920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -456448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 195456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -2860096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 4046400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -3598048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 238688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 58368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -103424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 354304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -8768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 67584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -41984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 851840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -1622144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 109056, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -1096192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -13120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 37184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -48, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 7136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -62032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 311296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -1046688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 2417344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -526816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 3321600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -985104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -1072544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 1026416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 18624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -38208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -15168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 161472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -178368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 23232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -101632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 299648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -537088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 512576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -223488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -10976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 6080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -9472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 397568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -1604224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 4533888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -8851200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 11673856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -1361728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 3966912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -34624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -14272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 210432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -761856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 1428480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -728064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -3130368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 1302528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -12415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 1393152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 72704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -119808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -41984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 457728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -719872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29],[r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43],[r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56],[r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68],[r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79],[r80,r81,r82,r83,r84,r85,r86,r87,r88,r89],[r90,r91,r92,r93,r94,r95,r96,r97,r98],[r99,r100,r101,r102,r103,r104,r105,r106],[],[],[],[],[r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120],[r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r57,r58,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143],[0,0,r144,r145,r146,r147,r148,r149,r150,r151,27648],[r107,r152,r153,r154,r155,r156,r157,r158,r159,r160],[0,0,r161,r162,r163,r164,r165,r166,-6144],[],[],[],[],[],[0,0,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176],[r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187],[0,r188,r189,r190,r191,r192,r193,r194,r195,768],[r196,r197,r198,r199,r200,r201,r202,r203,r204],[0,0,r80,r205,r206,r207,r208,-256],[r188,r209,r210,r211,r212,r213,-1152],[],[r80,r214,r215,r216,256],[],[r217,r218,r219,r220,r221,r222,r223,r224,r225,r226],[r227,r228,r229,r230,r231,r232,r233,r234,896],[r99,r100,r101,r102,r103,r104,r105,r106],[],[],[],[],[0,0,r235,r236,r237,r144,r238,-512],[r188,r209,r210,r211,r212,r213,-1152],[],[r80,r214,r215,r216,256],[],[],[],[],[],[0,0,r214,r239,r240,r241,r242,r243,r244,r245,r246,r247,-64512],[0,0,0,0,r161,r211,r248,r249,r250,r251,r252,6144],[0,0,r144,r145,r146,r147,r148,r149,r150,r151,27648],[],[0,0,r161,r162,r163,r164,r165,r166,-6144],[],[],[],[],[],[],[],[r227,r228,r229,r230,r231,r232,r233,r234,896],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r235,r236,r237,r144,r238,-512],[],[],[],[],[],[r188,r209,r210,r211,r212,r213,-1152],[],[],[],[],[r80,r214,r215,r216,256],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,0,1⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,0,2⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨0,0,3⟩,[r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,0,4⟩,[r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,0,5⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,0,6⟩,[r227,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,0,7⟩,[r121,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,0,8⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,1,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,1,1⟩,[r30,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨0,1,2⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,1,3⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,1,4⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨0,1,5⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨0,1,6⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨0,2,0⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨0,2,1⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,2,2⟩,[0,0,r90,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨0,2,3⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨0,2,4⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨0,2,5⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨0,2,6⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨0,2,7⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨0,2,9⟩,[r227,r460,r461,r462,128]),(⟨0,3,0⟩,[r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,3,1⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,3,2⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨0,3,3⟩,[r15,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨0,3,4⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨0,3,5⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,4,0⟩,[r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨0,4,1⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨0,4,2⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨0,4,3⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨0,4,4⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨0,4,5⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨0,4,7⟩,[r227,r460,r461,r462,128]),(⟨0,5,0⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,5,1⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨0,5,2⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨0,5,3⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,5,4⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨0,6,0⟩,[r227,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,6,1⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨0,6,2⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨0,7,0⟩,[r121,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,7,2⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨0,7,4⟩,[r227,r460,r461,r462,128]),(⟨0,8,0⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,9,2⟩,[r227,r460,r461,r462,128]),(⟨1,0,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨1,0,1⟩,[r30,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨1,0,2⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨1,0,3⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨1,0,4⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨1,0,5⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨1,0,6⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨1,1,0⟩,[r30,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨1,1,1⟩,[0,0,r460,r479,r480,r481,r482,r483,r484,r485,r486,r487,-32256]),(⟨1,1,2⟩,[0,0,0,0,r410,r457,r488,r489,r490,r491,r492,3072]),(⟨1,1,3⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨1,1,5⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨1,2,0⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨1,2,1⟩,[0,0,0,0,r410,r457,r488,r489,r490,r491,r492,3072]),(⟨1,2,4⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨1,3,0⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨1,3,1⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨1,4,0⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨1,4,2⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨1,5,0⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨1,5,1⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨1,6,0⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨2,0,0⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨2,0,1⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨2,0,2⟩,[0,0,r90,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨2,0,3⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨2,0,4⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨2,0,5⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨2,0,6⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨2,0,7⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨2,0,9⟩,[r227,r460,r461,r462,128]),(⟨2,1,0⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨2,1,1⟩,[0,0,0,0,r410,r457,r488,r489,r490,r491,r492,3072]),(⟨2,1,4⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨2,2,0⟩,[0,0,r90,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨2,2,4⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨2,3,0⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨2,3,4⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨2,4,0⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨2,4,1⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨2,4,2⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨2,4,3⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨2,4,5⟩,[r227,r460,r461,r462,128]),(⟨2,5,0⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨2,5,4⟩,[r227,r460,r461,r462,128]),(⟨2,6,0⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨2,7,0⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨2,9,0⟩,[r227,r460,r461,r462,128]),(⟨3,0,0⟩,[r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨3,0,1⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,0,2⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨3,0,3⟩,[r15,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨3,0,4⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨3,0,5⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨3,1,0⟩,[r310,r311,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,1,1⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨3,2,0⟩,[r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨3,2,4⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨3,3,0⟩,[r15,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨3,4,0⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨3,4,2⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨3,5,0⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨4,0,0⟩,[r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321]),(⟨4,0,1⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨4,0,2⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨4,0,3⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨4,0,4⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨4,0,5⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨4,0,7⟩,[r227,r460,r461,r462,128]),(⟨4,1,0⟩,[0,0,r207,r394,r395,r396,r397,r398,r399,r400,13824]),(⟨4,1,2⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨4,2,0⟩,[0,r436,r437,r438,r439,r440,r441,r442,r443,384]),(⟨4,2,1⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨4,2,2⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨4,2,3⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨4,2,5⟩,[r227,r460,r461,r462,128]),(⟨4,3,0⟩,[r107,r472,r473,r474,r475,r476,r477,r478,448]),(⟨4,3,2⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨4,4,0⟩,[0,0,r80,r205,r206,r207,r208,-256]),(⟨4,5,0⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨4,5,2⟩,[r227,r460,r461,r462,128]),(⟨4,7,0⟩,[r227,r460,r461,r462,128]),(⟨5,0,0⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨5,0,1⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨5,0,2⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨5,0,3⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨5,0,4⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨5,1,0⟩,[r30,r401,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨5,1,1⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨5,2,0⟩,[r57,r144,r444,r445,r446,r447,r448,r449,r450]),(⟨5,2,4⟩,[r227,r460,r461,r462,128]),(⟨5,3,0⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨5,4,0⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨5,4,2⟩,[r227,r460,r461,r462,128]),(⟨6,0,0⟩,[r227,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨6,0,1⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨6,0,2⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨6,1,0⟩,[0,0,r410,r411,r412,r413,r414,r415,-3072]),(⟨6,2,0⟩,[0,0,r227,r451,r452,r453,r454,-128]),(⟨7,0,0⟩,[r121,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨7,0,2⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨7,0,4⟩,[r227,r460,r461,r462,128]),(⟨7,2,0⟩,[r436,r455,r456,r457,r458,r459,-576]),(⟨7,4,0⟩,[r227,r460,r461,r462,128]),(⟨8,0,0⟩,[r350,r351,r352,r353,r354,r355,r356,r357]),(⟨9,0,2⟩,[r227,r460,r461,r462,128]),(⟨9,2,0⟩,[r227,r460,r461,r462,128])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-384,8384,-78592,440960,-1705088,4764160,-9624448,13537664,-12357632,6218048,-613248]),(⟨0,0,1⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,0,2⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,0,3⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,1,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,1,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨0,2,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨1,0,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨1,1,0⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨2,0,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨2,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨4,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r493) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 8 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r494) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨5,0,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,0,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨5,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,1,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨5,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨6,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨7,0,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨9,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨9,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨0,5,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,5,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,5,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,6,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,6,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,7,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,9,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-384,10304,-124352,921984,-4790720,18622400,-55896832,131144192,-240631808,342600896,-371565248,295944320,-161034432,50272064,-4292736]),(⟨1,0,1⟩,[-64,2816,-44736,395584,-2316160,9784512,-31082624,75582336,-141352512,202326912,-217731264,169222976,-87130624,23391424]),(⟨1,0,2⟩,[448,-10560,105344,-619072,2477632,-7147392,15041536,-22973312,24840512,-17544000,6059136,1132992,-1822016]),(⟨1,0,3⟩,[128,-4352,53760,-371584,1730048,-5806848,14258432,-25689088,33730944,-31294464,19039488,-6170752]),(⟨1,1,0⟩,[-64,2816,-44736,395584,-2316160,9784512,-31082624,75582336,-141352512,202326912,-217731264,169222976,-87130624,23391424]),(⟨1,1,1⟩,[0,0,2048,-38912,280576,-1015808,1904640,-970752,-4173824,12156928,-16553984,13002752,-5117952]),(⟨1,2,0⟩,[448,-10560,105344,-619072,2477632,-7147392,15041536,-22973312,24840512,-17544000,6059136,1132992,-1822016]),(⟨1,2,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[128,-4352,53760,-371584,1730048,-5806848,14258432,-25689088,33730944,-31294464,19039488,-6170752]),(⟨1,4,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,5,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,6,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[-64,2816,-45504,413120,-2490112,10823616,-35374720,88520832,-170129728,248651136,-269521856,206374336,-100793216,24617920]),(⟨2,0,1⟩,[0,0,1920,-33792,212352,-528896,-344832,6327808,-21086976,39782912,-47131776,34078208,-11801216]),(⟨2,0,2⟩,[0,0,896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨2,0,3⟩,[0,0,256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨2,1,0⟩,[0,0,1920,-33792,212352,-528896,-344832,6327808,-21086976,39782912,-47131776,34078208,-11801216]),(⟨2,1,1⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨2,2,0⟩,[0,0,896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨2,2,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[0,0,256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨2,4,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨2,5,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1600,-38784,411520,-2641024,11759680,-38562304,95124480,-176160768,239921600,-229272192,138284160,-38659968,-2986048]),(⟨3,0,1⟩,[192,-8000,115392,-910912,4722048,-17480320,47558528,-95146624,137644480,-138597952,88618432,-28612416]),(⟨3,0,2⟩,[-1344,28544,-248384,1252864,-4262016,10064128,-16141440,16578048,-8837696,142208,2342592]),(⟨3,0,3⟩,[-384,12160,-132608,795136,-3208448,9067776,-17702400,23347712,-19064192,7933824]),(⟨3,0,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,1,0⟩,[192,-8000,115392,-910912,4722048,-17480320,47558528,-95146624,137644480,-138597952,88618432,-28612416]),(⟨3,1,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨3,2,0⟩,[-1344,28544,-248384,1252864,-4262016,10064128,-16141440,16578048,-8837696,142208,2342592]),(⟨3,2,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-384,12160,-132608,795136,-3208448,9067776,-17702400,23347712,-19064192,7933824]),(⟨3,4,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,4,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,5,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,0,0⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨4,0,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,0,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,0⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,4,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨5,0,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,0,2⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,0,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,1,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,4,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨6,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨6,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨7,0,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨9,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨9,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨0,0,6⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,0,7⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,0,8⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,1,0⟩,[-384,10304,-124352,921984,-4790720,18622400,-55896832,131144192,-240631808,342600896,-371565248,295944320,-161034432,50272064,-4292736]),(⟨0,1,1⟩,[-64,2816,-44736,395584,-2316160,9784512,-31082624,75582336,-141352512,202326912,-217731264,169222976,-87130624,23391424]),(⟨0,1,2⟩,[448,-10560,105344,-619072,2477632,-7147392,15041536,-22973312,24840512,-17544000,6059136,1132992,-1822016]),(⟨0,1,3⟩,[128,-4352,53760,-371584,1730048,-5806848,14258432,-25689088,33730944,-31294464,19039488,-6170752]),(⟨0,1,5⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,1,6⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,2,0⟩,[-64,2816,-45504,413120,-2490112,10823616,-35374720,88520832,-170129728,248651136,-269521856,206374336,-100793216,24617920]),(⟨0,2,1⟩,[0,0,1920,-33792,212352,-528896,-344832,6327808,-21086976,39782912,-47131776,34078208,-11801216]),(⟨0,2,2⟩,[0,0,896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨0,2,3⟩,[0,0,256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨0,2,5⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,2,9⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1600,-38784,411520,-2641024,11759680,-38562304,95124480,-176160768,239921600,-229272192,138284160,-38659968,-2986048]),(⟨0,3,1⟩,[192,-8000,115392,-910912,4722048,-17480320,47558528,-95146624,137644480,-138597952,88618432,-28612416]),(⟨0,3,2⟩,[-1344,28544,-248384,1252864,-4262016,10064128,-16141440,16578048,-8837696,142208,2342592]),(⟨0,3,3⟩,[-384,12160,-132608,795136,-3208448,9067776,-17702400,23347712,-19064192,7933824]),(⟨0,3,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,3,5⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,4,0⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨0,4,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨0,4,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,4,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨0,5,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,5,2⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨0,5,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,5,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,6,0⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨0,6,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,6,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,7,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,7,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,9,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-384,10304,-124352,921984,-4790720,18622400,-55896832,131144192,-240631808,342600896,-371565248,295944320,-161034432,50272064,-4292736]),(⟨1,0,1⟩,[-64,2816,-44736,395584,-2316160,9784512,-31082624,75582336,-141352512,202326912,-217731264,169222976,-87130624,23391424]),(⟨1,0,2⟩,[448,-10560,105344,-619072,2477632,-7147392,15041536,-22973312,24840512,-17544000,6059136,1132992,-1822016]),(⟨1,0,3⟩,[128,-4352,53760,-371584,1730048,-5806848,14258432,-25689088,33730944,-31294464,19039488,-6170752]),(⟨1,0,5⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,0,6⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,1,0⟩,[-128,5632,-89472,791168,-4632320,19569024,-62165248,151164672,-282705024,404653824,-435462528,338445952,-174261248,46782848]),(⟨1,1,1⟩,[0,0,4096,-77824,561152,-2031616,3809280,-1941504,-8347648,24313856,-33107968,26005504,-10235904]),(⟨1,1,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,2,0⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨1,2,1⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,2,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨1,3,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,4,0⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,4,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,5,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,6,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[-64,2816,-45504,413120,-2490112,10823616,-35374720,88520832,-170129728,248651136,-269521856,206374336,-100793216,24617920]),(⟨2,0,1⟩,[0,0,1920,-33792,212352,-528896,-344832,6327808,-21086976,39782912,-47131776,34078208,-11801216]),(⟨2,0,2⟩,[0,0,896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨2,0,3⟩,[0,0,256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨2,0,5⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨2,0,9⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨2,1,1⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨2,1,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,0⟩,[0,0,1792,-35072,270336,-1175552,3407360,-6488576,7415808,-4384768,-52480,1041152]),(⟨2,2,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,3,0⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨2,3,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,4,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,5,0⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨2,5,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,6,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,7,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1600,-38784,411520,-2641024,11759680,-38562304,95124480,-176160768,239921600,-229272192,138284160,-38659968,-2986048]),(⟨3,0,1⟩,[192,-8000,115392,-910912,4722048,-17480320,47558528,-95146624,137644480,-138597952,88618432,-28612416]),(⟨3,0,2⟩,[-1344,28544,-248384,1252864,-4262016,10064128,-16141440,16578048,-8837696,142208,2342592]),(⟨3,0,3⟩,[-384,12160,-132608,795136,-3208448,9067776,-17702400,23347712,-19064192,7933824]),(⟨3,0,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,0,5⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨3,1,0⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨3,1,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨3,2,0⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨3,2,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-768,24320,-265216,1590272,-6416896,18135552,-35404800,46695424,-38128384,15867648]),(⟨3,4,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,4,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,5,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,0,0⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨4,0,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,0,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,2,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,4,0⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,5,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨5,0,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,0,2⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,0,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,1,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,4,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨6,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨6,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨7,0,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨9,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨9,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,1152,-30912,369600,-2678976,13402944,-49314432,136993920,-287496576,446313216,-488597952,337487040,-95624640,-42613440,35468544,-3679488]),(⟨0,0,1⟩,[-384,10496,-132800,1055616,-5953088,25209728,-82327936,208967168,-409644800,608436992,-660222656,487144064,-204240192,17120384,15757056]),(⟨0,0,2⟩,[-64,1472,-13824,101120,-721216,4185792,-18046720,57590016,-135105472,228583488,-271718144,216193024,-103057088,23056192]),(⟨0,0,3⟩,[1600,-39168,424576,-2801152,12837184,-43332352,109956096,-208329984,286594496,-270673920,154116480,-33296640,-8275264]),(⟨0,0,4⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨0,0,5⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨0,0,6⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨0,0,7⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,0,8⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,1,0⟩,[-384,10496,-132800,1055616,-5953088,25209728,-82327936,208967168,-409644800,608436992,-660222656,487144064,-204240192,17120384,15757056]),(⟨0,1,1⟩,[-128,5632,-89472,785024,-4515584,18745728,-59437312,147416832,-285174912,422151936,-462668160,354684544,-172203008,42396032]),(⟨0,1,2⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨0,1,3⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨0,1,4⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨0,1,5⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,1,6⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,2,0⟩,[-64,1472,-13824,101120,-721216,4185792,-18046720,57590016,-135105472,228583488,-271718144,216193024,-103057088,23056192]),(⟨0,2,1⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨0,2,2⟩,[0,0,1792,-35072,270336,-1175552,3407360,-6488576,7415808,-4384768,-52480,1041152]),(⟨0,2,3⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨0,2,4⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨0,2,5⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨0,2,6⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,2,7⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,2,9⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1600,-39168,424576,-2801152,12837184,-43332352,109956096,-208329984,286594496,-270673920,154116480,-33296640,-8275264]),(⟨0,3,1⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨0,3,2⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨0,3,3⟩,[-768,24320,-265216,1590272,-6416896,18135552,-35404800,46695424,-38128384,15867648]),(⟨0,3,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,3,5⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,4,0⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨0,4,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨0,4,2⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨0,4,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨0,4,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨0,4,5⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,4,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨0,5,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,5,2⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨0,5,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,5,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,6,0⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨0,6,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,6,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,7,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,7,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,9,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-384,10496,-132800,1055616,-5953088,25209728,-82327936,208967168,-409644800,608436992,-660222656,487144064,-204240192,17120384,15757056]),(⟨1,0,1⟩,[-128,5632,-89472,785024,-4515584,18745728,-59437312,147416832,-285174912,422151936,-462668160,354684544,-172203008,42396032]),(⟨1,0,2⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨1,0,3⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨1,0,4⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,0,5⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,0,6⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,1,0⟩,[-128,5632,-89472,785024,-4515584,18745728,-59437312,147416832,-285174912,422151936,-462668160,354684544,-172203008,42396032]),(⟨1,1,1⟩,[0,0,6144,-116736,841728,-3047424,5713920,-2912256,-12521472,36470784,-49661952,39008256,-15353856]),(⟨1,1,2⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,1,3⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,1,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,2,0⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨1,2,1⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,2,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨1,3,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,4,0⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨1,4,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,5,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,6,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[-64,1472,-13824,101120,-721216,4185792,-18046720,57590016,-135105472,228583488,-271718144,216193024,-103057088,23056192]),(⟨2,0,1⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨2,0,2⟩,[0,0,1792,-35072,270336,-1175552,3407360,-6488576,7415808,-4384768,-52480,1041152]),(⟨2,0,3⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨2,0,4⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨2,0,5⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨2,0,6⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,0,7⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,0,9⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[448,-10560,107264,-652864,2689984,-7676288,14696704,-16645504,3753536,22238912,-41072640,35211200,-13623232]),(⟨2,1,1⟩,[0,0,0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨2,1,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,0⟩,[0,0,1792,-35072,270336,-1175552,3407360,-6488576,7415808,-4384768,-52480,1041152]),(⟨2,2,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,3,0⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨2,3,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,4,0⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨2,4,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,4,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,4,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,4,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,5,0⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨2,5,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,6,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,7,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1600,-39168,424576,-2801152,12837184,-43332352,109956096,-208329984,286594496,-270673920,154116480,-33296640,-8275264]),(⟨3,0,1⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨3,0,2⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨3,0,3⟩,[-768,24320,-265216,1590272,-6416896,18135552,-35404800,46695424,-38128384,15867648]),(⟨3,0,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,0,5⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨3,1,0⟩,[320,-12352,169152,-1282496,6452096,-23287168,61816960,-120835712,171375424,-169892416,107657920,-34783168]),(⟨3,1,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨3,2,0⟩,[-1344,28544,-248128,1245184,-4186752,9669376,-14750848,13286400,-3940416,-4290176,4105664]),(⟨3,2,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-768,24320,-265216,1590272,-6416896,18135552,-35404800,46695424,-38128384,15867648]),(⟨3,4,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨3,4,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,5,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,0,0⟩,[320,-12352,170048,-1300032,6583168,-23813504,63229824,-123600768,175251264,-173915712,110511168,-35724864]),(⟨4,0,1⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,0,2⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨4,0,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,0,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,0,5⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[0,0,-6144,102400,-598016,1560576,-1413120,-2674688,9723904,-12226560,6580224]),(⟨4,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,2,0⟩,[0,768,-13056,74496,-152832,-60672,645888,-713472,36096,182784]),(⟨4,2,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,2,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,4,0⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,5,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-2112,45312,-405312,2127104,-7596928,19197696,-33999744,40361728,-28655680,8145920,2879168]),(⟨5,0,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,0,2⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,0,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,1,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[640,-12288,92928,-406528,1198592,-2148352,2050304,-893952,-307328]),(⟨5,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨5,4,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-512,17152,-195840,1218816,-5034240,14540544,-29142784,39533312,-33456384,14617088]),(⟨6,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨6,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨7,0,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨9,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨9,2,0⟩,[-512,6144,-15360,-18432,60928])]


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
    (Poly.add (Poly.scale (K.ofRat r495) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 8).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r493*r494 : ℚ)=r495 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 8 r493 r494 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=8 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 8).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C066

#print axioms Coulomb8.Columns.C066.sound
