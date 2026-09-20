import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C116

def r0 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -7979008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 148152320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1691090944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 13463248896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -80306290688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 375337263104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -1414150848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 4369723809792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -11176019935232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 23724075802624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -849706811392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 59654366011392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -9722811957248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 59217135689728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -36466843287552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 13715201236992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -2177813020672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 116644675584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -4390912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 99024896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -76644352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 1648459776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -74664083456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 7587299328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1472639172608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 4735752798208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -12504154537984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 27216627695616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -993079230464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 70500954243072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -80521293234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 69071347318784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -40769824587776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 13638784106496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -176125607936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -466944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 17104896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -276709376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 2655617024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -17169465344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 11461787648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -280886001664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 105742368768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1412906516480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1650387779584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 93304340480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -5491917291520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 14021668454400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -21002791092224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 2923956977664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -12220621225984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 480413048832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 12288000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -14155776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 2710929408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -20299382784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 110074363904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -455609286656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1482420486144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3846183845888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 7992061362176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -13209359351808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 2418804752384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -15922556305408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 9838472495104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -172427706368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -255332941824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 253952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -7749632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 94019584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -563838976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 1342758912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 4917510144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -60889718784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 18105958400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -1037922951168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 2580666400768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -4883747381248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 6965418819584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -7157177475072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 4828408233984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -236530622464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -8159232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 137756672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -1297285120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 1134100480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -34754494464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 114439225344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -41007054848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 548185636864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -782791049216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 768270532608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -411166769152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -6030032896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 21221376000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 32636928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -350420992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 2394324992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -11635654656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 42733142016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -120948391936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 38025461760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -3816488960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 570764427264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -477516726272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 216871960576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 29163520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -59768832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 3922067456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -26846494720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 143734013952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -88950964224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 2208248266752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -6429660086272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 2192680747008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -29779634946048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 45968221274112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -54378180837376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 46413423116288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -25526387605504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 971100307456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 4947968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -101711872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 1188986880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -9173827584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 50873925632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -212869447680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 98271133696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1727893635072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 477344268288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -4777853845504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 4464229318656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -1428429242368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -2575844409344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 82053824512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -42864574464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -43778048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 76349440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -4230578176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 24675516416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -16260595712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 24793186304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1245598416896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 2924928466944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -5380430495744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 7492621500416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -1068569821184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 4833993654272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -221019701248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -29097984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -10747904, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 13790347264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -5610405888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 68696932352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -4403494912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -192648839168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 545298579456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -688314384384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 3316908032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 770048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -26017792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 377700352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -3159556096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 145965056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -67732373504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 193815789568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -57502466048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 80625451008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -389811339264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -281852919808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 999559856128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -980368080896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 273050763264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 27247329280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -9830400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 170262528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1637154816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 10143367168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -44283396096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 142371454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -48376446976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 2018672640, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -97266171904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 401647206400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 163222323200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -506066731008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 50306940928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 425984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -36634624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 240680960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -947945472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 2256994304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -1955725312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -7085162496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 25350733824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -23236214784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -16544366592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 40923725824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -181960704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -21004288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 174882816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -911802368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 3184590848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -6708592640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 215285760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 2655682560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -6784188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 49265082368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -202014720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -46891008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 239599616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -599326720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 519045120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 898170880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -540540928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 6292733952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -392953856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -3506176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 155451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -472776704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 748552192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -363069440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -2118909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 7422279680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -62980096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -3276800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 1310720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -673579008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 4521263104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -22088515584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 83677413376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -245541634048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 549639094272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -927374901248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1127095205888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -898383085568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 389197266944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 21135360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -171868160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 809566208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -2312699904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 3908632576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -2340487168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -8430649344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 31443484672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -6900187136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 35618816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 524288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -93782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 479199232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -1198653440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 1038090240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 1796341760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1081081856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 12585467904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -785907712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -7012352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 53870592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -964165632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 1330642944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -55656972288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 221085302784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -598292299776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 147047055360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -613958418432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -2213933875200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1096429338624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -1741022035968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 1557473918976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -5497552896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -66322432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 812122112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -5407244288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 21841444864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -3188195328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 62430117888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 80914939904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -437508505600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 664624955392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -297334734848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -56124243968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 588120064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -98304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 32505856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -339869696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 2204663808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -9528901632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 27932229632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -1052770304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 35210756096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 101927845888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -366623326208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 574389092352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -71433814016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 244416512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 27262976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -15728640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1182793728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -1788870656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -3644850176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 17282629632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -19050528768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -14433648640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 476053504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 21037056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -265027584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 1811349504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -7461568512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 18933743616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -24461967360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -2097020928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 125106683904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -224040517632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 180849475584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -4397924352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -57114624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -42139648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 346750976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -1721368576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 5497290752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -10617225216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 6000345088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 27020427264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -78932803584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 97566392320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -451346432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -3989504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 74076160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -845545472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 6731624448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -40153145344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 187668631552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -707075424256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 2184861904896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -5588009967616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 11862037901312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -424853405696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 29827183005696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -4861405978624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 29608567844864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -18233421643776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 6857600618496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -1088906510336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 58322337792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -2195456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 49512448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -38322176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 824229888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -37332041728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 3793649664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -736319586304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 2367876399104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -6252077268992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 13608313847808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -496539615232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 35250477121536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -40260646617088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 34535673659392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -20384912293888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 6819392053248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -88062803968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -233472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 8552448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -138354688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1327808512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -8584732672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 5730893824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -140443000832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 52871184384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -706453258240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 825193889792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 46652170240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -2745958645760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 7010834227200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -10501395546112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 1461978488832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -6110310612992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 240206524416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 6144000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -7077888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 1355464704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -10149691392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 55037181952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -227804643328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 741210243072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -1923091922944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 3996030681088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -6604679675904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 1209402376192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -7961278152704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 4919236247552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -86213853184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -127666470912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 126976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -3874816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 47009792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -281919488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 671379456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 2458755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -30444859392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 9052979200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -518961475584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 1290333200384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -2441873690624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 3482709409792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -3578588737536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 2414204116992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -118265311232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -4079616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 68878336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -648642560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 567050240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -17377247232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 57219612672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -20503527424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 274092818432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -391395524608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 384135266304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -205583384576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -3015016448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 10610688000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 16318464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -175210496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 1197162496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -5817827328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 21366571008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -60474195968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 19012730880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -1908244480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 285382213632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -238758363136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 108435980288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 14581760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -29884416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 1961033728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -13423247360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 71867006976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -44475482112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 1104124133376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -3214830043136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 1096340373504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -14889817473024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 22984110637056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -27189090418688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 23206711558144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -12763193802752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 485550153728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 2473984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 594493440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -4586913792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 25436962816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -106434723840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 49135566848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -863946817536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 238672134144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -2388926922752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 2232114659328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -714214621184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -1287922204672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 41026912256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -21432287232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 966656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -21889024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 38174720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -2115289088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 12337758208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -8130297856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 12396593152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -622799208448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 1462464233472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -2690215247872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 3746310750208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -534284910592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 2416996827136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -110509850624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -14548992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 29753344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -5373952, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 6895173632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -2805202944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 34348466176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -2201747456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -96324419584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 272649289728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -344157192192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 1658454016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 385024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -13008896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 188850176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -1579778048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 72982528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -33866186752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 96907894784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -28751233024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 40312725504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -194905669632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -140926459904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 499779928064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -490184040448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 136525381632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 13623664640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -4915200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 85131264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -818577408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 5071683584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -22141698048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 71185727488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -24188223488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 1009336320, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -48633085952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 200823603200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 81611161600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -253033365504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 25153470464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -18317312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 120340480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -473972736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 1128497152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -977862656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -3542581248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 12675366912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -11618107392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -8272183296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 20461862912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -90980352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -10502144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 87441408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -455901184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 1592295424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -3354296320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 107642880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 1327841280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -3392094208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 24632541184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -101007360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -23445504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 119799808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -299663360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 259522560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 449085440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -270270464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 3146366976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -196476928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -1753088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 77725696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -236388352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 374276096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -181534720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -1059454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 3711139840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -31490048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 655360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -336789504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 2260631552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -11044257792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 41838706688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -122770817024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 274819547136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -463687450624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 563547602944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -449191542784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 194598633472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 10567680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -85934080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 404783104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -1156349952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 1954316288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -1170243584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -4215324672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 15721742336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -3450093568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 17809408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := 26935296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -482082816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 665321472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -27828486144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 110542651392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -299146149888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := 73523527680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -306979209216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -1106966937600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 548214669312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -870511017984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 778736959488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := -2748776448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -33161216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 406061056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := -2703622144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 10920722432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := -1594097664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 31215058944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := 40457469952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := -218754252800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 332312477696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := -148667367424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := -28062121984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := 294060032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -49152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := 16252928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -169934848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := 1102331904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := -4764450816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := 13966114816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := -526385152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := 17605378048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 50963922944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -183311663104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := 287194546176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := -35716907008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := 122208256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := 13631488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := -7864320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 591396864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -894435328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := -1822425088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 8641314816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := -9525264384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := -7216824320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := 238026752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := 10518528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := -132513792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := 905674752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := -3730784256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := 9466871808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := -12230983680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := -1048510464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := 62553341952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := -112020258816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := 90424737792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := -2198962176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := -28557312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r714 : ℚ := { num := -21069824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r715 : ℚ := { num := 173375488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r716 : ℚ := { num := -860684288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r717 : ℚ := { num := 2748645376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r718 : ℚ := { num := -5308612608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r719 : ℚ := { num := 3000172544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r720 : ℚ := { num := 13510213632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r721 : ℚ := { num := -39466401792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r722 : ℚ := { num := 48783196160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r723 : ℚ := { num := -225673216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r724 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r725 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18],[r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[r0,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97],[r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[],[],[],[],[],[],[r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143],[r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158],[0,0,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[],[],[],[],[],[],[],[r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185],[r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199],[r128,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211],[r144,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222],[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233],[r234,r235,r236,r237,r238,r239,r240,r241,r242,r243],[],[],[],[r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256],[r98,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267],[0,0,r268,r269,r270,r271,r272,r273,r274,r275,-524288],[],[],[],[],[r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286],[r234,r235,r236,r237,r238,r239,r240,r241,r242,r243],[r287,r288,r289,r290,r236,r291,r292,r293,131072],[],[],[],[],[],[],[0,0,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307],[0,0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320],[0,0,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[],[],[],[],[],[],[],[r98,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333],[0,0,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,-3145728],[r98,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267],[0,0,r268,r269,r270,r271,r272,r273,r274,r275,-524288],[],[],[],[],[],[0,0,r268,r269,r270,r271,r272,r273,r274,r275,-524288],[],[],[],[],[],[],[],[],[],[],[r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356],[r234,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367],[r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286],[],[r368,r369,r370,r371,r372,r373,r374,r375,262144],[],[],[],[r234,r235,r236,r237,r238,r239,r240,r241,r242,r243],[],[],[],[r368,r369,r370,r371,r372,r373,r374,r375,262144],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,0,1⟩,[r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,0,2⟩,[r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨0,0,3⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨0,0,4⟩,[r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,0,5⟩,[r376,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨0,0,6⟩,[r111,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,1,0⟩,[r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,1,1⟩,[r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨0,1,2⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,1,3⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨0,1,4⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨0,2,0⟩,[r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨0,2,1⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,2,2⟩,[r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨0,2,3⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨0,2,4⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,2,5⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,2,6⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨0,2,7⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨0,3,0⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨0,3,1⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨0,3,2⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨0,3,3⟩,[r98,r99,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨0,3,4⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨0,3,5⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨0,4,0⟩,[r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,4,1⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨0,4,2⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,4,3⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨0,4,4⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨0,4,5⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨0,4,6⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨0,5,0⟩,[r376,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨0,5,2⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,5,3⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨0,5,4⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨0,6,0⟩,[r111,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,6,2⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨0,6,4⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨0,7,2⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨1,0,0⟩,[r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨1,0,1⟩,[r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨1,0,2⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,0,3⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨1,0,4⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨1,1,0⟩,[r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨1,1,1⟩,[0,0,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663,r664,r665]),(⟨1,1,2⟩,[0,0,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨1,1,3⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨1,2,0⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,2,1⟩,[0,0,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨1,2,2⟩,[r111,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690,r691]),(⟨1,2,3⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨1,2,4⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨1,2,5⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨1,3,0⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨1,3,1⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨1,3,2⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨1,3,4⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨1,4,0⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨1,4,2⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨1,4,3⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨1,5,2⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨2,0,0⟩,[r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨2,0,1⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨2,0,2⟩,[r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨2,0,3⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨2,0,4⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,0,5⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨2,0,6⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,0,7⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨2,1,0⟩,[r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨2,1,1⟩,[0,0,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨2,1,2⟩,[r111,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690,r691]),(⟨2,1,3⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨2,1,4⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨2,1,5⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨2,2,0⟩,[r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨2,2,1⟩,[r111,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690,r691]),(⟨2,2,2⟩,[r701,r702,r703,r704,r705,r706,r707,r708,r709,r710,r711,r712,r713]),(⟨2,2,3⟩,[r144,r212,r714,r715,r716,r717,r718,r719,r720,r721,r722,r723]),(⟨2,2,4⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨2,2,6⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨2,3,0⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨2,3,1⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨2,3,2⟩,[r144,r212,r714,r715,r716,r717,r718,r719,r720,r721,r722,r723]),(⟨2,3,4⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨2,4,0⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,4,1⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨2,4,2⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨2,4,3⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨2,4,4⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨2,5,0⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨2,5,1⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨2,6,0⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,6,2⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨2,7,0⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨3,0,0⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨3,0,1⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨3,0,2⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨3,0,3⟩,[r98,r99,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨3,0,4⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨3,0,5⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨3,1,0⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨3,1,1⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨3,1,2⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨3,1,4⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨3,2,0⟩,[r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574]),(⟨3,2,1⟩,[0,0,r268,r692,r693,r694,r695,r696,r697,r698,r699,r700,-1572864]),(⟨3,2,2⟩,[r144,r212,r714,r715,r716,r717,r718,r719,r720,r721,r722,r723]),(⟨3,2,4⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨3,3,0⟩,[r98,r99,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨3,4,0⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨3,4,1⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨3,4,2⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨3,5,0⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨4,0,0⟩,[r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨4,0,1⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨4,0,2⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,0,3⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨4,0,4⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨4,0,5⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨4,0,6⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨4,1,0⟩,[0,0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨4,1,2⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨4,1,3⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨4,2,0⟩,[r503,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,2,1⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨4,2,2⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨4,2,3⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨4,2,4⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨4,3,0⟩,[r111,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638]),(⟨4,3,1⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨4,3,2⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨4,4,0⟩,[r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨4,4,2⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨4,5,0⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨4,6,0⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨5,0,0⟩,[r376,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨5,0,2⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨5,0,3⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨5,0,4⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨5,1,2⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨5,2,0⟩,[r519,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨5,2,1⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨5,3,0⟩,[0,0,r54,r639,r640,r641,r642,r643,r644,r645,-262144]),(⟨5,4,0⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨6,0,0⟩,[r111,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨6,0,2⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨6,0,4⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨6,2,0⟩,[r598,r308,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨6,2,2⟩,[r287,r288,r289,r290,r236,r291,r292,r293,131072]),(⟨6,4,0⟩,[r244,r646,r647,r648,r609,r649,r650,r651,65536]),(⟨7,0,2⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨7,2,0⟩,[r144,r608,r609,r610,r611,r612,r613,r614,r615,r616])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-384,8384,-78592,440960,-1705088,4764160,-9624448,13537664,-12357632,6218048,-613248]),(⟨0,0,1⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,0,2⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,0,3⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,1,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,1,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨0,2,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨1,0,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨1,1,0⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨2,0,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨2,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨4,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r724) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 8 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r724) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[-122880,4550656,-74997760,740642816,-4995252224,24811433984,-94876508160,285753331712,-683404689408,1293794136064,-1908029628416,2105896300544,-1576601780224,573799550976,176621002752,-261489332224,29396656128]),(⟨2,0,1⟩,[-20480,1110016,-23769088,283725824,-2199080960,12091551744,-49787056128,158103326720,-391955443712,758676672512,-1130163769344,1242018508800,-902594752512,285743337472,145630392320,-160184471552]),(⟨2,0,2⟩,[241664,-8167424,118837248,-997474304,5494288384,-21338087424,60054720512,-119683121152,150714028032,-55942406144,-205079023616,469169848320,-474055012352,222452211712,-6204821504]),(⟨2,0,3⟩,[57344,-2646016,48185344,-481312768,3064242176,-13549117440,43269718016,-99362635776,156336660480,-142200053760,-494321664,196498800640,-261414559744,144056786944]),(⟨2,0,4⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,0,5⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,1,0⟩,[-20480,1110016,-23769088,283725824,-2199080960,12091551744,-49787056128,158103326720,-391955443712,758676672512,-1130163769344,1242018508800,-902594752512,285743337472,145630392320,-160184471552]),(⟨2,1,1⟩,[0,0,655360,-19136512,225181696,-1387003904,4876795904,-9745989632,7751598080,16091971584,-66219278336,106750017536,-85835644928,9642967040,35047735296]),(⟨2,1,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,1,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,2,0⟩,[241664,-8167424,118837248,-997474304,5494288384,-21338087424,60054720512,-119683121152,150714028032,-55942406144,-205079023616,469169848320,-474055012352,222452211712,-6204821504]),(⟨2,2,1⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,2,2⟩,[-229376,7012352,-88342528,603783168,-2487189504,6311247872,-8153989120,-4893048832,41702227968,-74680172544,60283158528,-10261823488,-15858827264]),(⟨2,2,3⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,2,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,2,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[57344,-2646016,48185344,-481312768,3064242176,-13549117440,43269718016,-99362635776,156336660480,-142200053760,-494321664,196498800640,-261414559744,144056786944]),(⟨2,3,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,3,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,4,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,4,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,6,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[-69632,3215360,-62361600,697782272,-5199384576,28086030336,-115855577088,375610871808,-970208653312,2003745386496,-3284374040576,4166724677632,-3872882520064,2356575203328,-671124942848,-84750061568]),(⟨3,0,1⟩,[-8192,491520,-11100160,134512640,-1060544512,6214975488,-28962840576,107900633088,-317526532096,735959416832,-1333412765696,1836503433216,-1824468951040,1177549144064,-375999733760]),(⟨3,0,2⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨3,0,3⟩,[16384,-819200,15794176,-161579008,1063469056,-5226430464,20472135680,-62296621056,141730430976,-236606357504,278165389312,-210433179648,86162653184]),(⟨3,1,0⟩,[-8192,491520,-11100160,134512640,-1060544512,6214975488,-28962840576,107900633088,-317526532096,735959416832,-1333412765696,1836503433216,-1824468951040,1177549144064,-375999733760]),(⟨3,1,1⟩,[0,0,262144,-9175040,123994112,-859570176,3452436480,-8641839104,13114015744,-3411542016,-42283565056,114783682560,-149024407552,89935577088]),(⟨3,1,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,2,0⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨3,2,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,2,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,3,0⟩,[16384,-819200,15794176,-161579008,1063469056,-5226430464,20472135680,-62296621056,141730430976,-236606357504,278165389312,-210433179648,86162653184]),(⟨3,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,0,0⟩,[135168,-4349952,58257408,-428654592,1902809088,-4871593984,2478764032,38436700160,-197380820992,573614481408,-1168475664384,1722262437888,-1783629631488,1195280080896,-398570303488]),(⟨4,0,1⟩,[0,0,262144,-9175040,123994112,-859570176,3452436480,-8641839104,13114015744,-3411542016,-42283565056,114783682560,-149024407552,89935577088]),(⟨4,0,2⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,0,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,0,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,0⟩,[0,0,262144,-9175040,123994112,-859570176,3452436480,-8641839104,13114015744,-3411542016,-42283565056,114783682560,-149024407552,89935577088]),(⟨4,2,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,6,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨5,0,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨5,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,2,0⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨5,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨6,0,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨6,0,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,0,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,2,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,4,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨7,0,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨7,2,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-49152,2105344,-38592512,414056448,-3000303616,15994478592,-66068520960,217507545088,-578253209600,1245068713984,-2154210271232,2924706168832,-2970287767552,2070831865856,-816755335168,75434409984]),(⟨0,3,1⟩,[-8192,491520,-11755520,153649152,-1285726208,7601979392,-33839636480,117646622720,-325278130176,719867445248,-1267193487360,1729753415680,-1738633306112,1167906177024,-411047469056]),(⟨0,3,2⟩,[57344,-2269184,36945920,-337264640,2007441408,-8592580608,27916009472,-69954928640,135361536000,-198231547904,201317924864,-114887639040,8381194240,32017506304]),(⟨0,3,3⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨0,4,0⟩,[-8192,491520,-11755520,153649152,-1285726208,7601979392,-33839636480,117646622720,-325278130176,719867445248,-1267193487360,1729753415680,-1738633306112,1167906177024,-411047469056]),(⟨0,4,1⟩,[0,0,262144,-9175040,123994112,-859570176,3452436480,-8641839104,13114015744,-3411542016,-42283565056,114783682560,-149024407552,89935577088]),(⟨0,5,0⟩,[57344,-2269184,36945920,-337264640,2007441408,-8592580608,27916009472,-69954928640,135361536000,-198231547904,201317924864,-114887639040,8381194240,32017506304]),(⟨0,5,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,6,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨0,7,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,0,0⟩,[24576,-1249280,27152384,-347017216,3001118720,-19057029120,93600796672,-367561871360,1177112227840,-3106428637184,6775959482368,-12160697479168,17697185910784,-20296743424000,17459315634176,-10303274102784,3423854931968,-298637058048]),(⟨1,0,1⟩,[4096,-278528,7356416,-106528768,1003192320,-6838501376,36163141632,-154379255808,542438432768,-1579971428352,3804812918784,-7470388641792,11642109165568,-13829521915904,11784176812032,-6441462235136,1702022533120]),(⟨1,0,2⟩,[-28672,1363968,-26955776,305131520,-2292150272,12472733696,-51780833280,168055894016,-428140449792,843644858368,-1226858262528,1155229437952,-357540777984,-691251351552,1047708798976,-533951918080]),(⟨1,0,3⟩,[-8192,475136,-10788864,132710400,-1054744576,6122782720,-27949244416,102841450496,-305272676352,726504816640,-1356802482176,1909807316992,-1915525423104,1239447683072,-397569220608]),(⟨1,0,4⟩,[0,0,131072,-5373952,84279296,-693501952,3442737152,-10994581504,21234450432,-12000690176,-54040854528,157865607168,-195132784640,107420450816]),(⟨1,1,0⟩,[4096,-278528,7356416,-106528768,1003192320,-6838501376,36163141632,-154379255808,542438432768,-1579971428352,3804812918784,-7470388641792,11642109165568,-13829521915904,11784176812032,-6441462235136,1702022533120]),(⟨1,1,1⟩,[0,0,-262144,12320768,-225705984,2232156160,-13685489664,55905353728,-155579842560,274726387712,-172747915264,-572844670976,2012414214144,-3179970560000,2817126301696,-1170441502720]),(⟨1,1,2⟩,[0,0,458752,-14024704,178782208,-1262092288,5509152768,-14988083200,19885719552,17075798016,-117969715200,187461402624,-91699019776,-92777086976,120810962944]),(⟨1,1,3⟩,[0,0,131072,-5373952,84279296,-693501952,3442737152,-10994581504,21234450432,-12000690176,-54040854528,157865607168,-195132784640,107420450816]),(⟨1,2,0⟩,[-28672,1363968,-26955776,305131520,-2292150272,12472733696,-51780833280,168055894016,-428140449792,843644858368,-1226858262528,1155229437952,-357540777984,-691251351552,1047708798976,-533951918080]),(⟨1,2,1⟩,[0,0,458752,-14024704,178782208,-1262092288,5509152768,-14988083200,19885719552,17075798016,-117969715200,187461402624,-91699019776,-92777086976,120810962944]),(⟨1,2,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,2,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,3,0⟩,[-16384,966656,-22544384,286359552,-2340470784,13724762112,-61788880896,220488073216,-630550806528,1446372261888,-2623995969536,3639560732672,-3654158729216,2407353860096,-808616689664]),(⟨1,3,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,3,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,4,2⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,5,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,0,0⟩,[-118784,4272128,-67248128,620810240,-3796762624,16312250368,-49490354176,95916019712,-46020976640,-448070086656,1988050165760,-5003250110464,8850319998976,-11349079060480,10244563066880,-5922638336000,1656691240960]),(⟨2,0,1⟩,[-20480,1110016,-23965696,292704256,-2359775232,13643968512,-59063218176,194950877184,-491670827008,930231570432,-1232490172416,873029529600,376572809216,-1745449037824,1962683297792,-923428065280]),(⟨2,0,2⟩,[241664,-8167424,118837248,-997474304,5496385536,-21392613376,60589494272,-122048708608,154291769344,-48652705792,-239644282880,507270905856,-445187715072,109151477760,82888486912]),(⟨2,0,3⟩,[57344,-2646016,48185344,-481312768,3064242176,-13549117440,43269718016,-99362635776,156336660480,-142200053760,-494321664,196498800640,-261414559744,144056786944]),(⟨2,0,4⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,0,5⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,1,0⟩,[-20480,1110016,-23965696,292704256,-2359775232,13643968512,-59063218176,194950877184,-491670827008,930231570432,-1232490172416,873029529600,376572809216,-1745449037824,1962683297792,-923428065280]),(⟨2,1,1⟩,[0,0,655360,-19136512,229376000,-1496055808,5946343424,-14477164544,14907080704,30671372288,-135349796864,182952132608,-28101050368,-216958500864,213234352128]),(⟨2,1,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,1,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,2,0⟩,[241664,-8167424,118837248,-997474304,5496385536,-21392613376,60589494272,-122048708608,154291769344,-48652705792,-239644282880,507270905856,-445187715072,109151477760,82888486912]),(⟨2,2,1⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,2,2⟩,[-229376,7012352,-88342528,603783168,-2487189504,6311247872,-8153989120,-4893048832,41702227968,-74680172544,60283158528,-10261823488,-15858827264]),(⟨2,2,3⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,2,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,2,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨2,3,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,3,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,3,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,4,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,4,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,6,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,7,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,0,0⟩,[-98304,4579328,-89251840,999571456,-7426523136,39879024640,-163227082752,524608962560,-1342484643840,2744218755072,-4440810790912,5525809807360,-4963669950464,2814102036480,-623489540096,-211504070656]),(⟨3,0,1⟩,[-8192,491520,-10641408,120487936,-883859456,5007409152,-23988461568,95278137344,-301218553856,745745514496,-1416817221632,1985863778304,-1945035268096,1198072791040,-344282079232]),(⟨3,0,2⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨3,0,3⟩,[16384,-819200,15794176,-161579008,1063469056,-5226430464,20472135680,-62296621056,141730430976,-236606357504,278165389312,-210433179648,86162653184]),(⟨3,0,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,0,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,1,0⟩,[-8192,491520,-10641408,120487936,-883859456,5007409152,-23988461568,95278137344,-301218553856,745745514496,-1416817221632,1985863778304,-1945035268096,1198072791040,-344282079232]),(⟨3,1,1⟩,[0,0,262144,-9175040,123994112,-859570176,3452436480,-8641839104,13114015744,-3411542016,-42283565056,114783682560,-149024407552,89935577088]),(⟨3,1,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,1,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,2,0⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨3,2,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,2,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,3,0⟩,[32768,-1638400,32112640,-336789504,2260631552,-11044257792,41838706688,-122770817024,274819547136,-463687450624,563547602944,-449191542784,194598633472]),(⟨3,4,0⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,4,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,5,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,0,0⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨4,0,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,0,2⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,0,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,0,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,2,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,4,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,5,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,6,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨5,0,2⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,0,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,1,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,2,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,3,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨6,0,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨6,0,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,0,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,2,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,4,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨7,0,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨7,2,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[24576,-1249280,27152384,-347017216,3001118720,-19057029120,93600796672,-367561871360,1177112227840,-3106428637184,6775959482368,-12160697479168,17697185910784,-20296743424000,17459315634176,-10303274102784,3423854931968,-298637058048]),(⟨0,1,1⟩,[4096,-278528,7356416,-106528768,1003192320,-6838501376,36163141632,-154379255808,542438432768,-1579971428352,3804812918784,-7470388641792,11642109165568,-13829521915904,11784176812032,-6441462235136,1702022533120]),(⟨0,1,2⟩,[-28672,1363968,-26955776,305131520,-2292150272,12472733696,-51780833280,168055894016,-428140449792,843644858368,-1226858262528,1155229437952,-357540777984,-691251351552,1047708798976,-533951918080]),(⟨0,1,3⟩,[-8192,475136,-10788864,132710400,-1054744576,6122782720,-27949244416,102841450496,-305272676352,726504816640,-1356802482176,1909807316992,-1915525423104,1239447683072,-397569220608]),(⟨0,1,4⟩,[0,0,131072,-5373952,84279296,-693501952,3442737152,-10994581504,21234450432,-12000690176,-54040854528,157865607168,-195132784640,107420450816]),(⟨0,2,0⟩,[-118784,4272128,-67248128,620810240,-3796762624,16312250368,-49490354176,95916019712,-46020976640,-448070086656,1988050165760,-5003250110464,8850319998976,-11349079060480,10244563066880,-5922638336000,1656691240960]),(⟨0,2,1⟩,[-20480,1110016,-23965696,292704256,-2359775232,13643968512,-59063218176,194950877184,-491670827008,930231570432,-1232490172416,873029529600,376572809216,-1745449037824,1962683297792,-923428065280]),(⟨0,2,2⟩,[241664,-8167424,118837248,-997474304,5496385536,-21392613376,60589494272,-122048708608,154291769344,-48652705792,-239644282880,507270905856,-445187715072,109151477760,82888486912]),(⟨0,2,3⟩,[57344,-2646016,48185344,-481312768,3064242176,-13549117440,43269718016,-99362635776,156336660480,-142200053760,-494321664,196498800640,-261414559744,144056786944]),(⟨0,2,4⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨0,2,5⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨0,3,0⟩,[-98304,4579328,-89251840,999571456,-7426523136,39879024640,-163227082752,524608962560,-1342484643840,2744218755072,-4440810790912,5525809807360,-4963669950464,2814102036480,-623489540096,-211504070656]),(⟨0,3,1⟩,[-8192,491520,-10641408,120487936,-883859456,5007409152,-23988461568,95278137344,-301218553856,745745514496,-1416817221632,1985863778304,-1945035268096,1198072791040,-344282079232]),(⟨0,3,2⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨0,3,3⟩,[16384,-819200,15794176,-161579008,1063469056,-5226430464,20472135680,-62296621056,141730430976,-236606357504,278165389312,-210433179648,86162653184]),(⟨0,3,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨0,3,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨0,4,0⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨0,4,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨0,4,2⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨0,4,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨0,4,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨0,5,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨0,5,2⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨0,5,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨0,5,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,6,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨0,6,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨0,6,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨0,7,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,0,0⟩,[24576,-1249280,27152384,-347017216,3001118720,-19057029120,93600796672,-367561871360,1177112227840,-3106428637184,6775959482368,-12160697479168,17697185910784,-20296743424000,17459315634176,-10303274102784,3423854931968,-298637058048]),(⟨1,0,1⟩,[4096,-278528,7356416,-106528768,1003192320,-6838501376,36163141632,-154379255808,542438432768,-1579971428352,3804812918784,-7470388641792,11642109165568,-13829521915904,11784176812032,-6441462235136,1702022533120]),(⟨1,0,2⟩,[-28672,1363968,-26955776,305131520,-2292150272,12472733696,-51780833280,168055894016,-428140449792,843644858368,-1226858262528,1155229437952,-357540777984,-691251351552,1047708798976,-533951918080]),(⟨1,0,3⟩,[-8192,475136,-10788864,132710400,-1054744576,6122782720,-27949244416,102841450496,-305272676352,726504816640,-1356802482176,1909807316992,-1915525423104,1239447683072,-397569220608]),(⟨1,0,4⟩,[0,0,131072,-5373952,84279296,-693501952,3442737152,-10994581504,21234450432,-12000690176,-54040854528,157865607168,-195132784640,107420450816]),(⟨1,1,0⟩,[8192,-557056,15106048,-226361344,2201681920,-15337684992,81549295616,-344216567808,1179822145536,-3321835651072,7700892712960,-14579535052800,22069030944768,-25752400527360,21852118876160,-12102611238912,3329317117952]),(⟨1,1,1⟩,[0,0,-458752,21299200,-386400256,3784572928,-22961651712,92752904192,-255295225856,446281285632,-275074318336,-941833650176,3291581775872,-5211162935296,4634179207168,-1933685096448]),(⟨1,1,2⟩,[0,0,458752,-14024704,180879360,-1316618240,6043926528,-17353670656,23463460864,24365498368,-152534974464,225562460160,-62831722496,-206077820928,209904271360]),(⟨1,1,3⟩,[0,0,131072,-5373952,84279296,-693501952,3442737152,-10994581504,21234450432,-12000690176,-54040854528,157865607168,-195132784640,107420450816]),(⟨1,2,0⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨1,2,1⟩,[0,0,1114112,-33161216,406061056,-2703622144,10920722432,-27099660288,31215058944,40457469952,-218754252800,332312477696,-148667367424,-196434853888,244952006656]),(⟨1,2,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨1,2,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨1,2,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,2,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,3,0⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨1,3,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,3,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨1,3,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,4,2⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,5,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,0,0⟩,[-118784,4272128,-67248128,620810240,-3796762624,16312250368,-49490354176,95916019712,-46020976640,-448070086656,1988050165760,-5003250110464,8850319998976,-11349079060480,10244563066880,-5922638336000,1656691240960]),(⟨2,0,1⟩,[-20480,1110016,-23965696,292704256,-2359775232,13643968512,-59063218176,194950877184,-491670827008,930231570432,-1232490172416,873029529600,376572809216,-1745449037824,1962683297792,-923428065280]),(⟨2,0,2⟩,[241664,-8167424,118837248,-997474304,5496385536,-21392613376,60589494272,-122048708608,154291769344,-48652705792,-239644282880,507270905856,-445187715072,109151477760,82888486912]),(⟨2,0,3⟩,[57344,-2646016,48185344,-481312768,3064242176,-13549117440,43269718016,-99362635776,156336660480,-142200053760,-494321664,196498800640,-261414559744,144056786944]),(⟨2,0,4⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,0,5⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,1,0⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨2,1,1⟩,[0,0,1114112,-33161216,406061056,-2703622144,10920722432,-27099660288,31215058944,40457469952,-218754252800,332312477696,-148667367424,-196434853888,244952006656]),(⟨2,1,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,1,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,1,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨2,1,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,2,0⟩,[385024,-13008896,188850176,-1579778048,8684920832,-33866186752,96907894784,-201258631168,282189078528,-194905669632,-140926459904,499779928064,-490184040448,136525381632,95365652480]),(⟨2,2,1⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,2,2⟩,[-344064,10518528,-132513792,905674752,-3730784256,9466871808,-12230983680,-7339573248,62553341952,-112020258816,90424737792,-15392735232,-23788240896]),(⟨2,2,3⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,2,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,2,6⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,3,0⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨2,3,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,3,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,3,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,4,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨2,4,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨2,5,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,6,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,6,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,7,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,0,0⟩,[-98304,4579328,-89251840,999571456,-7426523136,39879024640,-163227082752,524608962560,-1342484643840,2744218755072,-4440810790912,5525809807360,-4963669950464,2814102036480,-623489540096,-211504070656]),(⟨3,0,1⟩,[-8192,491520,-10641408,120487936,-883859456,5007409152,-23988461568,95278137344,-301218553856,745745514496,-1416817221632,1985863778304,-1945035268096,1198072791040,-344282079232]),(⟨3,0,2⟩,[73728,-3104768,53198848,-507199488,3109773312,-13357031424,41882124288,-95747801088,152966914048,-147267624960,18006261760,172306907136,-241637154816,133816983552]),(⟨3,0,3⟩,[16384,-819200,15794176,-161579008,1063469056,-5226430464,20472135680,-62296621056,141730430976,-236606357504,278165389312,-210433179648,86162653184]),(⟨3,0,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,0,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,1,0⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨3,1,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨3,1,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,1,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,2,0⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨3,2,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,2,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨3,2,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,3,0⟩,[32768,-1638400,32112640,-336789504,2260631552,-11044257792,41838706688,-122770817024,274819547136,-463687450624,563547602944,-449191542784,194598633472]),(⟨3,4,0⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,4,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,5,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,0,0⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨4,0,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,0,2⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,0,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,0,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,1,2⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,2,0⟩,[-114688,3506176,-44171264,301891584,-1243594752,3155623936,-4076994560,-2446524416,20851113984,-37340086272,30141579264,-5130911744,-7929413632]),(⟨4,2,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,3,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,4,0⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,6,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨5,0,2⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,0,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,1,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,2,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,3,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨6,0,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨6,0,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,0,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,2,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,4,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨7,0,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨7,2,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[98304,-3989504,74076160,-845545472,6731624448,-40153145344,187668631552,-707075424256,2184861904896,-5588009967616,11862037901312,-20817816879104,29827183005696,-34029841850368,29608567844864,-18233421643776,6857600618496,-1088906510336,58322337792]),(⟨0,0,1⟩,[40960,-2195456,49512448,-651476992,5769609216,-37332041728,185888833536,-736319586304,2367876399104,-6252077268992,13608313847808,-24330441146368,35250477121536,-40260646617088,34535673659392,-20384912293888,6819392053248,-616439627776]),(⟨0,0,2⟩,[-233472,8552448,-138354688,1327808512,-8584732672,40116256768,-140443000832,370098290688,-706453258240,825193889792,46652170240,-2745958645760,7010834227200,-10501395546112,10233849421824,-6110310612992,1681445670912]),(⟨0,0,3⟩,[-131072,6144000,-120324096,1355464704,-10149691392,55037181952,-227804643328,741210243072,-1923091922944,3996030681088,-6604679675904,8465816633344,-7961278152704,4919236247552,-1465635504128,-127666470912]),(⟨0,0,4⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨0,0,5⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨0,0,6⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨0,1,0⟩,[40960,-2195456,49512448,-651476992,5769609216,-37332041728,185888833536,-736319586304,2367876399104,-6252077268992,13608313847808,-24330441146368,35250477121536,-40260646617088,34535673659392,-20384912293888,6819392053248,-616439627776]),(⟨0,1,1⟩,[8192,-557056,14581760,-209190912,1961033728,-13423247360,71867006976,-311328374784,1104124133376,-3214830043136,7674382614528,-14889817473024,22984110637056,-27189090418688,23206711558144,-12763193802752,3398851076096]),(⟨0,1,2⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨0,1,3⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨0,1,4⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨0,2,0⟩,[-233472,8552448,-138354688,1327808512,-8584732672,40116256768,-140443000832,370098290688,-706453258240,825193889792,46652170240,-2745958645760,7010834227200,-10501395546112,10233849421824,-6110310612992,1681445670912]),(⟨0,2,1⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨0,2,2⟩,[385024,-13008896,188850176,-1579778048,8684920832,-33866186752,96907894784,-201258631168,282189078528,-194905669632,-140926459904,499779928064,-490184040448,136525381632,95365652480]),(⟨0,2,3⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨0,2,4⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨0,2,5⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨0,2,6⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨0,2,7⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,3,0⟩,[-131072,6144000,-120324096,1355464704,-10149691392,55037181952,-227804643328,741210243072,-1923091922944,3996030681088,-6604679675904,8465816633344,-7961278152704,4919236247552,-1465635504128,-127666470912]),(⟨0,3,1⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨0,3,2⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨0,3,3⟩,[32768,-1638400,32112640,-336789504,2260631552,-11044257792,41838706688,-122770817024,274819547136,-463687450624,563547602944,-449191542784,194598633472]),(⟨0,3,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨0,3,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨0,4,0⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨0,4,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨0,4,2⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨0,4,3⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨0,4,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨0,4,5⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,4,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨0,5,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨0,5,2⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨0,5,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨0,5,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,6,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨0,6,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨0,6,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨0,7,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,0,0⟩,[40960,-2195456,49512448,-651476992,5769609216,-37332041728,185888833536,-736319586304,2367876399104,-6252077268992,13608313847808,-24330441146368,35250477121536,-40260646617088,34535673659392,-20384912293888,6819392053248,-616439627776]),(⟨1,0,1⟩,[8192,-557056,14581760,-209190912,1961033728,-13423247360,71867006976,-311328374784,1104124133376,-3214830043136,7674382614528,-14889817473024,22984110637056,-27189090418688,23206711558144,-12763193802752,3398851076096]),(⟨1,0,2⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨1,0,3⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨1,0,4⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,1,0⟩,[8192,-557056,14581760,-209190912,1961033728,-13423247360,71867006976,-311328374784,1104124133376,-3214830043136,7674382614528,-14889817473024,22984110637056,-27189090418688,23206711558144,-12763193802752,3398851076096]),(⟨1,1,1⟩,[0,0,-589824,26935296,-482082816,4657250304,-27828486144,110542651392,-299146149888,514664693760,-306979209216,-1106966937600,3837502685184,-6093577125888,5451158716416,-2289730781184]),(⟨1,1,2⟩,[0,0,1114112,-33161216,406061056,-2703622144,10920722432,-27099660288,31215058944,40457469952,-218754252800,332312477696,-148667367424,-196434853888,244952006656]),(⟨1,1,3⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,2,0⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨1,2,1⟩,[0,0,1114112,-33161216,406061056,-2703622144,10920722432,-27099660288,31215058944,40457469952,-218754252800,332312477696,-148667367424,-196434853888,244952006656]),(⟨1,2,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨1,2,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨1,2,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,2,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,3,0⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨1,3,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,3,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨1,3,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨1,4,2⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,5,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,0,0⟩,[-233472,8552448,-138354688,1327808512,-8584732672,40116256768,-140443000832,370098290688,-706453258240,825193889792,46652170240,-2745958645760,7010834227200,-10501395546112,10233849421824,-6110310612992,1681445670912]),(⟨2,0,1⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨2,0,2⟩,[385024,-13008896,188850176,-1579778048,8684920832,-33866186752,96907894784,-201258631168,282189078528,-194905669632,-140926459904,499779928064,-490184040448,136525381632,95365652480]),(⟨2,0,3⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨2,0,4⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨2,0,5⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨2,0,6⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,0,7⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,1,0⟩,[-49152,2473984,-50855936,594493440,-4586913792,25436962816,-106434723840,343948967936,-863946817536,1670704939008,-2388926922752,2232114659328,-714214621184,-1287922204672,2010318700544,-1050182074368]),(⟨2,1,1⟩,[0,0,1114112,-33161216,406061056,-2703622144,10920722432,-27099660288,31215058944,40457469952,-218754252800,332312477696,-148667367424,-196434853888,244952006656]),(⟨2,1,2⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,1,3⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,1,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨2,1,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,2,0⟩,[385024,-13008896,188850176,-1579778048,8684920832,-33866186752,96907894784,-201258631168,282189078528,-194905669632,-140926459904,499779928064,-490184040448,136525381632,95365652480]),(⟨2,2,1⟩,[16384,-835584,16252928,-169934848,1102331904,-4764450816,13966114816,-25792872448,17605378048,50963922944,-183311663104,287194546176,-250018349056,101799477248]),(⟨2,2,2⟩,[-344064,10518528,-132513792,905674752,-3730784256,9466871808,-12230983680,-7339573248,62553341952,-112020258816,90424737792,-15392735232,-23788240896]),(⟨2,2,3⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,2,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,2,6⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,3,0⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨2,3,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨2,3,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨2,3,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,4,0⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨2,4,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨2,4,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,4,3⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨2,5,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨2,6,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨2,6,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,7,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,0,0⟩,[-131072,6144000,-120324096,1355464704,-10149691392,55037181952,-227804643328,741210243072,-1923091922944,3996030681088,-6604679675904,8465816633344,-7961278152704,4919236247552,-1465635504128,-127666470912]),(⟨3,0,1⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨3,0,2⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨3,0,3⟩,[32768,-1638400,32112640,-336789504,2260631552,-11044257792,41838706688,-122770817024,274819547136,-463687450624,563547602944,-449191542784,194598633472]),(⟨3,0,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,0,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,1,0⟩,[-16384,966656,-21889024,267223040,-2115289088,12337758208,-56912084992,210742083584,-622799208448,1462464233472,-2690215247872,3746310750208,-3739994374144,2416996827136,-773568954368]),(⟨3,1,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨3,1,2⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,1,4⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,2,0⟩,[114688,-4915200,85131264,-818577408,5071683584,-22141698048,71185727488,-169317564416,291698196480,-340431601664,200823603200,81611161600,-253033365504,176074293248]),(⟨3,2,1⟩,[0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨3,2,2⟩,[-32768,1343488,-21069824,173375488,-860684288,2748645376,-5308612608,3000172544,13510213632,-39466401792,48783196160,-26855112704]),(⟨3,2,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,3,0⟩,[32768,-1638400,32112640,-336789504,2260631552,-11044257792,41838706688,-122770817024,274819547136,-463687450624,563547602944,-449191542784,194598633472]),(⟨3,4,0⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨3,4,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,5,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,0,0⟩,[126976,-3874816,47009792,-281919488,671379456,2458755072,-30444859392,153900646400,-518961475584,1290333200384,-2441873690624,3482709409792,-3578588737536,2414204116992,-827857178624]),(⟨4,0,1⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,0,2⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨4,0,3⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,0,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,0,5⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,0,6⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,0⟩,[0,0,393216,-14548992,208273408,-1553072128,6895173632,-19636420608,34348466176,-15412232192,-96324419584,272649289728,-344157192192,197356027904]),(⟨4,1,2⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,2,0⟩,[-49152,1490944,-18317312,120340480,-473972736,1128497152,-977862656,-3542581248,12675366912,-11618107392,-8272183296,20461862912,-10826661888]),(⟨4,2,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,2,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,2,3⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,3,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨4,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,4,0⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,6,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[98304,-4079616,68878336,-648642560,3969351680,-17377247232,57219612672,-143524691968,274092818432,-391395524608,384135266304,-205583384576,-3015016448,74274816000]),(⟨5,0,2⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,0,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,1,2⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[-16384,671744,-10502144,87441408,-455901184,1592295424,-3354296320,1829928960,9294888960,-23744659456,24632541184,-12019875840]),(⟨5,2,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,3,0⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨6,0,0⟩,[16384,-819200,16318464,-175210496,1197162496,-5817827328,21366571008,-60474195968,133089116160,-227081093120,285382213632,-238758363136,108435980288]),(⟨6,0,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,0,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,2,0⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨6,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,4,0⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨7,0,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨7,2,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712])]


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
    (Poly.add (Poly.scale (K.ofRat r725) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 8).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r724*r724 : ℚ)=r725 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 8 r724 r724 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=8 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 8).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C116

#print axioms Coulomb8.Columns.C116.sound
