import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C121

def r0 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -5079040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 12779520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -955613184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 6962577408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -5260673024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 2994208768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -450994339840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1088035586048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -298349395968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 461714948096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -243626180608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 4808270118912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -860790882304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 8132037836800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -8760584470528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 5457518821376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -1309606608896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 97581268992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2392064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 59146240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -780369920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 6515752960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -37581979648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 157846634496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -500129693696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1226684858368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2374141902848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 525699940352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -4706762129408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 795096678400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -7408895295488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 610252455936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -10800102932480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 5908068564992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -114084085760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 10387456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -158007296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1380220928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -7733903360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 4167925760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -74434543616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 120236310528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -81141497856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -142168588288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 72983838720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -756498726912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 740074586112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -1189271076864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 2779939930112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -3505527095296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 226566766592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 6258688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -135299072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 1522565120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -10517708800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 48597401600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -158417715200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 378716454912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -684298371072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 951917117440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -1049460047872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1131782176768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -1691644231680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 2363837415424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -31864619008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 13172441088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -4784128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 50987008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -214564864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -240812032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 6894977024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -36392992768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 112129736704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -33889550336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 360520941568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -396108234752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 408272896000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -711614365696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 1119358484480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -105299247104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -3866624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 10485760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -684982272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 3698130944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -12566331392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 28411691008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -44674580480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 2907373568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -37052547072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 40920154112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -106602168320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 96447430656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 6105399296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 16384000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -195821568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 1241645056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -4810866688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 12546473984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -23801102336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 4696309760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -588775424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 25143934976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -69110333440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 89305776128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 16449536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 2712993792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -2433613824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 4429643776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -248403984384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 639841665024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1316886282240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 2145982152704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -2774202580992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 3410605572096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -110686502912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 8466975227904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -8111177859072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 468433829888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -58359808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 677019648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -4733960192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 21897183232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -70701842432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 163746447360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -271798337536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 315879030784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -278738206720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 334087815168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -501624307712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 123745697792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 135678492672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -21220982784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -23592960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 48234496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -2668625920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 13450215424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -6763315200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 17776508928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -36058431488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 385702821888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -431816704000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 486173310976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -861710319616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 1194157539328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -97942241280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 94371840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -828375040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 209715200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -7063207936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 1455423488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 13350469632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1769996288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 666894336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -153131941888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1751121920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -15073280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 207618048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1576402944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 7293435904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -21213216768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 37299814400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -31462260736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -5927010304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 19040698368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 38670696448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -34395258880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -144688349184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 146125619200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 13388349440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -4653056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 93978624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -904265728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 4915658752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -16150757376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 32441630720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -38429523968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 26188120064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -3209625600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 58470301696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -91941634048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -13393395712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 19784466432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -393216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 279183360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -119013376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 746061824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 137101312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -6217531392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 1412300800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 831782912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 6685589504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -2094268416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -2359296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 198443008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -112197632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 1143996416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 1527250944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -6331826176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 1894776832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 429916160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 8593866752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -185860096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 32768000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -391643136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 2481192960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -1367343104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 24665128960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -46243250176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 66171961344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -4012900352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 62543626240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -120252268544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 148913782784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -248512512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 2695888896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -15624830976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 7323254784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -87218454528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 736100352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 5366611968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -62678630400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 11415846912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -1685213675520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 519507542016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -3089104896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -15728640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 189792256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -1188036608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 585629696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -7220494336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 3688890368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 5693767680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -23408934912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 121405177856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -225472151552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -5870977024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 350748672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 20578304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -31326208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 173932544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -3584425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 4029939712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 6245056512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -23237230592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 14585167872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 17550147584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 14660534272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -15691546624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 114950144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 50331648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -25165824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1358954496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 423624704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -10519314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 12255756288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 150994944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 66453504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -614858752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 3657695232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -13978828800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 31785222144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -27421048832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -8738439168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 223243272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -287253331968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 160762560512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -244318208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 61210624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -69861376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 2452881408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -8106803200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 1009516544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -15693774848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -31827820544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 133082513408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -184611373056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 811466752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 1048576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -187564032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 958398464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -2397306880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 2076180480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 3592683520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -2162163712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 25170935808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -1571815424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -14024704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 8650752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 621805568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -1891106816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 2994208768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -1452277760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -8475639808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 29689118720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -251920384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -2539520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 6389760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -477806592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 3481288704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -2630336512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1497104384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -225497169920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 544017793024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -149174697984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 230857474048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -121813090304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 2404135059456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -430395441152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 4066018918400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -4380292235264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 2728759410688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -654803304448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 48790634496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -1196032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 29573120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -390184960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 3257876480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -18790989824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 78923317248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -250064846848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 613342429184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -1187070951424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 262849970176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -2353381064704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 397548339200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -3704447647744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 305126227968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -5400051466240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 2954034282496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -57042042880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 5193728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -79003648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 690110464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -3866951680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 2083962880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -37217271808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 60118155264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -40570748928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -71084294144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 36491919360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -378249363456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 370037293056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -594635538432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 1389969965056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -1752763547648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 113283383296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 3129344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -67649536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 761282560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -5258854400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 24298700800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -79208857600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 189358227456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -342149185536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 475958558720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -524730023936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 565891088384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -845822115840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 1181918707712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -15932309504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 6586220544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 25493504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -107282432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -120406016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 3447488512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -18196496384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 56064868352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -16944775168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 180260470784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -198054117376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 204136448000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -355807182848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 559679242240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -52649623552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 5242880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -342491136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 1849065472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -6283165696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 14205845504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -22337290240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 1453686784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -18526273536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 20460077056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -53301084160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 48223715328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 3052699648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 8192000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -97910784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 620822528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -2405433344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 6273236992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -11900551168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 2348154880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -294387712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 12571967488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -34555166720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 44652888064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 8224768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -1179648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 1356496896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -1216806912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 2214821888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -124201992192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 319920832512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -658443141120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 1072991076352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -1387101290496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 1705302786048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -55343251456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 4233487613952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -4055588929536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 234216914944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -29179904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 338509824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -2366980096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 10948591616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -35350921216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 81873223680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -135899168768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 157939515392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -139369103360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 167043907584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -250812153856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 61872848896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 67839246336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -10610491392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -11796480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 24117248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -1334312960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 6725107712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -3381657600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 8888254464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -18029215744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 192851410944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -215908352000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 243086655488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -430855159808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 597078769664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -48971120640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 47185920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -414187520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 104857600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -3531603968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 727711744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 6675234816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -884998144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 333447168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -76565970944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 875560960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -7536640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 103809024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -788201472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 3646717952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -10606608384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 18649907200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -15731130368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -2963505152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 9520349184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 19335348224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -17197629440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -72344174592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 73062809600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 6694174720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -2326528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 46989312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -452132864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 2457829376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -8075378688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 16220815360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -19214761984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 13094060032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -1604812800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 29235150848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -45970817024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -6696697856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 9892233216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 373030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 68550656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -3108765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 706150400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 415891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 3342794752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -1047134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -1179648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 1240596480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -683671552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 12332564480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -23121625088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 33085980672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -2006450176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 31271813120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -60126134272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 74456891392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 1347944448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -7812415488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 3661627392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -43609227264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 368050176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 2683305984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -31339315200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 5707923456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -842606837760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 259753771008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -1544552448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -7864320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 94896128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -594018304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 292814848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -3610247168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 1844445184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 2846883840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -11704467456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 60702588928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -112736075776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -2935488512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 175374336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 10289152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -15663104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 86966272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -1792212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 2014969856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 3122528256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -11618615296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 7292583936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 8775073792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 7330267136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -7845773312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 57475072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 33226752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -307429376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 1828847616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -6989414400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 15892611072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -13710524416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -4369219584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 111621636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -143626665984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 80381280256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -122159104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 30605312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -34930688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 1226440704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -4053401600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 504758272, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -7846887424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -15913910272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 66541256704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -92305686528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 405733376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 524288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -93782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 479199232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -1198653440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 1038090240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 1796341760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -1081081856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 12585467904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := -785907712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -7012352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 310902784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -945553408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 1497104384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -726138880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -4237819904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 14844559360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -125960192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18],[r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98],[0,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[],[],[],[],[],[],[0,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142],[0,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156],[0,0,0,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167],[],[],[],[],[],[],[],[r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182],[r85,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195],[r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208],[0,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219],[],[],[],[],[],[0,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244],[0,0,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257],[0,0,0,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167],[],[],[],[],[],[],[],[0,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270],[0,0,0,0,r271,r272,r273,r274,r275,r276,r277,r278,-2097152],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r0,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290],[r0,r279,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300],[r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311],[r312,r313,r314,r315,r316,r317,r318,r319,r320,r321],[],[],[],[0,0,r271,r272,r273,r274,r275,r276,r277,r278,-2097152],[],[],[],[],[r245,r322,r323,r324,r314,r325,r326,r327,524288],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r85,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345]),(⟨0,0,1⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,0,2⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,0,3⟩,[r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨0,0,4⟩,[r397,r20,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,0,5⟩,[r19,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,0,6⟩,[0,r312,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨0,1,0⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,1,1⟩,[0,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨0,1,2⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,1,3⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨0,1,4⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨0,2,0⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,2,1⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,2,2⟩,[r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505]),(⟨0,2,3⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,2,4⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨0,2,5⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,3,0⟩,[r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨0,3,1⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨0,3,2⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨0,3,3⟩,[0,r99,r100,r101,r542,r543,r544,r545,r546,r547,r548,r549,r550]),(⟨0,4,0⟩,[r397,r20,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,4,1⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨0,4,2⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨0,5,0⟩,[r19,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,5,2⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,6,0⟩,[0,r312,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨1,0,0⟩,[r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨1,0,1⟩,[0,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨1,0,2⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,0,3⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨1,0,4⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨1,1,0⟩,[0,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨1,1,1⟩,[0,0,0,r551,r552,r553,r554,r555,r556,r557,r558,r559,r560,r561,r562,r563]),(⟨1,1,2⟩,[0,0,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨1,1,3⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨1,2,0⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,2,1⟩,[0,0,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨1,2,2⟩,[0,r111,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨1,2,3⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨1,3,0⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨1,3,1⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨1,3,2⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨1,4,0⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨2,0,0⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨2,0,1⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨2,0,2⟩,[r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505]),(⟨2,0,3⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨2,0,4⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨2,0,5⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨2,1,0⟩,[r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨2,1,1⟩,[0,0,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨2,1,2⟩,[0,r111,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨2,1,3⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨2,2,0⟩,[r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505]),(⟨2,2,1⟩,[0,r111,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586,r587,r588]),(⟨2,2,2⟩,[r85,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,2,3⟩,[r85,r596,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨2,2,4⟩,[r618,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨2,2,5⟩,[r196,r629,r630,r631,r632,r633,r634,r635,r636,r637]),(⟨2,3,0⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨2,3,1⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨2,3,2⟩,[r85,r596,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨2,3,3⟩,[0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨2,4,0⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨2,4,2⟩,[r618,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨2,4,4⟩,[r564,r638,r639,r640,r630,r641,r642,r643,262144]),(⟨2,5,0⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨2,5,2⟩,[r196,r629,r630,r631,r632,r633,r634,r635,r636,r637]),(⟨3,0,0⟩,[r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨3,0,1⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨3,0,2⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨3,0,3⟩,[0,r99,r100,r101,r542,r543,r544,r545,r546,r547,r548,r549,r550]),(⟨3,1,0⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨3,1,1⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨3,1,2⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨3,2,0⟩,[r19,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨3,2,1⟩,[0,0,0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨3,2,2⟩,[r85,r596,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨3,2,3⟩,[0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨3,3,0⟩,[0,r99,r100,r101,r542,r543,r544,r545,r546,r547,r548,r549,r550]),(⟨3,3,2⟩,[0,0,r220,r589,r590,r591,r592,r593,r594,r595,-1048576]),(⟨4,0,0⟩,[r397,r20,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨4,0,1⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨4,0,2⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨4,1,0⟩,[0,0,0,r271,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨4,2,0⟩,[r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨4,2,2⟩,[r618,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨4,2,4⟩,[r564,r638,r639,r640,r630,r641,r642,r643,262144]),(⟨4,4,2⟩,[r564,r638,r639,r640,r630,r641,r642,r643,262144]),(⟨5,0,0⟩,[r19,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨5,0,2⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,2,0⟩,[0,r245,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,2,2⟩,[r196,r629,r630,r631,r632,r633,r634,r635,r636,r637]),(⟨6,0,0⟩,[0,r312,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r644) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r644) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[-81920,2883584,-44711936,406929408,-2438283264,10178035712,-30391222272,65530150912,-102527451136,119492771840,-120006557696,153733480448,-254416896000,297576464384,-106398859264,-89648709632,24592318464]),(⟨2,0,1⟩,[0,491520,-14434304,180862976,-1284702208,5786075136,-17505533952,36807819264,-55195992064,62603558912,-69066735616,109486358528,-183569809408,182861266944,-30113513472,-75335450624]),(⟨2,0,2⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11129290752,-6068633600,-11543396352,16546496512,12338331648,-17911382016,-59167588352,95073959936,-14082539520]),(⟨2,0,3⟩,[0,-1048576,26968064,-283869184,1596227584,-5159813120,9279045632,-7202865152,-1227292672,-1708720128,22841753600,-22903619584,-34764849152,65277886464]),(⟨2,0,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,0,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,1,0⟩,[0,491520,-14434304,180862976,-1284702208,5786075136,-17505533952,36807819264,-55195992064,62603558912,-69066735616,109486358528,-183569809408,182861266944,-30113513472,-75335450624]),(⟨2,1,1⟩,[0,0,0,0,1310720,-35651584,375128064,-1916796928,4794613760,-4152360960,-7185367040,30270291968,-50341871616,22005415936,23365156864]),(⟨2,1,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,2,0⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11129290752,-6068633600,-11543396352,16546496512,12338331648,-17911382016,-59167588352,95073959936,-14082539520]),(⟨2,2,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,2,2⟩,[-131072,3932160,-46792704,279183360,-833093632,746061824,2330722304,-6217531392,1412300800,5822480384,6685589504,-14659878912,-1965293568]),(⟨2,2,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,3,0⟩,[0,-1048576,26968064,-283869184,1596227584,-5159813120,9279045632,-7202865152,-1227292672,-1708720128,22841753600,-22903619584,-34764849152,65277886464]),(⟨2,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,3,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,5,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,0,0⟩,[-32768,1835008,-37699584,412303360,-2790981632,12669779968,-40536817664,94701862912,-166164987904,224658784256,-249640566784,295520616448,-466153373696,622959624192,-382090428416,-12229394432]),(⟨3,0,1⟩,[0,196608,-6914048,97976320,-767623168,3791781888,-12741148672,30883053568,-56983683072,83234848768,-102770311168,144535912448,-254751604736,318249893888,-169952247808]),(⟨3,0,2⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨3,0,3⟩,[0,-262144,8192000,-97910784,619773952,-2380267520,6059327488,-11221073920,16648896512,-19684655104,18699845632,-25570967552,29804003328]),(⟨3,1,0⟩,[0,196608,-6914048,97976320,-767623168,3791781888,-12741148672,30883053568,-56983683072,83234848768,-102770311168,144535912448,-254751604736,318249893888,-169952247808]),(⟨3,1,1⟩,[0,0,0,0,524288,-17301504,211812352,-1243611136,3782213632,-5988417536,2904555520,16951279616,-59378237440,59957051392]),(⟨3,1,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨3,2,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,0⟩,[0,-262144,8192000,-97910784,619773952,-2380267520,6059327488,-11221073920,16648896512,-19684655104,18699845632,-25570967552,29804003328]),(⟨4,0,0⟩,[81920,-2523136,30638080,-185991168,539869184,-44204032,-5599854592,23238017024,-54054043648,83078971392,-87740678144,93940744192,-193074806784,310170124288,-191771181056]),(⟨4,0,1⟩,[0,0,0,0,524288,-17301504,211812352,-1243611136,3782213632,-5988417536,2904555520,16951279616,-59378237440,59957051392]),(⟨4,0,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,0⟩,[0,0,0,0,524288,-17301504,211812352,-1243611136,3782213632,-5988417536,2904555520,16951279616,-59378237440,59957051392]),(⟨4,2,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,2,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨5,0,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨6,0,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-32768,1343488,-23265280,231440384,-1506279424,6883704832,-23031283712,57894043648,-110968995840,162055225344,-180573831168,186034257920,-282583564288,440098357248,-351976914944,63106056192]),(⟨0,3,1⟩,[0,196608,-6914048,97976320,-768933888,3827433472,-13116276736,32799850496,-61778296832,87387209728,-95584944128,114265620480,-204409733120,296244477952,-193317404672]),(⟨0,3,2⟩,[32768,-1277952,20021248,-168263680,861601792,-2915565568,6941769728,-12011896832,14321352704,-9524969472,6393397248,-23067197440,28068151296,3967746048]),(⟨0,3,3⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064]),(⟨0,4,0⟩,[0,196608,-6914048,97976320,-768933888,3827433472,-13116276736,32799850496,-61778296832,87387209728,-95584944128,114265620480,-204409733120,296244477952,-193317404672]),(⟨0,4,1⟩,[0,0,0,0,524288,-17301504,211812352,-1243611136,3782213632,-5988417536,2904555520,16951279616,-59378237440,59957051392]),(⟨0,5,0⟩,[32768,-1277952,20021248,-168263680,861601792,-2915565568,6941769728,-12011896832,14321352704,-9524969472,6393397248,-23067197440,28068151296,3967746048]),(⟨0,6,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064]),(⟨1,0,0⟩,[16384,-802816,16629760,-199884800,1591705600,-9021571072,38004506624,-122368622592,306999132160,-607870369792,956575203328,-1214351015936,1364500447232,-1715445612544,2434503032832,-2667109875712,1552726933504,-249830375424]),(⟨1,0,1⟩,[0,-98304,3981312,-65994752,621363200,-3834413056,16974594048,-57826738176,158891655168,-352424984576,599823892480,-744028569600,778257285120,-1154960818176,1950438735872,-1985348894720,827838742528]),(⟨1,0,2⟩,[-16384,770048,-14745600,157646848,-1082015744,5151768576,-17676304384,43690459136,-74226647040,76834357248,-39033307136,38833651712,-134687539200,130559459328,118577758208,-207214837760]),(⟨1,0,3⟩,[0,131072,-4882432,70844416,-566689792,2933325824,-10930454528,31334727680,-69220827136,109616562176,-113138040832,98550743040,-176103555072,278828875776,-172845596672]),(⟨1,0,4⟩,[0,0,0,-2097152,46661632,-396886016,1570766848,-2287992832,-3054501888,12663652352,-3789553664,-14617149440,-17187733504,44234702848]),(⟨1,1,0⟩,[0,-98304,3981312,-65994752,621363200,-3834413056,16974594048,-57826738176,158891655168,-352424984576,599823892480,-744028569600,778257285120,-1154960818176,1950438735872,-1985348894720,827838742528]),(⟨1,1,1⟩,[0,0,0,3145728,-82575360,887881728,-5039194112,15712649216,-22596288512,-6478626816,61679861760,-39616774144,-2755395584,-310190014464,825773785088,-620377669632]),(⟨1,1,2⟩,[0,0,262144,-7864320,93585408,-558366720,1670381568,-1592786944,-3805806592,9717153792,-3671851008,9393668096,-37882691584,-6617038848,63326126080]),(⟨1,1,3⟩,[0,0,0,-2097152,46661632,-396886016,1570766848,-2287992832,-3054501888,12663652352,-3789553664,-14617149440,-17187733504,44234702848]),(⟨1,2,0⟩,[-16384,770048,-14745600,157646848,-1082015744,5151768576,-17676304384,43690459136,-74226647040,76834357248,-39033307136,38833651712,-134687539200,130559459328,118577758208,-207214837760]),(⟨1,2,1⟩,[0,0,262144,-7864320,93585408,-558366720,1670381568,-1592786944,-3805806592,9717153792,-3671851008,9393668096,-37882691584,-6617038848,63326126080]),(⟨1,3,0⟩,[0,327680,-11796480,168820736,-1335623680,6760759296,-24046731264,64134578176,-130999123968,197003771904,-208722984960,212816363520,-380513288192,575073353728,-366163001344]),(⟨1,3,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨1,4,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨2,0,0⟩,[-81920,2785280,-40468480,332546048,-1702100992,5462556672,-9300180992,-3749920768,70815678464,-218959413248,402746736640,-506876149760,541816651776,-847730376704,1562029817856,-1750404349952,789916008448]),(⟨2,0,1⟩,[0,491520,-14434304,182435840,-1326120960,6235389952,-20109672448,45351616512,-69732401152,68615045120,-53861335040,99039920128,-151224909824,-98007678976,575978618880,-504206180352]),(⟨2,0,2⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11133485056,-6169296896,-10687758336,13828587520,11491082240,3127246848,-83679100928,59137163264,45312999424]),(⟨2,0,3⟩,[0,-1048576,26968064,-283869184,1596227584,-5159813120,9279045632,-7202865152,-1227292672,-1708720128,22841753600,-22903619584,-34764849152,65277886464]),(⟨2,0,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,0,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,1,0⟩,[0,491520,-14434304,182435840,-1326120960,6235389952,-20109672448,45351616512,-69732401152,68615045120,-53861335040,99039920128,-151224909824,-98007678976,575978618880,-504206180352]),(⟨2,1,1⟩,[0,0,0,0,1310720,-35651584,383516672,-2118123520,6505889792,-9588178944,-8879865856,72347549696,-99364896768,-49868177408,142156234752]),(⟨2,1,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,2,0⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11133485056,-6169296896,-10687758336,13828587520,11491082240,3127246848,-83679100928,59137163264,45312999424]),(⟨2,2,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,2,2⟩,[-131072,3932160,-46792704,279183360,-833093632,746061824,2330722304,-6217531392,1412300800,5822480384,6685589504,-14659878912,-1965293568]),(⟨2,2,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,3,0⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨2,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,3,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,5,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,5,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨3,0,0⟩,[-49152,2605056,-52445184,568377344,-3831840768,17382981632,-55778066432,131223470080,-232331755520,313983254528,-335148335104,363524603904,-565740617728,782840152064,-483194322944,-27937292288]),(⟨3,0,1⟩,[0,196608,-6651904,90112000,-674037760,3233415168,-11074961408,29390929920,-61645127680,95669911552,-105594912768,132890951680,-268122783744,347569651712,-166021660672]),(⟨3,0,2⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨3,0,3⟩,[0,-262144,8192000,-97910784,619773952,-2380267520,6059327488,-11221073920,16648896512,-19684655104,18699845632,-25570967552,29804003328]),(⟨3,1,0⟩,[0,196608,-6651904,90112000,-674037760,3233415168,-11074961408,29390929920,-61645127680,95669911552,-105594912768,132890951680,-268122783744,347569651712,-166021660672]),(⟨3,1,1⟩,[0,0,0,0,524288,-17301504,211812352,-1243611136,3782213632,-5988417536,2904555520,16951279616,-59378237440,59957051392]),(⟨3,1,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨3,2,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,2⟩,[65536,-2686976,42270720,-343736320,1619132416,-4625399808,7817265152,-4680974336,-16861298688,62886969344,-96602619904,59340947456]),(⟨3,2,3⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,0⟩,[0,-524288,16384000,-195821568,1240596480,-4785700864,12332564480,-23121625088,33085980672,-34109652992,31271813120,-60126134272,74456891392]),(⟨3,3,2⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,0,0⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨4,0,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,0,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,2,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,2,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨5,0,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨6,0,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[16384,-802816,16629760,-199884800,1591705600,-9021571072,38004506624,-122368622592,306999132160,-607870369792,956575203328,-1214351015936,1364500447232,-1715445612544,2434503032832,-2667109875712,1552726933504,-249830375424]),(⟨0,1,1⟩,[0,-98304,3981312,-65994752,621363200,-3834413056,16974594048,-57826738176,158891655168,-352424984576,599823892480,-744028569600,778257285120,-1154960818176,1950438735872,-1985348894720,827838742528]),(⟨0,1,2⟩,[-16384,770048,-14745600,157646848,-1082015744,5151768576,-17676304384,43690459136,-74226647040,76834357248,-39033307136,38833651712,-134687539200,130559459328,118577758208,-207214837760]),(⟨0,1,3⟩,[0,131072,-4882432,70844416,-566689792,2933325824,-10930454528,31334727680,-69220827136,109616562176,-113138040832,98550743040,-176103555072,278828875776,-172845596672]),(⟨0,1,4⟩,[0,0,0,-2097152,46661632,-396886016,1570766848,-2287992832,-3054501888,12663652352,-3789553664,-14617149440,-17187733504,44234702848]),(⟨0,2,0⟩,[-81920,2785280,-40468480,332546048,-1702100992,5462556672,-9300180992,-3749920768,70815678464,-218959413248,402746736640,-506876149760,541816651776,-847730376704,1562029817856,-1750404349952,789916008448]),(⟨0,2,1⟩,[0,491520,-14434304,182435840,-1326120960,6235389952,-20109672448,45351616512,-69732401152,68615045120,-53861335040,99039920128,-151224909824,-98007678976,575978618880,-504206180352]),(⟨0,2,2⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11133485056,-6169296896,-10687758336,13828587520,11491082240,3127246848,-83679100928,59137163264,45312999424]),(⟨0,2,3⟩,[0,-1048576,26968064,-283869184,1596227584,-5159813120,9279045632,-7202865152,-1227292672,-1708720128,22841753600,-22903619584,-34764849152,65277886464]),(⟨0,2,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,2,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,3,0⟩,[-49152,2605056,-52445184,568377344,-3831840768,17382981632,-55778066432,131223470080,-232331755520,313983254528,-335148335104,363524603904,-565740617728,782840152064,-483194322944,-27937292288]),(⟨0,3,1⟩,[0,196608,-6651904,90112000,-674037760,3233415168,-11074961408,29390929920,-61645127680,95669911552,-105594912768,132890951680,-268122783744,347569651712,-166021660672]),(⟨0,3,2⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨0,3,3⟩,[0,-262144,8192000,-97910784,619773952,-2380267520,6059327488,-11221073920,16648896512,-19684655104,18699845632,-25570967552,29804003328]),(⟨0,4,0⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨0,4,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨0,4,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,5,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨0,5,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,6,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064]),(⟨1,0,0⟩,[16384,-802816,16629760,-199884800,1591705600,-9021571072,38004506624,-122368622592,306999132160,-607870369792,956575203328,-1214351015936,1364500447232,-1715445612544,2434503032832,-2667109875712,1552726933504,-249830375424]),(⟨1,0,1⟩,[0,-98304,3981312,-65994752,621363200,-3834413056,16974594048,-57826738176,158891655168,-352424984576,599823892480,-744028569600,778257285120,-1154960818176,1950438735872,-1985348894720,827838742528]),(⟨1,0,2⟩,[-16384,770048,-14745600,157646848,-1082015744,5151768576,-17676304384,43690459136,-74226647040,76834357248,-39033307136,38833651712,-134687539200,130559459328,118577758208,-207214837760]),(⟨1,0,3⟩,[0,131072,-4882432,70844416,-566689792,2933325824,-10930454528,31334727680,-69220827136,109616562176,-113138040832,98550743040,-176103555072,278828875776,-172845596672]),(⟨1,0,4⟩,[0,0,0,-2097152,46661632,-396886016,1570766848,-2287992832,-3054501888,12663652352,-3789553664,-14617149440,-17187733504,44234702848]),(⟨1,1,0⟩,[0,-196608,8224768,-140378112,1357545472,-8549892096,38065635328,-127106809856,332234784768,-690877169664,1122577186816,-1404638199808,1574490832896,-2300267659264,3618867412992,-3646104535040,1593162432512]),(⟨1,1,1⟩,[0,0,0,4718592,-123994112,1337196544,-7643332608,24256446464,-37132697600,-467140608,76885262336,-50063212544,29589504000,-591058960384,1431865917440,-1049248399360]),(⟨1,1,2⟩,[0,0,262144,-7864320,93585408,-558366720,1674575872,-1693450240,-2950168576,6999244800,-4519100416,30432296960,-62394204160,-42553835520,122721665024]),(⟨1,1,3⟩,[0,0,0,-2097152,46661632,-396886016,1570766848,-2287992832,-3054501888,12663652352,-3789553664,-14617149440,-17187733504,44234702848]),(⟨1,2,0⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨1,2,1⟩,[0,0,262144,-7864320,94896128,-594018304,2049703936,-3610247168,1844445184,2846883840,-11704467456,60702588928,-112736075776,-20548419584,146086821888]),(⟨1,2,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,2,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,3,0⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨1,3,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨1,3,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨2,0,0⟩,[-81920,2785280,-40468480,332546048,-1702100992,5462556672,-9300180992,-3749920768,70815678464,-218959413248,402746736640,-506876149760,541816651776,-847730376704,1562029817856,-1750404349952,789916008448]),(⟨2,0,1⟩,[0,491520,-14434304,182435840,-1326120960,6235389952,-20109672448,45351616512,-69732401152,68615045120,-53861335040,99039920128,-151224909824,-98007678976,575978618880,-504206180352]),(⟨2,0,2⟩,[147456,-4816896,66256896,-504233984,2337914880,-6734970880,11133485056,-6169296896,-10687758336,13828587520,11491082240,3127246848,-83679100928,59137163264,45312999424]),(⟨2,0,3⟩,[0,-1048576,26968064,-283869184,1596227584,-5159813120,9279045632,-7202865152,-1227292672,-1708720128,22841753600,-22903619584,-34764849152,65277886464]),(⟨2,0,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,0,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,1,0⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨2,1,1⟩,[0,0,262144,-7864320,94896128,-594018304,2049703936,-3610247168,1844445184,2846883840,-11704467456,60702588928,-112736075776,-20548419584,146086821888]),(⟨2,1,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,2,0⟩,[229376,-7536640,103809024,-788201472,3646717952,-10606608384,18649907200,-15731130368,-2963505152,9520349184,19335348224,-17197629440,-72344174592,73062809600,46859223040]),(⟨2,2,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,2,2⟩,[-196608,5898240,-70189056,418775040,-1249640448,1119092736,3496083456,-9326297088,2118451200,8733720576,10028384256,-21989818368,-2947940352]),(⟨2,2,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,3,0⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨2,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,3,2⟩,[65536,-2162688,30605312,-244514816,1226440704,-4053401600,8580890624,-7846887424,-15913910272,66541256704,-92305686528,48282271744]),(⟨2,3,3⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,4,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,4,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨2,4,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,5,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,5,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨3,0,0⟩,[-49152,2605056,-52445184,568377344,-3831840768,17382981632,-55778066432,131223470080,-232331755520,313983254528,-335148335104,363524603904,-565740617728,782840152064,-483194322944,-27937292288]),(⟨3,0,1⟩,[0,196608,-6651904,90112000,-674037760,3233415168,-11074961408,29390929920,-61645127680,95669911552,-105594912768,132890951680,-268122783744,347569651712,-166021660672]),(⟨3,0,2⟩,[32768,-1671168,30310400,-277905408,1470365696,-4707778560,8956739584,-8889368576,2702737408,-2232385536,15168471040,-15736930304,-26852261888,51844481024]),(⟨3,0,3⟩,[0,-262144,8192000,-97910784,619773952,-2380267520,6059327488,-11221073920,16648896512,-19684655104,18699845632,-25570967552,29804003328]),(⟨3,1,0⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨3,1,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨3,1,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨3,2,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,2⟩,[65536,-2162688,30605312,-244514816,1226440704,-4053401600,8580890624,-7846887424,-15913910272,66541256704,-92305686528,48282271744]),(⟨3,2,3⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,0⟩,[0,-524288,16384000,-195821568,1240596480,-4785700864,12332564480,-23121625088,33085980672,-34109652992,31271813120,-60126134272,74456891392]),(⟨3,3,2⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,0,0⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨4,0,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,0,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,2,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,2,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨5,0,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨6,0,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[65536,-2539520,44728320,-477806592,3481288704,-18412355584,73358114816,-225497169920,544017793024,-1044222885888,1616002318336,-2070822535168,2404135059456,-3012768088064,4066018918400,-4380292235264,2728759410688,-654803304448,48790634496]),(⟨0,0,1⟩,[16384,-1196032,29573120,-390184960,3257876480,-18790989824,78923317248,-250064846848,613342429184,-1187070951424,1839949791232,-2353381064704,2782838374400,-3704447647744,5187145875456,-5400051466240,2954034282496,-399294300160]),(⟨0,0,2⟩,[-147456,5193728,-79003648,690110464,-3866951680,14587740160,-37217271808,60118155264,-40570748928,-71084294144,255443435520,-378249363456,370037293056,-594635538432,1389969965056,-1752763547648,792983683072]),(⟨0,0,3⟩,[-49152,3129344,-67649536,761282560,-5258854400,24298700800,-79208857600,189358227456,-342149185536,475958558720,-524730023936,565891088384,-845822115840,1181918707712,-780683165696,6586220544]),(⟨0,0,4⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨0,0,5⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨0,0,6⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064]),(⟨0,1,0⟩,[16384,-1196032,29573120,-390184960,3257876480,-18790989824,78923317248,-250064846848,613342429184,-1187070951424,1839949791232,-2353381064704,2782838374400,-3704447647744,5187145875456,-5400051466240,2954034282496,-399294300160]),(⟨0,1,1⟩,[0,-196608,8224768,-140378112,1356496896,-8517648384,37651972096,-124201992192,319920832512,-658443141120,1072991076352,-1387101290496,1705302786048,-2711819321344,4233487613952,-4055588929536,1639518404608]),(⟨0,1,2⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨0,1,3⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨0,1,4⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨0,2,0⟩,[-147456,5193728,-79003648,690110464,-3866951680,14587740160,-37217271808,60118155264,-40570748928,-71084294144,255443435520,-378249363456,370037293056,-594635538432,1389969965056,-1752763547648,792983683072]),(⟨0,2,1⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨0,2,2⟩,[229376,-7536640,103809024,-788201472,3646717952,-10606608384,18649907200,-15731130368,-2963505152,9520349184,19335348224,-17197629440,-72344174592,73062809600,46859223040]),(⟨0,2,3⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨0,2,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,2,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,3,0⟩,[-49152,3129344,-67649536,761282560,-5258854400,24298700800,-79208857600,189358227456,-342149185536,475958558720,-524730023936,565891088384,-845822115840,1181918707712,-780683165696,6586220544]),(⟨0,3,1⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨0,3,2⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨0,3,3⟩,[0,-524288,16384000,-195821568,1240596480,-4785700864,12332564480,-23121625088,33085980672,-34109652992,31271813120,-60126134272,74456891392]),(⟨0,4,0⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨0,4,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨0,4,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,5,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨0,5,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,6,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064]),(⟨1,0,0⟩,[16384,-1196032,29573120,-390184960,3257876480,-18790989824,78923317248,-250064846848,613342429184,-1187070951424,1839949791232,-2353381064704,2782838374400,-3704447647744,5187145875456,-5400051466240,2954034282496,-399294300160]),(⟨1,0,1⟩,[0,-196608,8224768,-140378112,1356496896,-8517648384,37651972096,-124201992192,319920832512,-658443141120,1072991076352,-1387101290496,1705302786048,-2711819321344,4233487613952,-4055588929536,1639518404608]),(⟨1,0,2⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨1,0,3⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨1,0,4⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨1,1,0⟩,[0,-196608,8224768,-140378112,1356496896,-8517648384,37651972096,-124201992192,319920832512,-658443141120,1072991076352,-1387101290496,1705302786048,-2711819321344,4233487613952,-4055588929536,1639518404608]),(⟨1,1,1⟩,[0,0,0,4718592,-124256256,1347944448,-7812415488,25631391744,-43609227264,18034458624,45616201728,-31339315200,97034698752,-842606837760,1818276397056,-1286612189184]),(⟨1,1,2⟩,[0,0,262144,-7864320,94896128,-594018304,2049703936,-3610247168,1844445184,2846883840,-11704467456,60702588928,-112736075776,-20548419584,146086821888]),(⟨1,1,3⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨1,2,0⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨1,2,1⟩,[0,0,262144,-7864320,94896128,-594018304,2049703936,-3610247168,1844445184,2846883840,-11704467456,60702588928,-112736075776,-20548419584,146086821888]),(⟨1,2,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,2,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,3,0⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨1,3,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨1,3,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨2,0,0⟩,[-147456,5193728,-79003648,690110464,-3866951680,14587740160,-37217271808,60118155264,-40570748928,-71084294144,255443435520,-378249363456,370037293056,-594635538432,1389969965056,-1752763547648,792983683072]),(⟨2,0,1⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨2,0,2⟩,[229376,-7536640,103809024,-788201472,3646717952,-10606608384,18649907200,-15731130368,-2963505152,9520349184,19335348224,-17197629440,-72344174592,73062809600,46859223040]),(⟨2,0,3⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨2,0,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,0,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,1,0⟩,[-16384,1261568,-29179904,338509824,-2366980096,10948591616,-35350921216,81873223680,-135899168768,157939515392,-139369103360,167043907584,-250812153856,61872848896,474874724352,-519914078208]),(⟨2,1,1⟩,[0,0,262144,-7864320,94896128,-594018304,2049703936,-3610247168,1844445184,2846883840,-11704467456,60702588928,-112736075776,-20548419584,146086821888]),(⟨2,1,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,2,0⟩,[229376,-7536640,103809024,-788201472,3646717952,-10606608384,18649907200,-15731130368,-2963505152,9520349184,19335348224,-17197629440,-72344174592,73062809600,46859223040]),(⟨2,2,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,2,2⟩,[65536,-2162688,33226752,-307429376,1828847616,-6989414400,15892611072,-13710524416,-30584537088,111621636096,-143626665984,80381280256,-14536933376]),(⟨2,2,3⟩,[65536,-2162688,30605312,-244514816,1226440704,-4053401600,8580890624,-7846887424,-15913910272,66541256704,-92305686528,48282271744]),(⟨2,2,4⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨2,2,5⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨2,3,0⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨2,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,3,2⟩,[65536,-2162688,30605312,-244514816,1226440704,-4053401600,8580890624,-7846887424,-15913910272,66541256704,-92305686528,48282271744]),(⟨2,3,3⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,4,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,4,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨2,4,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,5,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,5,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨3,0,0⟩,[-49152,3129344,-67649536,761282560,-5258854400,24298700800,-79208857600,189358227456,-342149185536,475958558720,-524730023936,565891088384,-845822115840,1181918707712,-780683165696,6586220544]),(⟨3,0,1⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨3,0,2⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨3,0,3⟩,[0,-524288,16384000,-195821568,1240596480,-4785700864,12332564480,-23121625088,33085980672,-34109652992,31271813120,-60126134272,74456891392]),(⟨3,1,0⟩,[0,327680,-11796480,168820736,-1334312960,6725107712,-23671603200,62217781248,-126204510208,192851410944,-215908352000,243086655488,-430855159808,597078769664,-342797844480]),(⟨3,1,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨3,1,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[32768,-2326528,46989312,-452132864,2457829376,-8075378688,16220815360,-19214761984,13094060032,-11233689600,29235150848,-45970817024,-6696697856,69245632512]),(⟨3,2,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,2⟩,[65536,-2162688,30605312,-244514816,1226440704,-4053401600,8580890624,-7846887424,-15913910272,66541256704,-92305686528,48282271744]),(⟨3,2,3⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,0⟩,[0,-524288,16384000,-195821568,1240596480,-4785700864,12332564480,-23121625088,33085980672,-34109652992,31271813120,-60126134272,74456891392]),(⟨3,3,2⟩,[0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,0,0⟩,[81920,-2392064,25493504,-107282432,-120406016,3447488512,-18196496384,56064868352,-118613426176,180260470784,-198054117376,204136448000,-355807182848,559679242240,-368547364864]),(⟨4,0,1⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,0,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,0⟩,[0,0,0,-2097152,47185920,-414187520,1782579200,-3531603968,727711744,6675234816,-884998144,2334130176,-76565970944,104191754240]),(⟨4,2,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,2,2⟩,[-327680,8912896,-93782016,479199232,-1198653440,1038090240,1796341760,-7567572992,12585467904,-5501353984,-5841289216]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[32768,-1933312,36700160,-342491136,1849065472,-6283165696,14205845504,-22337290240,24712675328,-18526273536,20460077056,-53301084160,48223715328,21368897536]),(⟨5,0,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[-131072,4325376,-52953088,310902784,-945553408,1497104384,-726138880,-4237819904,14844559360,-14989262848]),(⟨6,0,0⟩,[0,-262144,8192000,-97910784,620822528,-2405433344,6273236992,-11900551168,16437084160,-14424997888,12571967488,-34555166720,44652888064])]


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
    (Poly.add (Poly.scale (K.ofRat r645) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r644*r644 : ℚ)=r645 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 13 r644 r644 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C121

#print axioms Coulomb8.Columns.C121.sound
