import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C146

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -38469632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 54329344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2582183936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 12990283776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -51293782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 166550503424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -65190166528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 1044443824128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1909937471488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 2651258945536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -2864633020416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 3264656965632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -5025876606976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 386119041024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -4812524617728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 1467128217600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -151296933888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2818048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 266665984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -2175664128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 12245139456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -52043644928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 178897616896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -514274623488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 71426244608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2224530063360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 2991176744960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -3128779210752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 3884478758912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -6590549000192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 8305488625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -740854333440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 126887657472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 64028672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -74514432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 2733113344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -9985851392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 27166572544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -56868667392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 82182144000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -25678839808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -216487755776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 494252785664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -395562188800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 320682590208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -1393943707648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 142445314048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -26466189312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 6094848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -501022720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 3438542848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -15940452352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 55697670144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -158449074176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 366403911680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -628606631936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 705534951424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -564165804032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 877317062656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -101643190272, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 1483440717824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -213740617728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -3276800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 14417920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 8454144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -2167668736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 12326010880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -44004016128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 117804433408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -222361550848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 252645605376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -183608541184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 50241011712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -15596781568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 82945245184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -22413312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 221511680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -70909952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 4278845440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -11571822592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 25570050048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -39801061376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 29639180288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -10117578752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 62360125440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -99886432256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 82182144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 7602176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -389808128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 1722810368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -324009984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 13424394240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -21676687360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 16306405376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -7182745600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 41977380864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -64493453312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 63438848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -654049280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 4140171264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -19326435328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 76277743616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -261245108224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 709057314816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -1358364016640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 1694728192000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1633604075520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 2780248801280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -5708000395264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 6419003342848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -405680160768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 18415616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -220397568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 1531052032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -7193100288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 25416630272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -70938984448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 150549037056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -218408812544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 199275511808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -190507974656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 361441132544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -280735907840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -64908754944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 13780844544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 4063232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -11403264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 693108736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -3739090944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 15355215872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -52641923072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 20079181824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -250368229376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 252509290496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -27477278720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 469652996096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -127341821952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 83850821632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -69992448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 35389440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -353370112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 4245684224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 1679294464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -11944853504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -6009389056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 14485028864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 100893196288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1285292032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -54788096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 385089536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1652162560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 4872470528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -11593842688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 24302321664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -38138150912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 30762598400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -4650172416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 277086208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -39087636480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 8156086272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -1782841344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 15204352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -779616256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 3445620736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -648019968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 26848788480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -43353374720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 32612810752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -14365491200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 83954761728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -128986906624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -7077888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 185204736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -1986134016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 11234574336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -34682044416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 2811494400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 19010420736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -109176422400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -63806373888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 30380261376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 931727278080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -56129617920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 2487877632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 57016320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -428736512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1916796928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -99221504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 4448583680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 10726146048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -36779720704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 35199385600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 8433041408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -44453724160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 1795424256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 144550264832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -1699479552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 20578304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -12713984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 67502080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -426115072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1556348928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1498677248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -21557936128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 2640314368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 11540758528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 29145563136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -8947630080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -480641024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -393216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 279183360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -119013376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 746061824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 137101312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -6217531392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 1412300800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 831782912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 6685589504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -2094268416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -2359296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 198443008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -112197632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 1143996416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 1527250944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -6331826176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 1894776832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 429916160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 8593866752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -185860096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 41156608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -62652416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 347865088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -7168851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 8059879424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 12490113024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -46474461184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 29170335744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 35100295168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 29321068544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -31383093248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 229900288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -835190784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 16252928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 15990784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -4858576896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 262275072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -4696834048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 18941345792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 472645632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -38010880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -84148224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 520617984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -1994915840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 5620367360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -14028374016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 25886195712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -859045888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -131150643200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 260309778432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -129725104128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -446693376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -23068672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 28835840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -960495616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 3099590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -8329887744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 16256073728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -4559208448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -66648539136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 20973617152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -121110528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 66322432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -299892736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 667418624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -997195776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 1833435136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 908066816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -14995423232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 2913468416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -3932160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 4194304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -203423744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 725614592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1762656256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 171966464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1860173824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -18777899008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 181927936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -37748736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1019215872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -317718528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 7889485824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -9191817216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -113246208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -19234816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 27164672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -1291091968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 6495141888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -25646891008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 83275251712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -32595083264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 522221912064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -954968735744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1325629472768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -1432316510208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 1632328482816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -2512938303488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 193059520512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -2406262308864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 733564108800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -75648466944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -1409024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 133332992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -1087832064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 6122569728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -26021822464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 89448808448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -257137311744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 35713122304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -1112265031680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 1495588372480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -1564389605376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 1942239379456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -3295274500096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 4152744312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -370427166720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 63443828736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 32014336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -37257216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 1366556672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -4992925696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 13583286272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -28434333696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 41091072000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -12839419904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -108243877888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 247126392832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -197781094400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 160341295104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -696971853824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 71222657024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -13233094656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 3047424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -250511360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 1719271424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -7970226176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 27848835072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -79224537088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 183201955840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -314303315968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 352767475712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -282082902016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 438658531328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -50821595136, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 741720358912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -106870308864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -1638400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 7208960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 4227072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -1083834368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 6163005440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -22002008064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 58902216704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -111180775424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 126322802688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -91804270592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 25120505856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -7798390784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 41472622592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -11206656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 110755840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -35454976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 2139422720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -5785911296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 12785025024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -19900530688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 14819590144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -5058789376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 31180062720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -49943216128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 41091072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 3801088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -194904064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 861405184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -162004992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 6712197120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -10838343680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 8153202688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -3591372800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 20988690432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -32246726656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 31719424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -327024640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 2070085632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -9663217664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 38138871808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -130622554112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 354528657408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -679182008320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 847364096000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -816802037760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1390124400640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -2854000197632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 3209501671424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -202840080384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 9207808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -110198784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 765526016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -3596550144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 12708315136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -35469492224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 75274518528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -109204406272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 99637755904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -95253987328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 180720566272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -140367953920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -32454377472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 6890422272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -5701632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 346554368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -1869545472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 7677607936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -26320961536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 10039590912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -125184114688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 126254645248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -13738639360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 234826498048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -63670910976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 41925410816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -34996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 17694720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -176685056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 2122842112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 839647232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -5972426752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -3004694528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 7242514432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 50446598144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -642646016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -27394048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 192544768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -826081280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 2436235264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -5796921344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 12151160832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -19069075456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 15381299200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -2325086208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 138543104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -19543818240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 4078043136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -891420672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -3538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 92602368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -993067008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 5617287168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -17341022208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 1405747200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 9505210368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -54588211200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -31903186944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 15190130688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 465863639040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -28064808960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 1243938816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 28508160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -214368256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 958398464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -49610752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 2224291840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 5363073024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -18389860352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 17599692800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 4216520704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -22226862080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 897712128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 72275132416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -849739776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 10289152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -6356992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 33751040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -213057536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 778174464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 749338624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -10778968064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 1320157184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 5770379264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 14572781568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -4473815040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -240320512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 373030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 68550656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -3108765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 706150400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 415891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 3342794752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -1047134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -1179648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -31326208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 173932544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -3584425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 4029939712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 6245056512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -23237230592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 14585167872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 17550147584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 14660534272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -15691546624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 114950144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -417595392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 8126464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 7995392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -2429288448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 131137536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -2348417024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 9470672896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 236322816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -19005440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -42074112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 260308992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -997457920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 2810183680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -7014187008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 12943097856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -429522944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -65575321600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 130154889216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -64862552064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -223346688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := -11534336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -480247808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 1549795328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -4164943872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 8128036864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -2279604224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -33324269568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 10486808576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -60555264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 33161216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -149946368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 333709312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -498597888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 916717568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 454033408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -7497711616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 1456734208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -1966080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -101711872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 362807296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -881328128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 85983232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 930086912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -9388949504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 90963968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -18874368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -509607936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -158859264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 3944742912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -4595908608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -56623104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18],[0,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35],[r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52],[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67],[r0,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81],[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105],[],[],[],[],[],[],[0,0,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120],[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135],[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[0,0,0,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159],[],[],[],[],[],[],[],[r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174],[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[],[],[],[],[],[],[],[0,0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198],[r36,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212],[0,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225],[r160,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237],[0,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248],[],[],[],[],[],[0,r53,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260],[r160,r226,r227,r228,r261,r262,r263,r264,r265,r266,r267,r268,r269],[0,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282],[0,r238,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292],[r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303],[0,r53,r304,r305,r306,r307,r308,r309,r310,r311],[],[],[],[0,0,r312,r313,r314,r315,r316,r317,r318,r319,1572864],[],[],[],[],[],[],[],[],[],[r320,r321,r322,r323,r324,r325,r326,r327,524288],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨0,0,1⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,0,2⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,0,3⟩,[0,r213,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,0,4⟩,[r328,r238,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨0,0,5⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,0,6⟩,[0,0,r53,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨0,1,0⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,1,1⟩,[0,0,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨0,1,2⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,1,3⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨0,1,4⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,2,0⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,2,1⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,2,2⟩,[r0,r68,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨0,2,3⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,3,0⟩,[0,r213,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,3,1⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨0,3,2⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,3,3⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]),(⟨0,4,0⟩,[r328,r238,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨0,4,1⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,5,0⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,6,0⟩,[0,0,r53,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨1,0,0⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨1,0,1⟩,[0,0,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨1,0,2⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,0,3⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨1,0,4⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,1,0⟩,[0,0,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445]),(⟨1,1,1⟩,[0,0,0,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509]),(⟨1,1,2⟩,[r364,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨1,1,3⟩,[0,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨1,1,4⟩,[r0,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547,r548]),(⟨1,1,5⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨1,2,0⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,2,1⟩,[r364,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨1,2,2⟩,[0,r213,r214,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨1,2,3⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨1,2,4⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨1,3,0⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨1,3,1⟩,[0,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨1,3,2⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨1,4,0⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,4,1⟩,[r0,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547,r548]),(⟨1,4,2⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨1,5,1⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,0,0⟩,[r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨2,0,1⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,0,2⟩,[r0,r68,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨2,0,3⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨2,1,0⟩,[0,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,1,1⟩,[r364,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨2,1,2⟩,[0,r213,r214,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨2,1,3⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨2,1,4⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,2,0⟩,[r0,r68,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨2,2,1⟩,[0,r213,r214,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨2,2,2⟩,[r160,r579,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨2,2,3⟩,[0,r320,r591,r70,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨2,2,4⟩,[r36,r600,r601,r602,r603,r604,r605,r606,r607,r608,r609]),(⟨2,2,5⟩,[0,r213,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨2,3,0⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨2,3,1⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨2,3,2⟩,[0,r320,r591,r70,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨2,3,3⟩,[0,0,r618,r619,r620,r621,r622,r623,r624,r625,786432]),(⟨2,4,1⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,4,2⟩,[r36,r600,r601,r602,r603,r604,r605,r606,r607,r608,r609]),(⟨2,5,2⟩,[0,r213,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨3,0,0⟩,[0,r213,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨3,0,1⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨3,0,2⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨3,0,3⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]),(⟨3,1,0⟩,[0,0,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473]),(⟨3,1,1⟩,[0,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨3,1,2⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨3,2,0⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨3,2,1⟩,[r0,r537,r538,r539,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨3,2,2⟩,[0,r320,r591,r70,r592,r593,r594,r595,r596,r597,r598,r599]),(⟨3,2,3⟩,[0,0,r618,r619,r620,r621,r622,r623,r624,r625,786432]),(⟨3,3,0⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]),(⟨3,3,2⟩,[0,0,r618,r619,r620,r621,r622,r623,r624,r625,786432]),(⟨3,3,4⟩,[r293,r175,r626,r627,r628,r629,r630,r631,262144]),(⟨3,4,3⟩,[r293,r175,r626,r627,r628,r629,r630,r631,262144]),(⟨4,0,0⟩,[r328,r238,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨4,0,1⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨4,1,0⟩,[0,0,0,r312,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨4,1,1⟩,[r0,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547,r548]),(⟨4,1,2⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨4,2,1⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨4,2,2⟩,[r36,r600,r601,r602,r603,r604,r605,r606,r607,r608,r609]),(⟨4,3,3⟩,[r293,r175,r626,r627,r628,r629,r630,r631,262144]),(⟨5,0,0⟩,[0,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨5,1,1⟩,[0,r320,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨5,2,2⟩,[0,r213,r610,r611,r612,r613,r614,r615,r616,r617]),(⟨6,0,0⟩,[0,0,r53,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r632) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r632) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

noncomputable def partial12 : Poly := [(⟨1,2,1⟩,[65536,-2097152,28704768,-220266496,1029111808,-2863333376,3612868608,3493199872,-19267649536,20854734848,4494065664,2413494272,-70502514688,81148313600,-15628763136]),(⟨1,2,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,2,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,2,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,3,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,3,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,5,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,0,0⟩,[32768,-1114112,16482304,-141983744,806846464,-3267166208,10059153408,-25128239104,52906786816,-89792643072,109461667840,-97711259648,130862317568,-246537191424,243310886912,-74559750144,6895042560]),(⟨2,0,1⟩,[0,-196608,5537792,-65306624,431751168,-1832321024,5609127936,-14011367424,30023614464,-50192515072,57303990272,-53766619136,94845272064,-173011959808,142962950144,-21122088960]),(⟨2,0,2⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2896887808,6037831680,-9213673472,6671433728,-1480261632,11283791872,-18963726336,796852224,433520640]),(⟨2,0,3⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨2,1,0⟩,[0,-196608,5537792,-65306624,431751168,-1832321024,5609127936,-14011367424,30023614464,-50192515072,57303990272,-53766619136,94845272064,-173011959808,142962950144,-21122088960]),(⟨2,1,1⟩,[65536,-2097152,28704768,-220266496,1028587520,-2849701888,3480223744,4092985344,-20602486784,22849126400,827195392,597360640,-40511668224,40359755776,-9077784576]),(⟨2,1,2⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,1,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,2,0⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2896887808,6037831680,-9213673472,6671433728,-1480261632,11283791872,-18963726336,796852224,433520640]),(⟨2,2,1⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,2,2⟩,[0,0,0,0,-2097152,50331648,-427819008,1358954496,423624704,-10519314432,12255756288,17968398336,-29697769472]),(⟨2,3,0⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨2,3,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,4,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,0,0⟩,[0,-393216,10780672,-128352256,894369792,-4192993280,14597586944,-40412938240,89576308736,-148212154368,165746802688,-145409671168,241788452864,-456156512256,391543422976,-66695036928]),(⟨3,0,1⟩,[0,0,1179648,-24576000,226689024,-1257963520,4881186816,-14448197632,32733790208,-51636994048,50546343936,-53269430272,140826312704,-237556400128,146157928448]),(⟨3,0,2⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨3,0,3⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨3,1,0⟩,[0,0,1179648,-24576000,226689024,-1257963520,4881186816,-14448197632,32733790208,-51636994048,50546343936,-53269430272,140826312704,-237556400128,146157928448]),(⟨3,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1789067264,1956249600,3529375744,-13069844480,10817896448,2928214016,3609919488,-17364615168,4577886208]),(⟨3,1,2⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨3,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,3,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨3,4,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,0,0⟩,[-32768,1048576,-12517376,71696384,-185827328,-53477376,2116943872,-9010151424,24854953984,-46959951872,52732952576,-40169504768,91871739904,-195970990080,140040470528]),(⟨4,0,1⟩,[0,0,0,0,0,3145728,-58720256,406847488,-1451229184,3525312512,-5846859776,-3720347648,37555798016,-43298848768]),(⟨4,1,0⟩,[0,0,0,0,0,3145728,-58720256,406847488,-1451229184,3525312512,-5846859776,-3720347648,37555798016,-43298848768]),(⟨4,1,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,2,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨4,3,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨5,1,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨6,0,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656])]


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

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,131072,-3932160,53805056,-452591616,2670723072,-11996954624,43327356928,-128869400576,310876438528,-578688778240,783033237504,-788936523776,897420361728,-1531920711680,2014213636096,-1283223650304,212367310848]),(⟨1,0,1⟩,[0,0,-589824,12713984,-120717312,711983104,-3372089344,15295053824,-61880598528,187973500928,-381237395456,476773482496,-403789840384,599089741824,-1309211361280,1542843006976,-697446629376]),(⟨1,0,2⟩,[0,-131072,3670016,-44892160,333774848,-1762131968,7053049856,-21054423040,43329912832,-52812709888,25673990144,-8975220736,76756877312,-100653072384,-76512952320,156982640640]),(⟨1,0,3⟩,[0,0,851968,-15335424,119865344,-611581952,2796421120,-11872763904,37543346176,-73547120640,75708301312,-42901045248,94000185344,-208139976704,147319947264]),(⟨1,0,4⟩,[0,0,0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨1,1,0⟩,[0,0,-589824,12713984,-120717312,711983104,-3372089344,15295053824,-61880598528,187973500928,-381237395456,476773482496,-403789840384,599089741824,-1309211361280,1542843006976,-697446629376]),(⟨1,1,1⟩,[0,0,0,-2359296,61734912,-659947520,3698720768,-11156979712,14010810368,12535988224,-53051916288,11243356160,61768859648,177278681088,-623153119232,489030549504]),(⟨1,1,2⟩,[65536,-2097152,28508160,-214368256,958922752,-2444558336,2360082432,4687790080,-16413294592,13566869504,7247953920,-4631756800,-42090496000,86111092736,-63123357696]),(⟨1,1,3⟩,[0,-393216,10289152,-108068864,573767680,-1494548480,836894720,4838522880,-9327738880,-2205155328,11617239040,18293129216,-42029613056,14700707840]),(⟨1,1,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,1,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,2,0⟩,[0,-131072,3670016,-44892160,333774848,-1762131968,7053049856,-21054423040,43329912832,-52812709888,25673990144,-8975220736,76756877312,-100653072384,-76512952320,156982640640]),(⟨1,2,1⟩,[65536,-2097152,28508160,-214368256,958922752,-2444558336,2360082432,4687790080,-16413294592,13566869504,7247953920,-4631756800,-42090496000,86111092736,-63123357696]),(⟨1,2,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨1,2,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,2,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,3,0⟩,[0,0,851968,-15335424,119865344,-611581952,2796421120,-11872763904,37543346176,-73547120640,75708301312,-42901045248,94000185344,-208139976704,147319947264]),(⟨1,3,1⟩,[0,-393216,10289152,-108068864,573767680,-1494548480,836894720,4838522880,-9327738880,-2205155328,11617239040,18293129216,-42029613056,14700707840]),(⟨1,3,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,4,0⟩,[0,0,0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨1,4,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,4,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,5,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,0,0⟩,[32768,-1114112,15695872,-122978304,600014848,-1894383616,3599728640,-1243185152,-19812417536,87701258240,-213972779008,316498018304,-286409719808,345312067584,-854392930304,1224838316032,-643665297408]),(⟨2,0,1⟩,[0,-196608,5537792,-66486272,462618624,-2163343360,7481556992,-19791708160,37989515264,-47024111616,39107919872,-64401014784,130288910336,-17724080128,-315428929536,324278255616]),(⟨2,0,2⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2900033536,6113329152,-9855401984,8709865472,-844824576,-4495179776,-580091904,27749449728,-44113133568]),(⟨2,0,3⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨2,1,0⟩,[0,-196608,5537792,-66486272,462618624,-2163343360,7481556992,-19791708160,37989515264,-47024111616,39107919872,-64401014784,130288910336,-17724080128,-315428929536,324278255616]),(⟨2,1,1⟩,[65536,-2097152,28704768,-220266496,1028587520,-2849701888,3473932288,4243980288,-21885943808,26925989888,2098069504,-30960582656,-3744399360,94264950784,-98171092992]),(⟨2,1,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,1,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,1,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,2,0⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2900033536,6113329152,-9855401984,8709865472,-844824576,-4495179776,-580091904,27749449728,-44113133568]),(⟨2,2,1⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,2,2⟩,[0,0,0,0,-3145728,75497472,-641728512,2038431744,635437056,-15778971648,18383634432,26952597504,-44546654208]),(⟨2,3,0⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨2,3,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,4,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,0,0⟩,[0,-524288,14450688,-172064768,1197277184,-5626200064,19824345088,-56090722304,126861312000,-210392449024,226276638720,-176262643712,292220108800,-578800386048,479791710208,-53342601216]),(⟨3,0,1⟩,[0,0,983040,-18677760,156499968,-839188480,3631546368,-13329104896,36229873664,-60963291136,52664795136,-44535709696,150854696960,-259546218496,143209988096]),(⟨3,0,2⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨3,0,3⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨3,1,0⟩,[0,0,983040,-18677760,156499968,-839188480,3631546368,-13329104896,36229873664,-60963291136,52664795136,-44535709696,150854696960,-259546218496,143209988096]),(⟨3,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1789067264,1956249600,3529375744,-13069844480,10817896448,2928214016,3609919488,-17364615168,4577886208]),(⟨3,1,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,0⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨3,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨3,2,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨3,3,2⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,4,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,0,0⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨4,0,1⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,0⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨4,3,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨5,1,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨6,0,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,131072,-3932160,53805056,-452591616,2670723072,-11996954624,43327356928,-128869400576,310876438528,-578688778240,783033237504,-788936523776,897420361728,-1531920711680,2014213636096,-1283223650304,212367310848]),(⟨0,1,1⟩,[0,0,-589824,12713984,-120717312,711983104,-3372089344,15295053824,-61880598528,187973500928,-381237395456,476773482496,-403789840384,599089741824,-1309211361280,1542843006976,-697446629376]),(⟨0,1,2⟩,[0,-131072,3670016,-44892160,333774848,-1762131968,7053049856,-21054423040,43329912832,-52812709888,25673990144,-8975220736,76756877312,-100653072384,-76512952320,156982640640]),(⟨0,1,3⟩,[0,0,851968,-15335424,119865344,-611581952,2796421120,-11872763904,37543346176,-73547120640,75708301312,-42901045248,94000185344,-208139976704,147319947264]),(⟨0,1,4⟩,[0,0,0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨0,2,0⟩,[32768,-1114112,15695872,-122978304,600014848,-1894383616,3599728640,-1243185152,-19812417536,87701258240,-213972779008,316498018304,-286409719808,345312067584,-854392930304,1224838316032,-643665297408]),(⟨0,2,1⟩,[0,-196608,5537792,-66486272,462618624,-2163343360,7481556992,-19791708160,37989515264,-47024111616,39107919872,-64401014784,130288910336,-17724080128,-315428929536,324278255616]),(⟨0,2,2⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2900033536,6113329152,-9855401984,8709865472,-844824576,-4495179776,-580091904,27749449728,-44113133568]),(⟨0,2,3⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨0,3,0⟩,[0,-524288,14450688,-172064768,1197277184,-5626200064,19824345088,-56090722304,126861312000,-210392449024,226276638720,-176262643712,292220108800,-578800386048,479791710208,-53342601216]),(⟨0,3,1⟩,[0,0,983040,-18677760,156499968,-839188480,3631546368,-13329104896,36229873664,-60963291136,52664795136,-44535709696,150854696960,-259546218496,143209988096]),(⟨0,3,2⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨0,3,3⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨0,4,0⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨0,4,1⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨0,5,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨0,6,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨1,0,0⟩,[0,131072,-3932160,53805056,-452591616,2670723072,-11996954624,43327356928,-128869400576,310876438528,-578688778240,783033237504,-788936523776,897420361728,-1531920711680,2014213636096,-1283223650304,212367310848]),(⟨1,0,1⟩,[0,0,-589824,12713984,-120717312,711983104,-3372089344,15295053824,-61880598528,187973500928,-381237395456,476773482496,-403789840384,599089741824,-1309211361280,1542843006976,-697446629376]),(⟨1,0,2⟩,[0,-131072,3670016,-44892160,333774848,-1762131968,7053049856,-21054423040,43329912832,-52812709888,25673990144,-8975220736,76756877312,-100653072384,-76512952320,156982640640]),(⟨1,0,3⟩,[0,0,851968,-15335424,119865344,-611581952,2796421120,-11872763904,37543346176,-73547120640,75708301312,-42901045248,94000185344,-208139976704,147319947264]),(⟨1,0,4⟩,[0,0,0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨1,1,0⟩,[0,0,-1376256,31719424,-327548928,2084765696,-9831514112,39180107776,-134599802880,365467402240,-704671842304,890982760448,-821061877760,1190939000832,-2406915178496,2842241073152,-1348006969344]),(⟨1,1,1⟩,[0,0,0,-3538944,92602368,-990969856,5571149824,-16937320448,21976711168,15704391680,-71247986688,608960512,97212497920,332566560768,-1081544998912,834430894080]),(⟨1,1,2⟩,[65536,-2097152,28508160,-214368256,958922752,-2444558336,2356936704,4763287552,-17055023104,15605301248,7883390976,-20410728448,-23706861568,113063690240,-107670011904]),(⟨1,1,3⟩,[0,-393216,10289152,-108068864,573767680,-1494548480,836894720,4838522880,-9327738880,-2205155328,11617239040,18293129216,-42029613056,14700707840]),(⟨1,1,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,1,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,2,0⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨1,2,1⟩,[65536,-2097152,28508160,-214368256,958398464,-2430926848,2224291840,5363073024,-18389860352,17599692800,4216520704,-22226862080,6283984896,72275132416,-101119033344]),(⟨1,2,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨1,2,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,2,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,3,0⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨1,3,1⟩,[0,-393216,10289152,-108068864,573767680,-1491402752,778174464,5245370368,-10778968064,1320157184,5770379264,14572781568,-4473815040,-28598140928]),(⟨1,3,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,4,0⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨1,4,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,4,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,5,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,0,0⟩,[32768,-1114112,15695872,-122978304,600014848,-1894383616,3599728640,-1243185152,-19812417536,87701258240,-213972779008,316498018304,-286409719808,345312067584,-854392930304,1224838316032,-643665297408]),(⟨2,0,1⟩,[0,-196608,5537792,-66486272,462618624,-2163343360,7481556992,-19791708160,37989515264,-47024111616,39107919872,-64401014784,130288910336,-17724080128,-315428929536,324278255616]),(⟨2,0,2⟩,[-32768,1048576,-13697024,96272384,-413040640,1218117632,-2900033536,6113329152,-9855401984,8709865472,-844824576,-4495179776,-580091904,27749449728,-44113133568]),(⟨2,0,3⟩,[0,262144,-6356992,61538304,-318177280,1026097152,-2519334912,5680005120,-10132258816,9335865344,-4075094016,16799694848,-29321003008,4878827520]),(⟨2,1,0⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨2,1,1⟩,[65536,-2097152,28508160,-214368256,958398464,-2430926848,2224291840,5363073024,-18389860352,17599692800,4216520704,-22226862080,6283984896,72275132416,-101119033344]),(⟨2,1,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,1,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,1,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,2,0⟩,[-65536,2097152,-27394048,192544768,-826081280,2436235264,-5796921344,12151160832,-19069075456,15381299200,-2325086208,6788612096,-19543818240,28546301952,-43679612928]),(⟨2,2,1⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,2,2⟩,[0,0,0,0,-3145728,75497472,-641728512,2038431744,635437056,-15778971648,18383634432,26952597504,-44546654208]),(⟨2,3,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨2,3,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,3,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨2,3,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨2,4,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨2,5,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨3,0,0⟩,[0,-524288,14450688,-172064768,1197277184,-5626200064,19824345088,-56090722304,126861312000,-210392449024,226276638720,-176262643712,292220108800,-578800386048,479791710208,-53342601216]),(⟨3,0,1⟩,[0,0,983040,-18677760,156499968,-839188480,3631546368,-13329104896,36229873664,-60963291136,52664795136,-44535709696,150854696960,-259546218496,143209988096]),(⟨3,0,2⟩,[0,196608,-4849664,49217536,-284557312,1113325568,-3266576384,7105019904,-9768271872,5483724800,-983695360,14380367872,-20622213120,-2865364992]),(⟨3,0,3⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨3,1,0⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨3,1,1⟩,[0,-393216,10289152,-108068864,573767680,-1491402752,778174464,5245370368,-10778968064,1320157184,5770379264,14572781568,-4473815040,-28598140928]),(⟨3,1,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨3,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨3,2,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,0⟩,[0,0,-3145728,53215232,-389808128,1722810368,-5508169728,13424394240,-21676687360,16306405376,-7182745600,41977380864,-64493453312]),(⟨3,3,2⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,4,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,0,0⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨4,0,1⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,0⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨4,3,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨5,1,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨6,0,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1179648,-19234816,190152704,-1291091968,6495141888,-25646891008,83275251712,-228165582848,522221912064,-954968735744,1325629472768,-1432316510208,1632328482816,-2512938303488,3282011848704,-2406262308864,733564108800,-75648466944]),(⟨0,0,1⟩,[0,327680,-9863168,133332992,-1087832064,6122569728,-26021822464,89448808448,-257137311744,607123079168,-1112265031680,1495588372480,-1564389605376,1942239379456,-3295274500096,4152744312832,-2592990167040,444106801152]),(⟨0,0,2⟩,[65536,-2228224,32014336,-260800512,1366556672,-4992925696,13583286272,-28434333696,41091072000,-12839419904,-108243877888,247126392832,-197781094400,160341295104,-696971853824,1210785169408,-648421638144]),(⟨0,0,3⟩,[0,-786432,21331968,-250511360,1719271424,-7970226176,27848835072,-79224537088,183201955840,-314303315968,352767475712,-282082902016,438658531328,-863967117312,741720358912,-106870308864]),(⟨0,0,4⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨0,0,5⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨0,0,6⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨0,1,0⟩,[0,327680,-9863168,133332992,-1087832064,6122569728,-26021822464,89448808448,-257137311744,607123079168,-1112265031680,1495588372480,-1564389605376,1942239379456,-3295274500096,4152744312832,-2592990167040,444106801152]),(⟨0,1,1⟩,[0,0,-1376256,31719424,-327024640,2070085632,-9663217664,38138871808,-130622554112,354528657408,-679182008320,847364096000,-816802037760,1390124400640,-2854000197632,3209501671424,-1419880562688]),(⟨0,1,2⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨0,1,3⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨0,1,4⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨0,2,0⟩,[65536,-2228224,32014336,-260800512,1366556672,-4992925696,13583286272,-28434333696,41091072000,-12839419904,-108243877888,247126392832,-197781094400,160341295104,-696971853824,1210785169408,-648421638144]),(⟨0,2,1⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨0,2,2⟩,[-65536,2097152,-27394048,192544768,-826081280,2436235264,-5796921344,12151160832,-19069075456,15381299200,-2325086208,6788612096,-19543818240,28546301952,-43679612928]),(⟨0,2,3⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨0,3,0⟩,[0,-786432,21331968,-250511360,1719271424,-7970226176,27848835072,-79224537088,183201955840,-314303315968,352767475712,-282082902016,438658531328,-863967117312,741720358912,-106870308864]),(⟨0,3,1⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨0,3,2⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨0,3,3⟩,[0,0,-3145728,53215232,-389808128,1722810368,-5508169728,13424394240,-21676687360,16306405376,-7182745600,41977380864,-64493453312]),(⟨0,4,0⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨0,4,1⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨0,5,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨0,6,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656]),(⟨1,0,0⟩,[0,327680,-9863168,133332992,-1087832064,6122569728,-26021822464,89448808448,-257137311744,607123079168,-1112265031680,1495588372480,-1564389605376,1942239379456,-3295274500096,4152744312832,-2592990167040,444106801152]),(⟨1,0,1⟩,[0,0,-1376256,31719424,-327024640,2070085632,-9663217664,38138871808,-130622554112,354528657408,-679182008320,847364096000,-816802037760,1390124400640,-2854000197632,3209501671424,-1419880562688]),(⟨1,0,2⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨1,0,3⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨1,0,4⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨1,1,0⟩,[0,0,-1376256,31719424,-327024640,2070085632,-9663217664,38138871808,-130622554112,354528657408,-679182008320,847364096000,-816802037760,1390124400640,-2854000197632,3209501671424,-1419880562688]),(⟨1,1,1⟩,[0,0,0,-3538944,92602368,-993067008,5617287168,-17341022208,23897702400,9505210368,-54588211200,-31903186944,106330914816,465863639040,-1375175639040,1036201033728]),(⟨1,1,2⟩,[65536,-2097152,28508160,-214368256,958398464,-2430926848,2224291840,5363073024,-18389860352,17599692800,4216520704,-22226862080,6283984896,72275132416,-101119033344]),(⟨1,1,3⟩,[0,-393216,10289152,-108068864,573767680,-1491402752,778174464,5245370368,-10778968064,1320157184,5770379264,14572781568,-4473815040,-28598140928]),(⟨1,1,4⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,1,5⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,2,0⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨1,2,1⟩,[65536,-2097152,28508160,-214368256,958398464,-2430926848,2224291840,5363073024,-18389860352,17599692800,4216520704,-22226862080,6283984896,72275132416,-101119033344]),(⟨1,2,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨1,2,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,2,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,3,0⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨1,3,1⟩,[0,-393216,10289152,-108068864,573767680,-1491402752,778174464,5245370368,-10778968064,1320157184,5770379264,14572781568,-4473815040,-28598140928]),(⟨1,3,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,4,0⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨1,4,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,4,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,5,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,0,0⟩,[65536,-2228224,32014336,-260800512,1366556672,-4992925696,13583286272,-28434333696,41091072000,-12839419904,-108243877888,247126392832,-197781094400,160341295104,-696971853824,1210785169408,-648421638144]),(⟨2,0,1⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨2,0,2⟩,[-65536,2097152,-27394048,192544768,-826081280,2436235264,-5796921344,12151160832,-19069075456,15381299200,-2325086208,6788612096,-19543818240,28546301952,-43679612928]),(⟨2,0,3⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨2,1,0⟩,[0,-327680,9207808,-110198784,765526016,-3596550144,12708315136,-35469492224,75274518528,-109204406272,99637755904,-95253987328,180720566272,-140367953920,-227180642304,337630691328]),(⟨2,1,1⟩,[65536,-2097152,28508160,-214368256,958398464,-2430926848,2224291840,5363073024,-18389860352,17599692800,4216520704,-22226862080,6283984896,72275132416,-101119033344]),(⟨2,1,2⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,1,3⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,1,4⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,2,0⟩,[-65536,2097152,-27394048,192544768,-826081280,2436235264,-5796921344,12151160832,-19069075456,15381299200,-2325086208,6788612096,-19543818240,28546301952,-43679612928]),(⟨2,2,1⟩,[0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨2,2,2⟩,[-131072,3670016,-42074112,260308992,-997457920,2810183680,-7014187008,12943097856,-429522944,-65575321600,130154889216,-64862552064,-26578255872]),(⟨2,2,3⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨2,2,4⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨2,2,5⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨2,3,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨2,3,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,3,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨2,3,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨2,4,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨2,5,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨3,0,0⟩,[0,-786432,21331968,-250511360,1719271424,-7970226176,27848835072,-79224537088,183201955840,-314303315968,352767475712,-282082902016,438658531328,-863967117312,741720358912,-106870308864]),(⟨3,0,1⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨3,0,2⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨3,0,3⟩,[0,0,-3145728,53215232,-389808128,1722810368,-5508169728,13424394240,-21676687360,16306405376,-7182745600,41977380864,-64493453312]),(⟨3,1,0⟩,[0,0,2031616,-39911424,346554368,-1869545472,7677607936,-26320961536,70277136384,-125184114688,126254645248,-96170475520,234826498048,-445696376832,293477875712]),(⟨3,1,1⟩,[0,-393216,10289152,-108068864,573767680,-1491402752,778174464,5245370368,-10778968064,1320157184,5770379264,14572781568,-4473815040,-28598140928]),(⟨3,1,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨3,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨3,2,2⟩,[0,524288,-11534336,100925440,-480247808,1549795328,-4164943872,8128036864,-2279604224,-33324269568,73407660032,-50442534912]),(⟨3,2,3⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,0⟩,[0,0,-3145728,53215232,-389808128,1722810368,-5508169728,13424394240,-21676687360,16306405376,-7182745600,41977380864,-64493453312]),(⟨3,3,2⟩,[0,0,786432,-18874368,160432128,-509607936,-158859264,3944742912,-4595908608,-6738149376,11136663552]),(⟨3,3,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,4,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,0,0⟩,[-32768,1048576,-11468800,50462720,4227072,-1083834368,6163005440,-22002008064,58902216704,-111180775424,126322802688,-91804270592,175843540992,-382121148416,290308358144]),(⟨4,0,1⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,0⟩,[0,0,0,1572864,-34996224,300810240,-1236795392,2122842112,839647232,-5972426752,-3004694528,7242514432,50446598144,-76474875904]),(⟨4,1,1⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨4,1,2⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,2,2⟩,[131072,-3407872,33161216,-149946368,333709312,-498597888,916717568,454033408,-7497711616,10197139456,-1637744640]),(⟨4,3,3⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,458752,-11206656,110755840,-602734592,2139422720,-5785911296,12785025024,-19900530688,14819590144,-5058789376,31180062720,-49943216128,2013462528]),(⟨5,1,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨5,2,2⟩,[0,-786432,14680064,-101711872,362807296,-881328128,1461714944,930086912,-9388949504,10824712192]),(⟨6,0,0⟩,[0,0,-1572864,26607616,-194904064,861405184,-2754084864,6712197120,-10838343680,8153202688,-3591372800,20988690432,-32246726656])]


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
    (Poly.add (Poly.scale (K.ofRat r633) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 11 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r632*r632 : ℚ)=r633 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 11 13 r632 r632 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 11=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 11 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C146

#print axioms Coulomb8.Columns.C146.sound
