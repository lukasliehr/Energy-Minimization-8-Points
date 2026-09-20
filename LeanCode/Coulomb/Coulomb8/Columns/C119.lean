import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C119

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2277376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -35291136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 46923776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2106490880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 10212458496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -40093679616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 18951897088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -372800094208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 17941020672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1713305321472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 2710141927424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -3347423330304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 2965807906816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1597547741184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 374101966848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -28047310848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 999424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -21135360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 34209792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1751564288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 9320677376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -39367081984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 19802816512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -410157957120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 143692808192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -287932907520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 3245179273216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -4016992894976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 3445879914496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -33534967808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 31764578304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -4636672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 8781824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -462028800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 2275164160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -8218460160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 3370057728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -7650017280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 84753956864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -54941073408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -137922740224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 78521040896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1010529550336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1012533870592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -59249983488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -376832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 48431104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -462290944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 2795356160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -1766440960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 44118048768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -129685127168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 305701339136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -567084367872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 116471562240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -832342589440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 64508182528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -26576601088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -2916352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 77922304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 10108928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -1419640832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 8393523200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -32955564032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 94032052224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -199082835968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 45993132032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -7285964800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 27092205568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -1540096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 202964992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -960299008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 3412721664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -9932570624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 21679439872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -34413903872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 42156752896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -27647901696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -744292352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -5439488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 55312384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -314310656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 1297743872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -4293525504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 10579869696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2754871296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 27375894528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -21854093312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 59146240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -449052672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 357335040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -1753481216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 53646786560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -27447525376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 544228311040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -1231467839488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 2202652934144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2875270627328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 2335420284928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -122808434688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -147456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 20283392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -201785344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 1263386624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -5765185536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 20860174336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -8615100416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 135380320256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -227535962112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 253118742528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -88593203200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1623474176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 4418224128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -76054528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 484835328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -2437611520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 11155800064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -40930705408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 110343487488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -227983065088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 363375099904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -54232711168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 26124353536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 8060928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -108789760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 95682560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -2143944704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 4008312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -4012638208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -8216903680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 41044738048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -370868224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -77004800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 9764864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -1862172672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 111804416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -13962444800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 27530493952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -1830322176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 493944832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 49978343424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -44490489856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -1530298368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 1900544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -31948800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 253427712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -1200422912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 4187619328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -12015042560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 25743458304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -35553705984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 25494618112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 9055928320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -4347330560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 16580608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -74973184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 166854656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -249298944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 458358784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 227016704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -3748855808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 728367104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -983040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 181403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -440664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 42991616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 465043456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -4694474752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 45481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -10485760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 101187584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -548405248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 2340683776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -8666480640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 3304587264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -40866152448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 51382714368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -38139854848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -15237120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 37060608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -2152366080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 10167582720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -30113071104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 60167356416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -9976086528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -62198218752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 482936979456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -17860362240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 683900928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -4030464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 50954240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -48988160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1329102848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -2960064512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 3091136512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 342949888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -14854979584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 23405559808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -24570265600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 49491836928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -469139456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 20938752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -163807232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 2424832, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1642921984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 1764687872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 98107392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -12443287552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 23226580992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -7256571904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -121536512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -46891008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 239599616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -599326720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 519045120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 898170880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -540540928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 6292733952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -392953856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -3506176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 155451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -472776704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 748552192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -363069440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -2118909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 7422279680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -62980096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -2424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 36503552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -293273600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 197001216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -3850502144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 5734793216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -616955904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -18001100800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 46224834560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -8556969984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 40960000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -6717440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 242745344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -626065408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 603979776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 924647424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -4441243648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 7058718720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -232521728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -5734400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 983040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1572864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 179699712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 271319040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 241827840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -7208435712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -293535744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 4110286848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -29687808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 1138688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -17645568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 23461888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1053245440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 5106229248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -20046839808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 9475948544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -186400047104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 8970510336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -856652660736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 1355070963712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -1673711665152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 1482903953408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -798773870592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 187050983424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -14023655424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 499712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -10567680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 17104896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -875782144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 4660338688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -19683540992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 9901408256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -205078978560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 71846404096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -143966453760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 1622589636608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -2008496447488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 1722939957248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -16767483904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 15882289152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -2318336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 4390912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -231014400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 1137582080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -4109230080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 1685028864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -3825008640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 42376978432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -27470536704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -68961370112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 39260520448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -505264775168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 506266935296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -29624991744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 24215552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -231145472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 1397678080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -883220480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 22059024384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -64842563584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 152850669568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -283542183936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 58235781120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -416171294720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 32254091264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -13288300544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -1458176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 38961152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 5054464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -709820416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 4196761600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -16477782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 47016026112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -99541417984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 22996566016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -3642982400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 13546102784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -770048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 101482496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -480149504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 1706360832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -4966285312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 10839719936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -17206951936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 21078376448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -13823950848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -372146176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -2719744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 27656192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -157155328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 648871936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -2146762752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 5289934848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1377435648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 13687947264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -10927046656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 29573120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -224526336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 178667520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -876740608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 26823393280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -13723762688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 272114155520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -615733919744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1101326467072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -1437635313664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1167710142464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -61404217344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 10141696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -100892672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 631693312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -2882592768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 10430087168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -4307550208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 67690160128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -113767981056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 126559371264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -44296601600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -811737088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 2209112064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -38027264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 242417664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -1218805760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 5577900032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -20465352704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 55171743744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -113991532544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 181687549952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -27116355584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 13062176768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 4030464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -54394880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 47841280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -1071972352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 2004156416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -2006319104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -4108451840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 20522369024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -185434112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 3309568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -38502400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 4882432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -931086336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 55902208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -6981222400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 13765246976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -915161088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 246972416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 24989171712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -22245244928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -765149184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -15974400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 126713856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -600211456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 2093809664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -6007521280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 12871729152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -17776852992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 12747309056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 4527964160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -2173665280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 8290304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -37486592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 83427328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -124649472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 229179392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 113508352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -1874427904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 364183552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -491520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 90701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -220332032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 21495808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 232521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -2347237376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 22740992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -5242880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 50593792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -274202624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 1170341888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -4333240320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 1652293632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -20433076224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 25691357184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -19069927424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -7618560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 18530304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -1076183040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 5083791360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -15056535552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 30083678208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -4988043264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -31099109376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 241468489728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -8930181120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 341950464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -2015232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 25477120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -24494080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 664551424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -1480032256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 1545568256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 171474944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -7427489792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 11702779904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -12285132800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 24745918464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -234569728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 10469376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -81903616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 1212416, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -821460992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 882343936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 49053696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -6221643776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 11613290496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -3628285952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -60768256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -23445504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 119799808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -299663360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 259522560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 449085440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -270270464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 3146366976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -196476928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -1753088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 77725696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -236388352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 374276096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -181534720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -1059454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 3711139840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -31490048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 18251776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -146636800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 98500608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -1925251072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 2867396608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -308477952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -9000550400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 23112417280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -4278484992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 20480000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -3358720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 121372672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -313032704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 301989888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 462323712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -2220621824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 3529359360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -116260864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -2867200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -2555904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 491520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -786432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 89849856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 135659520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 120913920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -3604217856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -146767872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 2055143424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -14843904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74],[r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86],[0,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96],[],[],[],[],[],[],[0,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124],[0,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136],[0,0,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146],[],[],[],[],[],[],[],[r125,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158],[r75,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169],[r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180],[0,r181,r182,r183,r184,r185,r186,r187,r188,r189],[],[],[],[],[],[0,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211],[r97,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223],[r224,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235],[r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246],[r0,r63,r247,r248,r249,r250,r251,r252,r253,r254],[],[],[],[],[],[r170,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265],[r236,r237,r266,r267,r268,r269,r270,r271,r272,r273,r274],[r0,r63,r247,r248,r249,r250,r251,r252,r253,r254],[],[],[],[],[],[],[r97,r275,r276,r277,r247,r278,r279,r280,131072],[],[],[],[],[],[],[],[],[],[],[r87,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290],[0,r181,r182,r183,r184,r185,r186,r187,r188,r189],[],[],[],[],[],[r97,r275,r276,r277,r247,r278,r279,r280,131072],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r75,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨0,0,1⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322]),(⟨0,0,2⟩,[r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,0,3⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,0,4⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,0,5⟩,[r17,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,0,6⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,1,0⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322]),(⟨0,1,1⟩,[0,r170,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,1,2⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,1,3⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨0,1,4⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨0,2,0⟩,[r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,2,1⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,2,2⟩,[r413,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨0,2,3⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨0,2,4⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨0,2,5⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,3,0⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,3,1⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨0,3,2⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨0,3,3⟩,[0,r87,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨0,4,0⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,4,1⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨0,4,2⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨0,5,0⟩,[r17,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,5,2⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,6,0⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨1,0,0⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322]),(⟨1,0,1⟩,[0,r170,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,0,2⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨1,0,3⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨1,0,4⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨1,1,0⟩,[0,r170,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,1,1⟩,[0,0,r33,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨1,1,2⟩,[r170,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,1,3⟩,[r111,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,1,4⟩,[r62,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨1,1,5⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨1,2,0⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨1,2,1⟩,[r170,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,2,2⟩,[r224,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨1,2,3⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨1,2,4⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨1,3,0⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨1,3,1⟩,[r111,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨1,3,2⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨1,3,4⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨1,4,0⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨1,4,1⟩,[r62,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨1,4,2⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨1,4,3⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨1,5,1⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨2,0,0⟩,[r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨2,0,1⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨2,0,2⟩,[r413,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨2,0,3⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨2,0,4⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨2,0,5⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨2,1,0⟩,[r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨2,1,1⟩,[r170,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨2,1,2⟩,[r224,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,1,3⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨2,1,4⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨2,2,0⟩,[r413,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨2,2,1⟩,[r224,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,2,2⟩,[r376,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572]),(⟨2,2,3⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨2,3,0⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨2,3,1⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨2,3,2⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨2,3,3⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨2,4,0⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨2,4,1⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨2,5,0⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨3,0,0⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨3,0,1⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨3,0,2⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨3,0,3⟩,[0,r87,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨3,1,0⟩,[0,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨3,1,1⟩,[r111,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518]),(⟨3,1,2⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨3,1,4⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨3,2,0⟩,[r17,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨3,2,1⟩,[r62,r519,r548,r549,r550,r551,r552,r553,r554,r555,r556]),(⟨3,2,2⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨3,2,3⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨3,3,0⟩,[0,r87,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨3,3,2⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨3,4,1⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨4,0,0⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨4,0,1⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨4,0,2⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨4,1,0⟩,[0,0,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨4,1,1⟩,[r62,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨4,1,2⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨4,1,3⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨4,2,0⟩,[r224,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467]),(⟨4,2,1⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨4,3,1⟩,[r170,r557,r558,r559,r529,r560,r561,r562,65536]),(⟨5,0,0⟩,[r17,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨5,0,2⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨5,1,1⟩,[r75,r353,r529,r530,r531,r532,r533,r534,r535,r536]),(⟨5,2,0⟩,[0,r137,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨6,0,0⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r573) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r573) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[40960,-1277952,17039360,-130924544,675323904,-2646261760,8607039488,-23561076736,52003856384,-88208637952,109226950656,-85253734400,17597915136,25184649216,-7068450816]),(⟨2,0,1⟩,[0,-163840,4128768,-43958272,275709952,-1236582400,4502192128,-13487800320,31368282112,-54091579392,66118418432,-47552774144,1817116672,19843203072]),(⟨2,0,2⟩,[-73728,2113536,-24510464,152158208,-589438976,1702002688,-4206952448,7990902784,-7991418880,-4128686080,24168038400,-25968590848,5136359424]),(⟨2,0,3⟩,[0,376832,-8257536,73023488,-367788032,1323663360,-3823632384,8002240512,-9337831424,448315392,15458500608,-16868884480]),(⟨2,0,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,0,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,1,0⟩,[0,-163840,4128768,-43958272,275709952,-1236582400,4502192128,-13487800320,31368282112,-54091579392,66118418432,-47552774144,1817116672,19843203072]),(⟨2,1,1⟩,[0,0,-245760,6684672,-70336512,359399424,-898990080,778567680,1347256320,-5675679744,9439100928,-4126015488,-4380966912]),(⟨2,1,2⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨2,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨2,2,0⟩,[-73728,2113536,-24510464,152158208,-589438976,1702002688,-4206952448,7990902784,-7991418880,-4128686080,24168038400,-25968590848,5136359424]),(⟨2,2,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨2,2,2⟩,[65536,-1703936,16580608,-74973184,166854656,-249298944,458358784,227016704,-3748855808,5098569728,-818872320]),(⟨2,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,0⟩,[0,376832,-8257536,73023488,-367788032,1323663360,-3823632384,8002240512,-9337831424,448315392,15458500608,-16868884480]),(⟨2,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨2,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,4,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,5,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,0,0⟩,[16384,-770048,13254656,-120946688,705953792,-3056680960,10883989504,-32337362944,77141131264,-144048275456,206061256704,-204476874752,101489016832,1704935424]),(⟨3,0,1⟩,[0,-65536,1785856,-17858560,97992704,-454819840,2295758848,-9595977728,28123365376,-60015706112,95169167360,-97847115776,46538440704]),(⟨3,0,2⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨3,0,3⟩,[0,98304,-2523136,22937600,-117047296,521469952,-2186477568,6276120576,-10791026688,12003409920,-8142880768]),(⟨3,1,0⟩,[0,-65536,1785856,-17858560,97992704,-454819840,2295758848,-9595977728,28123365376,-60015706112,95169167360,-97847115776,46538440704]),(⟨3,1,1⟩,[0,0,-98304,3244032,-39714816,233177088,-709165056,1122828288,-544604160,-3178364928,11133419520,-11241947136]),(⟨3,1,2⟩,[-81920,2228224,-23248896,115081216,-259555328,132120576,409370624,-905707520,1997389824,-3059875840,1323843584]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨3,2,1⟩,[-81920,2228224,-23248896,115081216,-259555328,132120576,409370624,-905707520,1997389824,-3059875840,1323843584]),(⟨3,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,98304,-2523136,22937600,-117047296,521469952,-2186477568,6276120576,-10791026688,12003409920,-8142880768]),(⟨3,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[-40960,1130496,-11960320,62537728,-172531712,204111872,580911104,-5109809152,19050930176,-46019624960,81955291136,-96735903744,51563667456]),(⟨4,0,1⟩,[0,0,-98304,3244032,-39714816,233177088,-709165056,1122828288,-544604160,-3178364928,11133419520,-11241947136]),(⟨4,0,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,1,0⟩,[0,0,-98304,3244032,-39714816,233177088,-709165056,1122828288,-544604160,-3178364928,11133419520,-11241947136]),(⟨4,1,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,1,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,2,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨5,0,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨5,1,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,2,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,0,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[16384,-606208,9125888,-76988416,430243840,-1820098560,6381797376,-18849562624,45772849152,-89956696064,139942838272,-156924100608,99671900160,-18138267648]),(⟨0,3,1⟩,[0,-65536,2031616,-24543232,168329216,-814219264,3194748928,-10374545408,26776109056,-54340026368,85730066432,-93721100288,50919407616]),(⟨0,3,2⟩,[-16384,573440,-7716864,53690368,-232423424,770146304,-2183888896,4869488640,-8439021568,12298993664,-10930536448,1653227520]),(⟨0,3,3⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656]),(⟨0,4,0⟩,[0,-65536,2031616,-24543232,168329216,-814219264,3194748928,-10374545408,26776109056,-54340026368,85730066432,-93721100288,50919407616]),(⟨0,4,1⟩,[0,0,-98304,3244032,-39714816,233177088,-709165056,1122828288,-544604160,-3178364928,11133419520,-11241947136]),(⟨0,5,0⟩,[-16384,573440,-7716864,53690368,-232423424,770146304,-2183888896,4869488640,-8439021568,12298993664,-10930536448,1653227520]),(⟨0,6,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656]),(⟨1,0,0⟩,[-8192,368640,-6799360,71303168,-495198208,2529075200,-10303160320,35187654656,-101863677952,247048232960,-494836137984,803217014784,-1008152305664,883284959232,-440373755904,71807533056]),(⟨1,0,1⟩,[0,32768,-1146880,15974400,-130007040,767508480,-3725869056,15085043712,-49495638016,132248829952,-295070859264,536978440192,-717082640384,591373484032,-219553087488]),(⟨1,0,2⟩,[8192,-352256,5963776,-54919168,324280320,-1388208128,4713545728,-13196001280,30458929152,-56165670912,73086926848,-43909054464,-25961865216,43897577472]),(⟨1,0,3⟩,[0,-49152,1622016,-20168704,144424960,-763985920,3282141184,-10869374976,27048378368,-53975826432,86518382592,-91967373312,44896796672]),(⟨1,0,4⟩,[0,0,0,786432,-14680064,101711872,-362807296,881328128,-1461714944,-930086912,9388949504,-10824712192]),(⟨1,1,0⟩,[0,32768,-1146880,15974400,-130007040,767508480,-3725869056,15085043712,-49495638016,132248829952,-295070859264,536978440192,-717082640384,591373484032,-219553087488]),(⟨1,1,1⟩,[0,0,49152,-3063808,54771712,-459653120,2174844928,-6568640512,14192836608,-19766804480,-8086765568,113813766144,-219267284992,145390780416]),(⟨1,1,2⟩,[0,0,-131072,3407872,-33947648,168820736,-494141440,1008205824,-757858304,-4398776320,12093620224,-3458990080,-9498918912]),(⟨1,1,3⟩,[0,0,0,786432,-14680064,101711872,-362807296,881328128,-1461714944,-930086912,9388949504,-10824712192]),(⟨1,2,0⟩,[8192,-352256,5963776,-54919168,324280320,-1388208128,4713545728,-13196001280,30458929152,-56165670912,73086926848,-43909054464,-25961865216,43897577472]),(⟨1,2,1⟩,[0,0,-131072,3407872,-33947648,168820736,-494141440,1008205824,-757858304,-4398776320,12093620224,-3458990080,-9498918912]),(⟨1,3,0⟩,[0,-114688,3653632,-44711936,312754176,-1578205184,6476890112,-21243920384,53824487424,-108315852800,172248449024,-185688473600,95816204288]),(⟨1,3,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨1,4,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨1,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,5,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,0,0⟩,[40960,-1245184,15761408,-111280128,503242752,-1618444288,3886858240,-5741346816,-3864240128,54944858112,-186908868608,401928355840,-587713470464,524742983680,-208653139968]),(⟨2,0,1⟩,[0,-163840,4177920,-46497792,318947328,-1595310080,6196789248,-18506645504,41396174848,-65730347008,55752048640,32936722432,-144042508288,114791448576]),(⟨2,0,2⟩,[-73728,2113536,-24510464,152158208,-590225408,1720877056,-4367384576,8500510720,-7832559616,-8073428992,28763947008,-19230441472,-6000304128]),(⟨2,0,3⟩,[0,376832,-8257536,73023488,-367788032,1323663360,-3823632384,8002240512,-9337831424,448315392,15458500608,-16868884480]),(⟨2,0,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,0,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,1,0⟩,[0,-163840,4177920,-46497792,318947328,-1595310080,6196789248,-18506645504,41396174848,-65730347008,55752048640,32936722432,-144042508288,114791448576]),(⟨2,1,1⟩,[0,0,-245760,6684672,-71909376,397148160,-1219854336,1797783552,1664974848,-13565165568,18630918144,9350283264,-26654294016]),(⟨2,1,2⟩,[16384,-540672,7684096,-60702720,284721152,-768901120,913080320,861765632,-4785225728,7390674944,-5798739968,2224603136]),(⟨2,1,3⟩,[0,0,-65536,1572864,-13369344,42467328,13238272,-328728576,382992384,561512448,-928055296]),(⟨2,2,0⟩,[-73728,2113536,-24510464,152158208,-590225408,1720877056,-4367384576,8500510720,-7832559616,-8073428992,28763947008,-19230441472,-6000304128]),(⟨2,2,1⟩,[16384,-540672,7684096,-60702720,284721152,-768901120,913080320,861765632,-4785225728,7390674944,-5798739968,2224603136]),(⟨2,2,2⟩,[65536,-1703936,16056320,-62390272,59899904,90439680,564264960,-2402811904,-684916736,9590669312,-8243314688]),(⟨2,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,0⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨2,3,1⟩,[0,0,-65536,1572864,-13369344,42467328,13238272,-328728576,382992384,561512448,-928055296]),(⟨2,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,4,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,5,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,0,0⟩,[24576,-1122304,19218432,-175341568,1018699776,-4343963648,15117287424,-43983568896,103435116544,-192085909504,276868579328,-281710198784,148934811648,-4840022016]),(⟨3,0,1⟩,[0,-65536,1654784,-14450688,64831488,-304873472,1962049536,-9097379840,27206647808,-60469739520,102666878976,-108044255232,48176185344]),(⟨3,0,2⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨3,0,3⟩,[0,98304,-2523136,22937600,-117047296,521469952,-2186477568,6276120576,-10791026688,12003409920,-8142880768]),(⟨3,1,0⟩,[0,-65536,1654784,-14450688,64831488,-304873472,1962049536,-9097379840,27206647808,-60469739520,102666878976,-108044255232,48176185344]),(⟨3,1,1⟩,[16384,-671744,10469376,-82690048,365068288,-923172864,1245151232,-47415296,-4759928832,12543377408,-13017235456,3593289728]),(⟨3,1,2⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨3,2,1⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,196608,-5242880,50593792,-274202624,1170341888,-4333240320,11566055424,-20433076224,25691357184,-19069927424]),(⟨3,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨4,0,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,0,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,1,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,1,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,1,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,2,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨5,0,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨5,1,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,2,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,0,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-8192,368640,-6799360,71303168,-495198208,2529075200,-10303160320,35187654656,-101863677952,247048232960,-494836137984,803217014784,-1008152305664,883284959232,-440373755904,71807533056]),(⟨0,1,1⟩,[0,32768,-1146880,15974400,-130007040,767508480,-3725869056,15085043712,-49495638016,132248829952,-295070859264,536978440192,-717082640384,591373484032,-219553087488]),(⟨0,1,2⟩,[8192,-352256,5963776,-54919168,324280320,-1388208128,4713545728,-13196001280,30458929152,-56165670912,73086926848,-43909054464,-25961865216,43897577472]),(⟨0,1,3⟩,[0,-49152,1622016,-20168704,144424960,-763985920,3282141184,-10869374976,27048378368,-53975826432,86518382592,-91967373312,44896796672]),(⟨0,1,4⟩,[0,0,0,786432,-14680064,101711872,-362807296,881328128,-1461714944,-930086912,9388949504,-10824712192]),(⟨0,2,0⟩,[40960,-1245184,15761408,-111280128,503242752,-1618444288,3886858240,-5741346816,-3864240128,54944858112,-186908868608,401928355840,-587713470464,524742983680,-208653139968]),(⟨0,2,1⟩,[0,-163840,4177920,-46497792,318947328,-1595310080,6196789248,-18506645504,41396174848,-65730347008,55752048640,32936722432,-144042508288,114791448576]),(⟨0,2,2⟩,[-73728,2113536,-24510464,152158208,-590225408,1720877056,-4367384576,8500510720,-7832559616,-8073428992,28763947008,-19230441472,-6000304128]),(⟨0,2,3⟩,[0,376832,-8257536,73023488,-367788032,1323663360,-3823632384,8002240512,-9337831424,448315392,15458500608,-16868884480]),(⟨0,2,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,2,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,3,0⟩,[24576,-1122304,19218432,-175341568,1018699776,-4343963648,15117287424,-43983568896,103435116544,-192085909504,276868579328,-281710198784,148934811648,-4840022016]),(⟨0,3,1⟩,[0,-65536,1654784,-14450688,64831488,-304873472,1962049536,-9097379840,27206647808,-60469739520,102666878976,-108044255232,48176185344]),(⟨0,3,2⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨0,3,3⟩,[0,98304,-2523136,22937600,-117047296,521469952,-2186477568,6276120576,-10791026688,12003409920,-8142880768]),(⟨0,4,0⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨0,4,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨0,4,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,5,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨0,5,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,6,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656]),(⟨1,0,0⟩,[-8192,368640,-6799360,71303168,-495198208,2529075200,-10303160320,35187654656,-101863677952,247048232960,-494836137984,803217014784,-1008152305664,883284959232,-440373755904,71807533056]),(⟨1,0,1⟩,[0,32768,-1146880,15974400,-130007040,767508480,-3725869056,15085043712,-49495638016,132248829952,-295070859264,536978440192,-717082640384,591373484032,-219553087488]),(⟨1,0,2⟩,[8192,-352256,5963776,-54919168,324280320,-1388208128,4713545728,-13196001280,30458929152,-56165670912,73086926848,-43909054464,-25961865216,43897577472]),(⟨1,0,3⟩,[0,-49152,1622016,-20168704,144424960,-763985920,3282141184,-10869374976,27048378368,-53975826432,86518382592,-91967373312,44896796672]),(⟨1,0,4⟩,[0,0,0,786432,-14680064,101711872,-362807296,881328128,-1461714944,-930086912,9388949504,-10824712192]),(⟨1,1,0⟩,[0,65536,-2424832,35618816,-302088192,1795325952,-8446050304,32904773632,-105363734528,275402326016,-591206678528,1024160530432,-1322394025984,1090931818496,-421137776640]),(⟨1,1,1⟩,[0,0,98304,-5603328,98009088,-818380800,3869442048,-11587485696,24220729344,-31405572096,-18453135360,194303262720,-365126909952,240339025920]),(⟨1,1,2⟩,[0,0,-131072,3407872,-34734080,187695104,-654573568,1517813760,-598999040,-8343519232,16689528832,3279159296,-20635582464]),(⟨1,1,3⟩,[0,0,0,786432,-14680064,101711872,-362807296,881328128,-1461714944,-930086912,9388949504,-10824712192]),(⟨1,2,0⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨1,2,1⟩,[0,0,-376832,10092544,-105070592,547094528,-1553563648,2296381440,748257280,-14019198976,26128629760,-846856192,-25016549376]),(⟨1,2,2⟩,[16384,-540672,7684096,-60702720,284721152,-768901120,913080320,861765632,-4785225728,7390674944,-5798739968,2224603136]),(⟨1,2,3⟩,[0,0,-65536,1572864,-13369344,42467328,13238272,-328728576,382992384,561512448,-928055296]),(⟨1,3,0⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨1,3,1⟩,[16384,-671744,10469376,-81903616,350388224,-821460992,882343936,833912832,-6221643776,11613290496,-3628285952,-7231422464]),(⟨1,3,2⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨1,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨1,4,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨1,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,0,0⟩,[40960,-1245184,15761408,-111280128,503242752,-1618444288,3886858240,-5741346816,-3864240128,54944858112,-186908868608,401928355840,-587713470464,524742983680,-208653139968]),(⟨2,0,1⟩,[0,-163840,4177920,-46497792,318947328,-1595310080,6196789248,-18506645504,41396174848,-65730347008,55752048640,32936722432,-144042508288,114791448576]),(⟨2,0,2⟩,[-73728,2113536,-24510464,152158208,-590225408,1720877056,-4367384576,8500510720,-7832559616,-8073428992,28763947008,-19230441472,-6000304128]),(⟨2,0,3⟩,[0,376832,-8257536,73023488,-367788032,1323663360,-3823632384,8002240512,-9337831424,448315392,15458500608,-16868884480]),(⟨2,0,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,0,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,1,0⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨2,1,1⟩,[0,0,-376832,10092544,-105070592,547094528,-1553563648,2296381440,748257280,-14019198976,26128629760,-846856192,-25016549376]),(⟨2,1,2⟩,[16384,-540672,7684096,-60702720,284721152,-768901120,913080320,861765632,-4785225728,7390674944,-5798739968,2224603136]),(⟨2,1,3⟩,[0,0,-65536,1572864,-13369344,42467328,13238272,-328728576,382992384,561512448,-928055296]),(⟨2,2,0⟩,[-114688,3309568,-38502400,239239168,-931086336,2739208192,-6981222400,13765246976,-15557738496,246972416,24989171712,-22245244928,-5356044288]),(⟨2,2,1⟩,[32768,-1212416,18251776,-146636800,689504256,-1925251072,2867396608,-308477952,-9000550400,23112417280,-29949394944,17059840000]),(⟨2,2,2⟩,[98304,-2555904,24084480,-93585408,89849856,135659520,846397440,-3604217856,-1027375104,14386003968,-12364972032]),(⟨2,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,0⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨2,3,1⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨2,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,5,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,0,0⟩,[24576,-1122304,19218432,-175341568,1018699776,-4343963648,15117287424,-43983568896,103435116544,-192085909504,276868579328,-281710198784,148934811648,-4840022016]),(⟨3,0,1⟩,[0,-65536,1654784,-14450688,64831488,-304873472,1962049536,-9097379840,27206647808,-60469739520,102666878976,-108044255232,48176185344]),(⟨3,0,2⟩,[-16384,704512,-10600448,78921728,-352485376,1157595136,-3225124864,6901497856,-9008922624,3967926272,7421378560,-10957406208]),(⟨3,0,3⟩,[0,98304,-2523136,22937600,-117047296,521469952,-2186477568,6276120576,-10791026688,12003409920,-8142880768]),(⟨3,1,0⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨3,1,1⟩,[16384,-671744,10469376,-81903616,350388224,-821460992,882343936,833912832,-6221643776,11613290496,-3628285952,-7231422464]),(⟨3,1,2⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨3,2,1⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,2,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,196608,-5242880,50593792,-274202624,1170341888,-4333240320,11566055424,-20433076224,25691357184,-19069927424]),(⟨3,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨4,0,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,0,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,1,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,1,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,1,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,2,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨5,0,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨5,1,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,2,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,0,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1138688,-17645568,164233216,-1053245440,5106229248,-20046839808,66331639808,-186400047104,439555006464,-856652660736,1355070963712,-1673711665152,1482903953408,-798773870592,187050983424,-14023655424]),(⟨0,0,1⟩,[-8192,499712,-10567680,119734272,-875782144,4660338688,-19683540992,69309857792,-205078978560,502924828672,-1007765176320,1622589636608,-2008496447488,1722939957248,-821606711296,111176024064]),(⟨0,0,2⟩,[73728,-2318336,30736384,-231014400,1137582080,-4109230080,11795202048,-26775060480,42376978432,-27470536704,-68961370112,274823643136,-505264775168,506266935296,-207374942208]),(⟨0,0,3⟩,[24576,-1318912,24215552,-231145472,1397678080,-6182543360,22059024384,-64842563584,152850669568,-283542183936,407650467840,-416171294720,225778638848,-13288300544]),(⟨0,0,4⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨0,0,5⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨0,0,6⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656]),(⟨0,1,0⟩,[-8192,499712,-10567680,119734272,-875782144,4660338688,-19683540992,69309857792,-205078978560,502924828672,-1007765176320,1622589636608,-2008496447488,1722939957248,-821606711296,111176024064]),(⟨0,1,1⟩,[0,65536,-2228224,29573120,-224526336,1250672640,-6137184256,26823393280,-96066338816,272114155520,-615733919744,1101326467072,-1437635313664,1167710142464,-429829521408]),(⟨0,1,2⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨0,1,3⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨0,1,4⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨0,2,0⟩,[73728,-2318336,30736384,-231014400,1137582080,-4109230080,11795202048,-26775060480,42376978432,-27470536704,-68961370112,274823643136,-505264775168,506266935296,-207374942208]),(⟨0,2,1⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨0,2,2⟩,[-114688,3309568,-38502400,239239168,-931086336,2739208192,-6981222400,13765246976,-15557738496,246972416,24989171712,-22245244928,-5356044288]),(⟨0,2,3⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨0,2,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,2,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,3,0⟩,[24576,-1318912,24215552,-231145472,1397678080,-6182543360,22059024384,-64842563584,152850669568,-283542183936,407650467840,-416171294720,225778638848,-13288300544]),(⟨0,3,1⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨0,3,2⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨0,3,3⟩,[0,196608,-5242880,50593792,-274202624,1170341888,-4333240320,11566055424,-20433076224,25691357184,-19069927424]),(⟨0,4,0⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨0,4,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨0,4,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,5,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨0,5,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,6,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656]),(⟨1,0,0⟩,[-8192,499712,-10567680,119734272,-875782144,4660338688,-19683540992,69309857792,-205078978560,502924828672,-1007765176320,1622589636608,-2008496447488,1722939957248,-821606711296,111176024064]),(⟨1,0,1⟩,[0,65536,-2228224,29573120,-224526336,1250672640,-6137184256,26823393280,-96066338816,272114155520,-615733919744,1101326467072,-1437635313664,1167710142464,-429829521408]),(⟨1,0,2⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨1,0,3⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨1,0,4⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨1,1,0⟩,[0,65536,-2228224,29573120,-224526336,1250672640,-6137184256,26823393280,-96066338816,272114155520,-615733919744,1101326467072,-1437635313664,1167710142464,-429829521408]),(⟨1,1,1⟩,[0,0,147456,-7618560,129712128,-1076183040,5083791360,-15056535552,30083678208,-34916302848,-31099109376,241468489728,-437578874880,284844736512]),(⟨1,1,2⟩,[65536,-2015232,25477120,-171458560,664551424,-1480032256,1545568256,1200324608,-7427489792,11702779904,-12285132800,24745918464,-27913797632]),(⟨1,1,3⟩,[16384,-671744,10469376,-81903616,350388224,-821460992,882343936,833912832,-6221643776,11613290496,-3628285952,-7231422464]),(⟨1,1,4⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨1,1,5⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,2,0⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨1,2,1⟩,[65536,-2015232,25477120,-171458560,664551424,-1480032256,1545568256,1200324608,-7427489792,11702779904,-12285132800,24745918464,-27913797632]),(⟨1,2,2⟩,[32768,-1212416,18251776,-146636800,689504256,-1925251072,2867396608,-308477952,-9000550400,23112417280,-29949394944,17059840000]),(⟨1,2,3⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨1,2,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,3,0⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨1,3,1⟩,[16384,-671744,10469376,-81903616,350388224,-821460992,882343936,833912832,-6221643776,11613290496,-3628285952,-7231422464]),(⟨1,3,2⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨1,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨1,4,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨1,4,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨1,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,0,0⟩,[73728,-2318336,30736384,-231014400,1137582080,-4109230080,11795202048,-26775060480,42376978432,-27470536704,-68961370112,274823643136,-505264775168,506266935296,-207374942208]),(⟨2,0,1⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨2,0,2⟩,[-114688,3309568,-38502400,239239168,-931086336,2739208192,-6981222400,13765246976,-15557738496,246972416,24989171712,-22245244928,-5356044288]),(⟨2,0,3⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨2,0,4⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,0,5⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,1,0⟩,[8192,-516096,10141696,-100892672,631693312,-2882592768,10430087168,-30152851456,67690160128,-113767981056,126559371264,-44296601600,-96596713472,108246491136]),(⟨2,1,1⟩,[65536,-2015232,25477120,-171458560,664551424,-1480032256,1545568256,1200324608,-7427489792,11702779904,-12285132800,24745918464,-27913797632]),(⟨2,1,2⟩,[32768,-1212416,18251776,-146636800,689504256,-1925251072,2867396608,-308477952,-9000550400,23112417280,-29949394944,17059840000]),(⟨2,1,3⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨2,1,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,2,0⟩,[-114688,3309568,-38502400,239239168,-931086336,2739208192,-6981222400,13765246976,-15557738496,246972416,24989171712,-22245244928,-5356044288]),(⟨2,2,1⟩,[32768,-1212416,18251776,-146636800,689504256,-1925251072,2867396608,-308477952,-9000550400,23112417280,-29949394944,17059840000]),(⟨2,2,2⟩,[98304,-2555904,24084480,-93585408,89849856,135659520,846397440,-3604217856,-1027375104,14386003968,-12364972032]),(⟨2,2,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,0⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨2,3,1⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨2,3,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨2,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,5,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,0,0⟩,[24576,-1318912,24215552,-231145472,1397678080,-6182543360,22059024384,-64842563584,152850669568,-283542183936,407650467840,-416171294720,225778638848,-13288300544]),(⟨3,0,1⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨3,0,2⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨3,0,3⟩,[0,196608,-5242880,50593792,-274202624,1170341888,-4333240320,11566055424,-20433076224,25691357184,-19069927424]),(⟨3,1,0⟩,[0,-114688,3407872,-38027264,242417664,-1218805760,5577900032,-20465352704,55171743744,-113991532544,181687549952,-189814489088,91435237376]),(⟨3,1,1⟩,[16384,-671744,10469376,-81903616,350388224,-821460992,882343936,833912832,-6221643776,11613290496,-3628285952,-7231422464]),(⟨3,1,2⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[-16384,950272,-15974400,126713856,-600211456,2093809664,-6007521280,12871729152,-17776852992,12747309056,4527964160,-15215656960]),(⟨3,2,1⟩,[-81920,2228224,-23511040,121372672,-313032704,301989888,462323712,-2220621824,3529359360,-813826048,-2388377600]),(⟨3,2,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,196608,-5242880,50593792,-274202624,1170341888,-4333240320,11566055424,-20433076224,25691357184,-19069927424]),(⟨3,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[-40960,1081344,-10207232,38961152,5054464,-709820416,4196761600,-16477782016,47016026112,-99541417984,160975962112,-178506137600,94822719488]),(⟨4,0,1⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,0,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,1,0⟩,[0,0,-98304,4030464,-54394880,334888960,-1071972352,2004156416,-2006319104,-4108451840,20522369024,-22066659328]),(⟨4,1,1⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨4,1,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨4,2,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[-16384,819200,-13090816,101482496,-480149504,1706360832,-4966285312,10839719936,-17206951936,21078376448,-13823950848,-2605023232]),(⟨5,0,2⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨5,1,1⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,2,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,0,0⟩,[0,98304,-2719744,27656192,-157155328,648871936,-2146762752,5289934848,-9642049536,13687947264,-10927046656])]


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
    (Poly.add (Poly.scale (K.ofRat r574) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r573*r573 : ℚ)=r574 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 11 r573 r573 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C119

#print axioms Coulomb8.Columns.C119.sound
