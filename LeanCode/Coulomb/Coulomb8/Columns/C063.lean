import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C063

def r0 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -112512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1257792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -391296, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 21557952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -45756864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 63625056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -54009696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 20917632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 4093248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -5904960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 140928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 22976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -424064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 2881728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -11870272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 4704640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -63343008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 83628416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -71890880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 34632896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -664832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -295232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -2752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -64896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 549312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -2731648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 9091392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -20391264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 30541440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -4191680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 16360320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -596672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -21056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 1358400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -6237184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 2514880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -32283904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 38113344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -26596480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 8252672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 40000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 2272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -55616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 731008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -3568896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 10261184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -19012032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -2363424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 826784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -6208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 169600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -998016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 3032576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -5412032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 5598336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -2832672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 29184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 17216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -786752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 2476224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -4496896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 4628800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -324000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -54912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 194112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -323840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 37184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 197696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -331136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 37952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 9664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -244736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 301312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -1280640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 24241024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -44648896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 56853568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -48780864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 26072576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -994176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 5536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -71744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 384512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -1158464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 2066432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -1824640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -506848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 3307680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -527200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 228928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -1312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 734784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -506560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 10072064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -18473088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 22004544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -15892384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 796192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -16064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 93376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -233280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 161472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 495808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -1393856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 90432, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 42688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -264640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 908736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1796160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 282304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -145600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -27520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 25344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 50944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -157312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -118656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 498048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -1035904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 1168256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -83328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -31040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1451136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -2307072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 2016640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -699936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -17792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -34624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -14272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 187008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -1062144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 3065728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -5225344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 5105536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -341568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -105216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 380928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -714240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 364032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1565184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -651264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 6207744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -696576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -36352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 59904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -228864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 359936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 74752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -195072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 176640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 334336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1215488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1528320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 51712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -177152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 48, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -56256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 628896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -195648, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 10778976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -22878432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 31812528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -27004848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 10458816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 2046624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -2952480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 70464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 11488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -212032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1440864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -5935136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 2352320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -31671504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 41814208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -35945440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 17316448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -332416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -147616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -1376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -32448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 274656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -1365824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 4545696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -10195632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 15270720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -2095840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 8180160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -298336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -10528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 679200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -3118592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 1257440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -16141952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 19056672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -13298240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 4126336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 20000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 1136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -27808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 365504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1784448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 5130592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -9506016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -1181712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 413392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -3104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 84800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -499008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1516288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -2706016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 2799168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -1416336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 14592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 8608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -393376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 1238112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -2248448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 2314400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -162000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -27456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 97056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -161920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 18592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -27264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 98848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -165568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 18976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 4832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -122368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 150656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -640320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 12120512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -22324448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 28426784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -24390432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 13036288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -497088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 2768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -35872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 192256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -579232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 1033216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -912320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -253424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1653840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -263600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 114464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 367392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -253280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 5036032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -9236544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 11002272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -7946192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 398096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -8032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 46688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -116640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 80736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 247904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -696928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 45216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 21344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -132320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 454368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -898080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 141152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -72800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -13760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 25472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -78656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 6240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -12000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -59328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 249024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -517952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 584128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -41664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 49216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -15520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 725568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -1153536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 1008320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -349968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -8896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -17312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -7136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 93504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -531072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 1532864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -2612672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 2552768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -170784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -52608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 190464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -357120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 182016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 782592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -325632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 3103872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -348288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 29952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -114432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 179968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 37376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -97536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 88320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 167168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -607744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 764160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -88576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r14,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39],[r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51],[r40,r52,r53,r54,r55,r56,r57,r58,191744,r59,r60],[r61,r62,r63,r64,r65,r66,r67,r68,r69,r70],[r61,r71,r72,r73,r74,r75,r76,r77,r78],[r79,r72,r80,r81,r82,r83,r84,r85],[r79,r86,r87,r88,r89,r90,r91],[],[],[],[],[r92,r42,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103],[r104,r61,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114],[r40,r52,r115,r116,r117,r118,r119,r120,r121,r122,r123],[0,r124,r125,r126,r127,r128,r129,r130,r131,-6528],[0,r92,r132,r133,r134,r135,r136,r137,r138],[0,r139,r140,r141,r142,r143,r144,1408],[r145,r146,r147,r148,r149,r150,-576],[],[r40,r151,r152,r153,128],[],[],[0,0,r40,r154,r155,r156,r157,r158,r159,r160,r161],[r162,r163,r164,r165,r166,r167,r168,r169,r170,r171],[r79,r172,r173,r174,r175,r176,r177,r178,448],[r79,r72,r80,r81,r82,r83,r84,r85],[],[],[],[],[],[r145,r179,r180,r181,r182,r183,r184,r185,r186],[0,0,r40,r187,r188,r189,r190,-128],[r79,r86,r87,r88,r89,r90,r91],[],[],[],[],[r191,r192,r193,r194,r195,r196,-1152],[],[r40,r151,r152,r153,128],[],[],[],[],[],[],[0,r189,r197,r198,r199,r200,r201,r202,r203,r204,r205,16128],[0,0,0,r139,r206,r207,r208,r209,r210,r211,-1536],[0,r212,r213,r214,r215,r216,r217,r218,r219,-6912],[r40,r220,r213,r221,r222,r223,r224,r225,896],[0,r139,r226,r227,r228,r229,r230,1536],[],[],[],[],[],[],[],[0,0,r40,r187,r188,r189,r190,-128],[],[],[],[],[],[],[r145,r146,r147,r148,r149,r150,-576],[],[],[],[],[],[r40,r151,r152,r153,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,0,1⟩,[r245,r246,r187,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨0,0,2⟩,[r245,r258,r1,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,0,3⟩,[r79,r124,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨0,0,4⟩,[r79,r279,r280,r281,r282,r283,r284,r285,95872,r286,r287]),(⟨0,0,5⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨0,0,6⟩,[r288,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨0,0,7⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨0,0,8⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨0,1,0⟩,[r245,r246,r187,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨0,1,1⟩,[r14,r269,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,1,2⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨0,1,3⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,1,4⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨0,1,5⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨0,1,6⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨0,1,7⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨0,1,9⟩,[r79,r212,r375,r376,64]),(⟨0,2,0⟩,[r245,r258,r1,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,2,1⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨0,2,2⟩,[0,0,r79,r377,r378,r379,r380,r381,r382,r383,r221]),(⟨0,2,3⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,2,4⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨0,2,5⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨0,3,0⟩,[r79,r124,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨0,3,1⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,3,2⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,3,3⟩,[r162,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨0,3,4⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨0,3,5⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨0,4,0⟩,[r79,r279,r280,r281,r282,r283,r284,r285,95872,r286,r287]),(⟨0,4,1⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨0,4,2⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨0,4,3⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨0,4,4⟩,[r145,r146,r147,r148,r149,r150,-576]),(⟨0,4,6⟩,[r79,r212,r375,r376,64]),(⟨0,5,0⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨0,5,1⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨0,5,2⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨0,5,3⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨0,6,0⟩,[r288,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨0,6,1⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨0,6,4⟩,[r79,r212,r375,r376,64]),(⟨0,7,0⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨0,7,1⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨0,8,0⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨0,9,1⟩,[r79,r212,r375,r376,64]),(⟨1,0,0⟩,[r245,r246,r187,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨1,0,1⟩,[r14,r269,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,0,2⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨1,0,3⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨1,0,4⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨1,0,5⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨1,0,6⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨1,0,7⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨1,0,9⟩,[r79,r212,r375,r376,64]),(⟨1,1,0⟩,[r14,r269,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,1,1⟩,[0,r410,r412,r413,r414,r415,r416,r417,r418,r419,r420,8064]),(⟨1,1,2⟩,[0,0,0,r364,r421,r422,r423,r424,r425,r426,-768]),(⟨1,1,3⟩,[0,r191,r173,r427,r428,r429,r430,r431,r432,-3456]),(⟨1,1,4⟩,[r79,r172,r173,r174,r175,r176,r177,r178,448]),(⟨1,1,5⟩,[0,r364,r433,r434,r435,r436,r437,768]),(⟨1,2,0⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨1,2,1⟩,[0,0,0,r364,r421,r422,r423,r424,r425,r426,-768]),(⟨1,2,4⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨1,3,0⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨1,3,1⟩,[0,r191,r173,r427,r428,r429,r430,r431,r432,-3456]),(⟨1,3,4⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨1,4,0⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨1,4,1⟩,[r79,r172,r173,r174,r175,r176,r177,r178,448]),(⟨1,4,2⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨1,4,3⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨1,4,5⟩,[r79,r212,r375,r376,64]),(⟨1,5,0⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨1,5,1⟩,[0,r364,r433,r434,r435,r436,r437,768]),(⟨1,5,4⟩,[r79,r212,r375,r376,64]),(⟨1,6,0⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨1,7,0⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨1,9,0⟩,[r79,r212,r375,r376,64]),(⟨2,0,0⟩,[r245,r258,r1,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,0,1⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨2,0,2⟩,[0,0,r79,r377,r378,r379,r380,r381,r382,r383,r221]),(⟨2,0,3⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨2,0,4⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨2,0,5⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨2,1,0⟩,[r329,r288,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨2,1,1⟩,[0,0,0,r364,r421,r422,r423,r424,r425,r426,-768]),(⟨2,1,4⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨2,2,0⟩,[0,0,r79,r377,r378,r379,r380,r381,r382,r383,r221]),(⟨2,3,0⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨2,4,0⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨2,4,1⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨2,5,0⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨3,0,0⟩,[r79,r124,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨3,0,1⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,0,2⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨3,0,3⟩,[r162,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨3,0,4⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨3,0,5⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨3,1,0⟩,[r79,r279,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,1,1⟩,[0,r191,r173,r427,r428,r429,r430,r431,r432,-3456]),(⟨3,1,4⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨3,2,0⟩,[r384,r139,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨3,3,0⟩,[r162,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨3,4,0⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨3,4,1⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨3,5,0⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨4,0,0⟩,[r79,r279,r280,r281,r282,r283,r284,r285,95872,r286,r287]),(⟨4,0,1⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨4,0,2⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨4,0,3⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨4,0,4⟩,[r145,r146,r147,r148,r149,r150,-576]),(⟨4,0,6⟩,[r79,r212,r375,r376,64]),(⟨4,1,0⟩,[0,r349,r350,r351,r352,r353,r354,r355,r356,-3264]),(⟨4,1,1⟩,[r79,r172,r173,r174,r175,r176,r177,r178,448]),(⟨4,1,2⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨4,1,3⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨4,1,5⟩,[r79,r212,r375,r376,64]),(⟨4,2,0⟩,[r104,r393,r394,r395,r396,r397,r398,r399,224]),(⟨4,2,1⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨4,3,0⟩,[0,0,r79,r408,r409,r410,r411,-64]),(⟨4,3,1⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨4,4,0⟩,[r145,r146,r147,r148,r149,r150,-576]),(⟨4,5,1⟩,[r79,r212,r375,r376,64]),(⟨4,6,0⟩,[r79,r212,r375,r376,64]),(⟨5,0,0⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨5,0,1⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨5,0,2⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨5,0,3⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨5,1,0⟩,[0,r14,r357,r358,r359,r360,r361,r362,r363]),(⟨5,1,1⟩,[0,r364,r433,r434,r435,r436,r437,768]),(⟨5,1,4⟩,[r79,r212,r375,r376,64]),(⟨5,2,0⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨5,3,0⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨5,4,1⟩,[r79,r212,r375,r376,64]),(⟨6,0,0⟩,[r288,r298,r299,r300,r301,r302,r303,r304,r305]),(⟨6,0,1⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨6,0,4⟩,[r79,r212,r375,r376,64]),(⟨6,1,0⟩,[0,r364,r365,r366,r367,r368,r369,704]),(⟨6,4,0⟩,[r79,r212,r375,r376,64]),(⟨7,0,0⟩,[r104,r299,r306,r307,r308,r309,r310,r311]),(⟨7,0,1⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨7,1,0⟩,[r162,r370,r371,r372,r373,r374,-288]),(⟨8,0,0⟩,[r104,r312,r313,r314,r315,r316,r317]),(⟨9,0,1⟩,[r79,r212,r375,r376,64]),(⟨9,1,0⟩,[r79,r212,r375,r376,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r438) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 5 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r439) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨5,0,1⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨5,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,1,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨5,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨6,0,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨6,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨6,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨8,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨9,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨9,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨0,5,1⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,5,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,5,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,6,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,6,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨0,6,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,8,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,9,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[64,-1088,2624,72064,-835840,4659840,-16511360,40592768,-71779008,92034112,-84104896,51820288,-18546304,2301824]),(⟨1,0,1⟩,[64,-1344,8896,384,-347648,2450176,-9432960,23932288,-42461632,53452864,-46751040,26329856,-7507584]),(⟨1,0,2⟩,[-64,832,1216,-71168,506752,-1888512,4455552,-7090816,7680704,-5443648,2166976,-219520]),(⟨1,0,3⟩,[-64,960,-192,-65664,499328,-1900544,4523648,-7196032,7683008,-5240256,1859648]),(⟨1,1,0⟩,[64,-1344,8896,384,-347648,2450176,-9432960,23932288,-42461632,53452864,-46751040,26329856,-7507584]),(⟨1,1,1⟩,[0,-512,9728,-70144,253952,-476160,242688,1043456,-3039232,4138496,-3250688,1279488]),(⟨1,1,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,2,0⟩,[-64,832,1216,-71168,506752,-1888512,4455552,-7090816,7680704,-5443648,2166976,-219520]),(⟨1,3,0⟩,[-64,960,-192,-65664,499328,-1900544,4523648,-7196032,7683008,-5240256,1859648]),(⟨1,4,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,5,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨1,5,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,9,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[64,-1344,9024,-1280,-349824,2596224,-10515968,28035840,-51834432,66826176,-58179904,31252992,-8165248]),(⟨2,0,1⟩,[0,-512,9856,-72320,262272,-428416,-322688,3441536,-8694400,12059008,-9547776,3424512]),(⟨2,0,2⟩,[0,0,-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨2,0,3⟩,[0,0,-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨2,0,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,1,0⟩,[0,-512,9856,-72320,262272,-428416,-322688,3441536,-8694400,12059008,-9547776,3424512]),(⟨2,1,1⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨2,1,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨2,3,0⟩,[0,0,-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨2,4,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,4,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨3,0,0⟩,[-256,3648,192,-294784,2512128,-10988288,30089600,-54510464,65021952,-47806784,17695168,-1033984]),(⟨3,0,1⟩,[-192,3584,-18176,-47744,970240,-5191296,15620480,-29750144,36326080,-26544512,9287040]),(⟨3,0,2⟩,[192,-2048,-8576,195456,-1061376,3018624,-5118592,5090944,-2593472,282240]),(⟨3,0,3⟩,[192,-2432,-5248,187008,-1062144,3065728,-5225344,5105536,-2390976]),(⟨3,0,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,1,0⟩,[-192,3584,-18176,-47744,970240,-5191296,15620480,-29750144,36326080,-26544512,9287040]),(⟨3,1,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨3,1,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[192,-2048,-8576,195456,-1061376,3018624,-5118592,5090944,-2593472,282240]),(⟨3,3,0⟩,[192,-2432,-5248,187008,-1062144,3065728,-5225344,5105536,-2390976]),(⟨3,4,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,4,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,0,0⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨4,0,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨4,0,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨4,4,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨5,0,1⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,1,0⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨6,0,1⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨7,0,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,1,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨8,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨9,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨9,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨0,0,6⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,0,7⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,0,8⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,1,0⟩,[64,-1088,2624,72064,-835840,4659840,-16511360,40592768,-71779008,92034112,-84104896,51820288,-18546304,2301824]),(⟨0,1,1⟩,[64,-1344,8896,384,-347648,2450176,-9432960,23932288,-42461632,53452864,-46751040,26329856,-7507584]),(⟨0,1,2⟩,[-64,832,1216,-71168,506752,-1888512,4455552,-7090816,7680704,-5443648,2166976,-219520]),(⟨0,1,3⟩,[-64,960,-192,-65664,499328,-1900544,4523648,-7196032,7683008,-5240256,1859648]),(⟨0,1,5⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,1,6⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨0,1,9⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[64,-1344,9024,-1280,-349824,2596224,-10515968,28035840,-51834432,66826176,-58179904,31252992,-8165248]),(⟨0,2,1⟩,[0,-512,9856,-72320,262272,-428416,-322688,3441536,-8694400,12059008,-9547776,3424512]),(⟨0,2,2⟩,[0,0,-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨0,2,3⟩,[0,0,-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨0,2,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,2,5⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,3,0⟩,[-256,3648,192,-294784,2512128,-10988288,30089600,-54510464,65021952,-47806784,17695168,-1033984]),(⟨0,3,1⟩,[-192,3584,-18176,-47744,970240,-5191296,15620480,-29750144,36326080,-26544512,9287040]),(⟨0,3,2⟩,[192,-2048,-8576,195456,-1061376,3018624,-5118592,5090944,-2593472,282240]),(⟨0,3,3⟩,[192,-2432,-5248,187008,-1062144,3065728,-5225344,5105536,-2390976]),(⟨0,3,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,3,5⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,4,0⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨0,4,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨0,4,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,4,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,5,0⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨0,5,1⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨0,5,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,5,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,6,0⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨0,6,1⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨0,6,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,7,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,8,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,9,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[64,-1088,2624,72064,-835840,4659840,-16511360,40592768,-71779008,92034112,-84104896,51820288,-18546304,2301824]),(⟨1,0,1⟩,[64,-1344,8896,384,-347648,2450176,-9432960,23932288,-42461632,53452864,-46751040,26329856,-7507584]),(⟨1,0,2⟩,[-64,832,1216,-71168,506752,-1888512,4455552,-7090816,7680704,-5443648,2166976,-219520]),(⟨1,0,3⟩,[-64,960,-192,-65664,499328,-1900544,4523648,-7196032,7683008,-5240256,1859648]),(⟨1,0,5⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨1,0,6⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,0,9⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[128,-2688,17792,768,-695296,4900352,-18865920,47864576,-84923264,106905728,-93502080,52659712,-15015168]),(⟨1,1,1⟩,[0,-1024,19456,-140288,507904,-952320,485376,2086912,-6078464,8276992,-6501376,2558976]),(⟨1,1,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,1,5⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,2,0⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨1,2,1⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,2,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,0⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨1,3,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨1,3,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,4,0⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨1,4,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,4,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨1,5,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨1,7,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,9,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[64,-1344,9024,-1280,-349824,2596224,-10515968,28035840,-51834432,66826176,-58179904,31252992,-8165248]),(⟨2,0,1⟩,[0,-512,9856,-72320,262272,-428416,-322688,3441536,-8694400,12059008,-9547776,3424512]),(⟨2,0,2⟩,[0,0,-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨2,0,3⟩,[0,0,-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨2,0,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,0,5⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨2,1,0⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨2,1,1⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨2,1,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,-256,2304,15616,-237312,996096,-2071808,2336512,-1166592,125440]),(⟨2,3,0⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨2,4,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,4,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨3,0,0⟩,[-256,3648,192,-294784,2512128,-10988288,30089600,-54510464,65021952,-47806784,17695168,-1033984]),(⟨3,0,1⟩,[-192,3584,-18176,-47744,970240,-5191296,15620480,-29750144,36326080,-26544512,9287040]),(⟨3,0,2⟩,[192,-2048,-8576,195456,-1061376,3018624,-5118592,5090944,-2593472,282240]),(⟨3,0,3⟩,[192,-2432,-5248,187008,-1062144,3065728,-5225344,5105536,-2390976]),(⟨3,0,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,0,5⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨3,1,0⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨3,1,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨3,1,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨3,3,0⟩,[384,-4864,-10496,374016,-2124288,6131456,-10450688,10211072,-4781952]),(⟨3,4,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,4,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,0,0⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨4,0,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨4,0,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨4,1,0⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨4,1,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,2,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,3,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,3,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,4,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨5,0,1⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,1,0⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨6,0,1⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨7,0,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,1,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨8,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨9,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨9,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-192,3264,-7296,-225024,2515584,-13304064,43115904,-91513728,127250112,-108019392,41835264,8186496,-11809920,1972992]),(⟨0,0,1⟩,[64,-1280,6656,45952,-848128,5763456,-23740544,65864960,-126686016,167256832,-143781760,69265792,-9307648,-4133248]),(⟨0,0,2⟩,[64,-1152,6528,-5504,-129792,1098624,-5463296,18182784,-40782528,61082880,-58683520,32720640,-8353408]),(⟨0,0,3⟩,[-256,3840,-2688,-294784,2716800,-12474368,35208320,-64567808,76226688,-53192960,16505344,560000]),(⟨0,0,4⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨0,0,5⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨0,0,6⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨0,0,7⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,0,8⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,1,0⟩,[64,-1280,6656,45952,-848128,5763456,-23740544,65864960,-126686016,167256832,-143781760,69265792,-9307648,-4133248]),(⟨0,1,1⟩,[128,-2688,19328,-28416,-489472,4218368,-17928960,48482048,-89297792,113707136,-97561728,52145152,-13918464]),(⟨0,1,2⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨0,1,3⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨0,1,4⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨0,1,5⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨0,1,6⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨0,1,7⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,1,9⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[64,-1152,6528,-5504,-129792,1098624,-5463296,18182784,-40782528,61082880,-58683520,32720640,-8353408]),(⟨0,2,1⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨0,2,2⟩,[0,0,-256,2304,15616,-237312,996096,-2071808,2336512,-1166592,125440]),(⟨0,2,3⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨0,2,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,2,5⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,3,0⟩,[-256,3840,-2688,-294784,2716800,-12474368,35208320,-64567808,76226688,-53192960,16505344,560000]),(⟨0,3,1⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨0,3,2⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨0,3,3⟩,[384,-4864,-10496,374016,-2124288,6131456,-10450688,10211072,-4781952]),(⟨0,3,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,3,5⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,4,0⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨0,4,1⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨0,4,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,4,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,4,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨0,4,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,5,0⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨0,5,1⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨0,5,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,5,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,6,0⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨0,6,1⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨0,6,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,7,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,8,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,9,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[64,-1280,6656,45952,-848128,5763456,-23740544,65864960,-126686016,167256832,-143781760,69265792,-9307648,-4133248]),(⟨1,0,1⟩,[128,-2688,19328,-28416,-489472,4218368,-17928960,48482048,-89297792,113707136,-97561728,52145152,-13918464]),(⟨1,0,2⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨1,0,3⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨1,0,4⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨1,0,5⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨1,0,6⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨1,0,7⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,0,9⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[128,-2688,19328,-28416,-489472,4218368,-17928960,48482048,-89297792,113707136,-97561728,52145152,-13918464]),(⟨1,1,1⟩,[0,-1536,29184,-210432,761856,-1428480,728064,3130368,-9117696,12415488,-9752064,3838464]),(⟨1,1,2⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,1,3⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨1,1,4⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,1,5⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,2,0⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨1,2,1⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,2,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,0⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨1,3,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨1,3,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,4,0⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨1,4,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,4,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,4,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨1,5,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨1,7,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,9,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[64,-1152,6528,-5504,-129792,1098624,-5463296,18182784,-40782528,61082880,-58683520,32720640,-8353408]),(⟨2,0,1⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨2,0,2⟩,[0,0,-256,2304,15616,-237312,996096,-2071808,2336512,-1166592,125440]),(⟨2,0,3⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨2,0,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,0,5⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨2,1,0⟩,[-64,320,11072,-143488,769024,-2316928,4132864,-3649280,-1013696,6615360,-7380800,3204992]),(⟨2,1,1⟩,[0,0,0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨2,1,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,-256,2304,15616,-237312,996096,-2071808,2336512,-1166592,125440]),(⟨2,3,0⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨2,4,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,4,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨3,0,0⟩,[-256,3840,-2688,-294784,2716800,-12474368,35208320,-64567808,76226688,-53192960,16505344,560000]),(⟨3,0,1⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨3,0,2⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨3,0,3⟩,[384,-4864,-10496,374016,-2124288,6131456,-10450688,10211072,-4781952]),(⟨3,0,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,0,5⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨3,1,0⟩,[-256,4544,-18368,-113408,1469568,-7091840,20144128,-36946176,44009088,-31784768,11146688]),(⟨3,1,1⟩,[0,1536,-25600,149504,-390144,353280,668672,-2430976,3056640,-1645056]),(⟨3,1,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[192,-2048,-8704,196864,-1055360,2902272,-4614144,4033280,-1399872,-249088]),(⟨3,3,0⟩,[384,-4864,-10496,374016,-2124288,6131456,-10450688,10211072,-4781952]),(⟨3,4,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,4,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,0,0⟩,[-256,4544,-18496,-111232,1462016,-7137792,20522368,-38024064,45635072,-33087936,11574976]),(⟨4,0,1⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨4,0,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,0,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,0,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨4,1,0⟩,[0,1920,-32128,186752,-466560,322944,991616,-2787712,3074688,-1553664]),(⟨4,1,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨4,1,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,2,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,3,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,3,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,4,0⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[320,-3584,-12416,339200,-1996032,6065152,-10824064,11196672,-5665344,408576]),(⟨5,0,1⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,1,0⟩,[0,128,-6528,85376,-529280,1817472,-3592320,3952256,-2038400]),(⟨5,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨5,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨5,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-4480,1024,241024,-1573504,4952448,-8993792,9257600,-4536000]),(⟨6,0,1⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,14080,-55040,50688,101888,-314624,335104]),(⟨6,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨7,0,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,1,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨8,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨9,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨9,1,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r440) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 5).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r438*r439 : ℚ)=r440 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 5 r438 r439 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=5 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 5).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C063

#print axioms Coulomb8.Columns.C063.sound
