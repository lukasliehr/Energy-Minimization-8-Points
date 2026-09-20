import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C143

def r0 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 270336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -4022272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 35880960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -214097920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 896647168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -2675294208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 5636882432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -8191467520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 8427577344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1285103616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 15459516416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -22793560064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 17755701248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -5326766080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 525336576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -2678784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 32391168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -230154240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 1064108032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -474365952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 6977978368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -9632006144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 1316061184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -10901479424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 21559001088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -30331068416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 19962331136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -3316645888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 6381568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -43040768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 24076288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -51281920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 196165632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 916455424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -2126577664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 1225965568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -306225152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 5127192576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -1445208064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 768311296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 5513216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -55492608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 43982848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1024262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 2033270784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -2193588224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 1259454464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -2321383424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 870735872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -5419286528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 306339840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -1900544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 212992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 53821440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -45268992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 791773184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -876150784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 320462848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -880369664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 2879160320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -2407841792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -2768896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 21823488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -82313216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 145031168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -9273344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -46727168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -239206400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 15155200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 6946816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -35127296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 79298560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -57147392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -3014656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -116916224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 278790144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 18989056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -23478272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 836501504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -380010496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 5273026560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -6243745792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 5202427904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -9406644224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 21891923968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -25727877120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 11517755392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 2383872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -3276800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 16310272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -309985280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 413515776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -8454144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 3686400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -836796416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 227008512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 3278569472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -541630464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 1245184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -18710528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 18087936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -459177984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 900464640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -118816768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 60293120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1490501632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 3318546432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -2270789632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -2654208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 2916352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -74874880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 118325248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -3244032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -54624256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -504332288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 45252608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -5373952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 30310400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -89817088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 123502592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -14024704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -92864512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -102449152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 262029312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -320995328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 77824000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 13893632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -70254592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 158597120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -114294784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -6029312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -233832448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 557580288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -6602752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 53018624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -279691264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 981794816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -2191294464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 2731540480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -1399111680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 1773633536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -9478651904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 58916864, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -36519936, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 18300928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -94240768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 286294016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -513835008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 473989120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -20971520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 714752000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -2879668224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 24494080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -65536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 5177344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 103841792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -197394432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 165937152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 11534336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 131678208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -756088832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 43188224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 2654208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -2916352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 10846208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -134053888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 72450048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1998848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 38043648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -23232512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -5767168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 43778048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -122683392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 8126464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 27787264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 819200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -8159232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 41451520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -109150208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 94470144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 250773504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -771129344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 692846592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1048576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -3801088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 26804224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -82837504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 73728000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 28442624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -551616512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 3407872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -753664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 5931008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -16875520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 72187904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -9404416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -229376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 3932160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -17301504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 14155776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -786432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1441792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 10944512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 2031616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 6946816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 1441792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -10944512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2031616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -6946816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 135168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -2011136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 17940480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -107048960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 448323584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -1337647104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 2818441216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -4095733760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 4213788672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -642551808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 7729758208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -11396780032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 8877850624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -2663383040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 262668288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1339392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 16195584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -115077120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 532054016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -237182976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 3488989184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -4816003072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 658030592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -5450739712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 10779500544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -15165534208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 9981165568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -1658322944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 3190784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -21520384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 12038144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -25640960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 98082816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 458227712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -1063288832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 612982784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -153112576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 2563596288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -722604032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 384155648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 2756608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -27746304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 21991424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -512131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 1016635392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -1096794112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 629727232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -1160691712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 435367936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -2709643264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 153169920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 106496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 26910720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -22634496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 395886592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -438075392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 160231424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -440184832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 1439580160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -1203920896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -1384448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 10911744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -41156608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 72515584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -4636672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -23363584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -119603200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 7577600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 3473408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -17563648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 39649280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -28573696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1507328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -58458112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 139395072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -540672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 9494528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -11739136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 418250752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -190005248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 2636513280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -3121872896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 2601213952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -4703322112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 10945961984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -12863938560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 5758877696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 1191936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -1638400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 8155136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -154992640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 206757888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -4227072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1843200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -418398208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 113504256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 1639284736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -270815232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 622592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -9355264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 9043968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -229588992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 450232320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -59408384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 30146560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -745250816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1659273216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -1135394816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -1327104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 1458176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -37437440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 59162624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -1622016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -27312128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -252166144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 22626304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -2686976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 15155200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -44908544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 61751296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -7012352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -46432256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -51224576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 131014656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -160497664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 38912000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -3301376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 26509312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -139845632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 490897408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -1095647232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 1365770240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -699555840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 886816768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -4739325952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 29458432, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -18259968, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -958464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 9150464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -47120384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 143147008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -256917504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 236994560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -10485760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 357376000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -1439834112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 12247040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 2588672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -15335424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 51920896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -98697216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 82968576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 5767168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 65839104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -378044416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 21594112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1327104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -1458176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 5423104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -67026944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 36225024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -999424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 19021824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -11616256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -2883584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 21889024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -61341696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 4063232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 13893632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 409600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -4079616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 20725760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -54575104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 47235072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 125386752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -385564672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 346423296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -524288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 13402112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -41418752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 36864000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 14221312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -275808256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 1703936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -376832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 2965504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -8437760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 36093952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -4702208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -114688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 1966080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -8650752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 7077888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 29753344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -393216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 5472256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 3473408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -5472256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 15335424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -3473408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[0,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29],[r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43],[0,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55],[r0,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66],[0,r67,r68,r69,r70,r71,r72,r73,r74,196608,r75],[0,0,r76,r77,r78,r79,r80,r81,r82,r83],[],[],[],[],[],[],[0,r30,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95],[0,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107],[0,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118],[0,0,r67,r119,r120,r121,r122,r123,r124,r125,r126],[],[],[],[],[],[],[],[r108,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137],[0,r67,r68,r69,r70,r71,r72,r73,r74,196608,r75],[],[],[],[],[],[],[],[0,0,r138,r139,r140,r141,r142,r143,r144,r145],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r108,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157],[0,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168],[r30,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178],[0,r179,r180,r181,r182,r183,r184,r185,r186,r187],[],[],[],[],[],[],[0,0,0,0,r188,r189,r190,r191,r192,r193,-262144],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r194,r195,r196,r197,r198,r199,r200,r201,r202,r203],[0,r204,r205,r206,r207,r208,r209,r210,r211],[r212,r213,r214,r215,r216,r217,r218,r219],[0,r220,r221,r222,r223,r224,r225],[],[],[],[0,r226,r227,r228,r171,r229,r230,-65536],[],[],[],[],[],[],[],[],[r231,r232,r233,r234,r235,r236,65536],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252]),(⟨0,0,1⟩,[0,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨0,0,2⟩,[r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨0,0,3⟩,[0,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,0,4⟩,[r237,r293,r216,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,0,5⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨0,0,6⟩,[0,0,r220,r311,r312,r313,r314,r315,r316,r317]),(⟨0,1,0⟩,[0,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨0,1,1⟩,[0,r267,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329]),(⟨0,1,2⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,1,3⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,1,4⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,2,0⟩,[r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨0,2,1⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,2,2⟩,[r0,r56,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,2,3⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨0,3,0⟩,[0,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,3,1⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,3,2⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨0,3,3⟩,[0,0,r76,r77,r78,r79,r80,r81,r82,r83]),(⟨0,4,0⟩,[r237,r293,r216,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,4,1⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,5,0⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨0,6,0⟩,[0,0,r220,r311,r312,r313,r314,r315,r316,r317]),(⟨1,0,0⟩,[0,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨1,0,1⟩,[0,r267,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329]),(⟨1,0,2⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,0,3⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,0,4⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,1,0⟩,[0,r267,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329]),(⟨1,1,1⟩,[r0,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨1,1,2⟩,[0,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,1,3⟩,[r267,r44,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨1,1,4⟩,[0,r231,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨1,2,0⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,2,1⟩,[0,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,2,2⟩,[0,0,0,0,r67,r410,r411,r412,r413,r414,-131072]),(⟨1,3,0⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,3,1⟩,[r267,r44,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨1,4,0⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,4,1⟩,[0,r231,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨2,0,0⟩,[r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨2,0,1⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,0,2⟩,[r0,r56,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨2,0,3⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨2,1,0⟩,[0,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,1,1⟩,[0,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨2,1,2⟩,[0,0,0,0,r67,r410,r411,r412,r413,r414,-131072]),(⟨2,2,0⟩,[r0,r56,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨2,2,1⟩,[0,0,0,0,r67,r410,r411,r412,r413,r414,-131072]),(⟨2,2,2⟩,[r108,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨2,2,3⟩,[0,r16,r57,r424,r425,r426,r427,r428,r429]),(⟨2,2,4⟩,[r30,r430,r431,r432,r433,r434,r435,r436]),(⟨2,2,5⟩,[0,r179,r437,r438,r439,r440,r441]),(⟨2,3,0⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨2,3,2⟩,[0,r16,r57,r424,r425,r426,r427,r428,r429]),(⟨2,3,3⟩,[0,r212,r442,r443,r394,r444,r445,-32768]),(⟨2,4,2⟩,[r30,r430,r431,r432,r433,r434,r435,r436]),(⟨2,5,2⟩,[0,r179,r437,r438,r439,r440,r441]),(⟨3,0,0⟩,[0,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨3,0,1⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨3,0,2⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨3,0,3⟩,[0,0,r76,r77,r78,r79,r80,r81,r82,r83]),(⟨3,1,0⟩,[0,r0,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨3,1,1⟩,[r267,r44,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨3,2,0⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨3,2,2⟩,[0,r16,r57,r424,r425,r426,r427,r428,r429]),(⟨3,2,3⟩,[0,r212,r442,r443,r394,r444,r445,-32768]),(⟨3,3,0⟩,[0,0,r76,r77,r78,r79,r80,r81,r82,r83]),(⟨3,3,2⟩,[0,r212,r442,r443,r394,r444,r445,-32768]),(⟨3,3,3⟩,[r194,r446,r447,r448,r449,r450,32768]),(⟨4,0,0⟩,[r237,r293,r216,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨4,0,1⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨4,1,0⟩,[0,0,r226,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨4,1,1⟩,[0,r231,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨4,2,2⟩,[r30,r430,r431,r432,r433,r434,r435,r436]),(⟨5,0,0⟩,[0,r226,r303,r304,r305,r306,r307,r308,r309,98304,r310]),(⟨5,2,2⟩,[0,r179,r437,r438,r439,r440,r441]),(⟨6,0,0⟩,[0,0,r220,r311,r312,r313,r314,r315,r316,r317])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r451) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r452) sourceRight))).isZero := by decide +kernel

noncomputable def partial14 : Poly := []

theorem partial_sound14 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 14)
      sourceRight).eval u v t=partial14.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[4096,-126976,1667072,-12296192,56414208,-164749312,291676160,-267059200,121040896,-362508288,933457920,-664199168,-124997632,57458688]),(⟨2,0,1⟩,[0,-24576,618496,-6234112,32993280,-98484224,159440896,-113852416,57958400,-315285504,653766656,-329097216,-176017408]),(⟨2,0,2⟩,[-4096,118784,-1343488,7577600,-22454272,30941184,-4947968,-12271616,-56283136,67538944,37847040,3612672]),(⟨2,0,3⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨2,1,0⟩,[0,-24576,618496,-6234112,32993280,-98484224,159440896,-113852416,57958400,-315285504,653766656,-329097216,-176017408]),(⟨2,1,1⟩,[0,0,0,0,-65536,1507328,-11862016,33751040,1900544,-144375808,131661824,54591488]),(⟨2,2,0⟩,[-4096,118784,-1343488,7577600,-22454272,30941184,-4947968,-12271616,-56283136,67538944,37847040,3612672]),(⟨2,3,0⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨3,0,0⟩,[0,-57344,1372160,-13705216,75100160,-245055488,471359488,-480034816,266199040,-628350976,1621798912,-1358045184,20983808]),(⟨3,0,1⟩,[0,0,196608,-3375104,23789568,-86900736,165740544,-139001856,83427328,-404619264,842530816,-548896768]),(⟨3,0,2⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨3,0,3⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨3,1,0⟩,[0,0,196608,-3375104,23789568,-86900736,165740544,-139001856,83427328,-404619264,842530816,-548896768]),(⟨3,1,1⟩,[0,0,0,0,0,524288,-7864320,34603008,-28311552,-119013376,187170816]),(⟨3,2,0⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨3,3,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨4,0,0⟩,[-4096,118784,-1146880,4202496,1400832,-57466880,172654592,-185024512,25243648,-192704512,748716032,-599875584]),(⟨4,0,1⟩,[0,0,0,0,0,524288,-7864320,34603008,-28311552,-119013376,187170816]),(⟨4,1,0⟩,[0,0,0,0,0,524288,-7864320,34603008,-28311552,-119013376,187170816]),(⟨4,2,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨5,0,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨5,2,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨6,0,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial14)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 14))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound14 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544])]

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,24576,-671744,8183808,-58908672,277315584,-884228096,1900249088,-2663743488,2478841856,-2635038720,5202550784,-7579607040,5077139456,-853671936]),(⟨1,0,1⟩,[0,8192,-393216,6324224,-52592640,262356992,-827621376,1643511808,-1965260800,1587126272,-2479587328,5569675264,-6503530496,2894200832]),(⟨1,0,2⟩,[0,-24576,573440,-5234688,24092672,-56115200,39714816,95600640,-192299008,44343296,-142065664,865148928,-908615680]),(⟨1,0,3⟩,[0,-8192,425984,-5980160,39518208,-142688256,284491776,-276856832,127598592,-340631552,816742400,-586498048]),(⟨1,0,4⟩,[0,0,65536,-1327104,10207232,-37961728,67026944,-36225024,999424,-133152768,197476352]),(⟨1,1,0⟩,[0,8192,-393216,6324224,-52592640,262356992,-827621376,1643511808,-1965260800,1587126272,-2479587328,5569675264,-6503530496,2894200832]),(⟨1,1,1⟩,[-8192,245760,-3252224,25321472,-128172032,430620672,-927236096,1160904704,-760078336,991133696,-3339902976,5082030080,-2800041984]),(⟨1,1,2⟩,[0,40960,-958464,9150464,-47054848,141770752,-247939072,225132544,-136642560,505815040,-1335304192,1137647616]),(⟨1,1,3⟩,[8192,-229376,2588672,-15335424,51920896,-99221504,90832896,-28835840,94150656,-259031040,179929088]),(⟨1,1,4⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨1,2,0⟩,[0,-24576,573440,-5234688,24092672,-56115200,39714816,95600640,-192299008,44343296,-142065664,865148928,-908615680]),(⟨1,2,1⟩,[0,40960,-958464,9150464,-47054848,141770752,-247939072,225132544,-136642560,505815040,-1335304192,1137647616]),(⟨1,2,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨1,3,0⟩,[0,-8192,425984,-5980160,39518208,-142688256,284491776,-276856832,127598592,-340631552,816742400,-586498048]),(⟨1,3,1⟩,[8192,-229376,2588672,-15335424,51920896,-99221504,90832896,-28835840,94150656,-259031040,179929088]),(⟨1,4,0⟩,[0,0,65536,-1327104,10207232,-37961728,67026944,-36225024,999424,-133152768,197476352]),(⟨1,4,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨2,0,0⟩,[4096,-126976,1519616,-9125888,26767360,-7217152,-227057664,808845312,-1253871616,840519680,-788729856,3169828864,-5099712512,2672574464]),(⟨2,0,1⟩,[0,-24576,569344,-5046272,21319680,-37814272,-16572416,144621568,-47194112,-272146432,-347459584,1999126528,-1842032640]),(⟨2,0,2⟩,[-4096,118784,-1343488,7577600,-22454272,30810112,-2064384,-34160640,5058560,63475712,-198344704,268771328]),(⟨2,0,3⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨2,1,0⟩,[0,-24576,569344,-5046272,21319680,-37814272,-16572416,144621568,-47194112,-272146432,-347459584,1999126528,-1842032640]),(⟨2,1,1⟩,[0,49152,-1187840,11673600,-61128704,184860672,-318177280,260800512,-66011136,450527232,-1565712384,1439850496]),(⟨2,1,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,2,0⟩,[-4096,118784,-1343488,7577600,-22454272,30810112,-2064384,-34160640,5058560,63475712,-198344704,268771328]),(⟨2,2,1⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,3,0⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨3,0,0⟩,[0,-81920,1994752,-20127744,110866432,-362233856,694689792,-696516608,344727552,-774602752,2082762752,-1717886976,-32690176]),(⟨3,0,1⟩,[0,-8192,425984,-5898240,37797888,-128614400,227000320,-162807808,76038144,-497770496,968409088,-531349504]),(⟨3,0,2⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨3,0,3⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨3,1,0⟩,[0,-8192,425984,-5898240,37797888,-128614400,227000320,-162807808,76038144,-497770496,968409088,-531349504]),(⟨3,1,1⟩,[8192,-229376,2523136,-14008320,41713664,-60735488,15941632,41992192,64839680,-244891648,169623552]),(⟨3,2,0⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨3,2,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨3,2,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨3,3,2⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,3⟩,[-32768,720896,-5472256,15335424,-1015808,-59047936,66289664]),(⟨4,0,0⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨4,0,1⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,0⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨4,2,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨5,0,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨5,2,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨6,0,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,24576,-671744,8183808,-58908672,277315584,-884228096,1900249088,-2663743488,2478841856,-2635038720,5202550784,-7579607040,5077139456,-853671936]),(⟨0,1,1⟩,[0,8192,-393216,6324224,-52592640,262356992,-827621376,1643511808,-1965260800,1587126272,-2479587328,5569675264,-6503530496,2894200832]),(⟨0,1,2⟩,[0,-24576,573440,-5234688,24092672,-56115200,39714816,95600640,-192299008,44343296,-142065664,865148928,-908615680]),(⟨0,1,3⟩,[0,-8192,425984,-5980160,39518208,-142688256,284491776,-276856832,127598592,-340631552,816742400,-586498048]),(⟨0,1,4⟩,[0,0,65536,-1327104,10207232,-37961728,67026944,-36225024,999424,-133152768,197476352]),(⟨0,2,0⟩,[4096,-126976,1519616,-9125888,26767360,-7217152,-227057664,808845312,-1253871616,840519680,-788729856,3169828864,-5099712512,2672574464]),(⟨0,2,1⟩,[0,-24576,569344,-5046272,21319680,-37814272,-16572416,144621568,-47194112,-272146432,-347459584,1999126528,-1842032640]),(⟨0,2,2⟩,[-4096,118784,-1343488,7577600,-22454272,30810112,-2064384,-34160640,5058560,63475712,-198344704,268771328]),(⟨0,2,3⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨0,3,0⟩,[0,-81920,1994752,-20127744,110866432,-362233856,694689792,-696516608,344727552,-774602752,2082762752,-1717886976,-32690176]),(⟨0,3,1⟩,[0,-8192,425984,-5898240,37797888,-128614400,227000320,-162807808,76038144,-497770496,968409088,-531349504]),(⟨0,3,2⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨0,3,3⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨0,4,0⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨0,4,1⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨0,5,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨0,6,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨1,0,0⟩,[0,24576,-671744,8183808,-58908672,277315584,-884228096,1900249088,-2663743488,2478841856,-2635038720,5202550784,-7579607040,5077139456,-853671936]),(⟨1,0,1⟩,[0,8192,-393216,6324224,-52592640,262356992,-827621376,1643511808,-1965260800,1587126272,-2479587328,5569675264,-6503530496,2894200832]),(⟨1,0,2⟩,[0,-24576,573440,-5234688,24092672,-56115200,39714816,95600640,-192299008,44343296,-142065664,865148928,-908615680]),(⟨1,0,3⟩,[0,-8192,425984,-5980160,39518208,-142688256,284491776,-276856832,127598592,-340631552,816742400,-586498048]),(⟨1,0,4⟩,[0,0,65536,-1327104,10207232,-37961728,67026944,-36225024,999424,-133152768,197476352]),(⟨1,1,0⟩,[0,8192,-540672,9494528,-82239488,419889152,-1346355200,2719416320,-3340173312,2790154240,-4201775104,9403703296,-11478245376,5509316608]),(⟨1,1,1⟩,[-8192,245760,-3301376,26509312,-139845632,491290624,-1103249408,1419378688,-865230848,1034272768,-4341129216,7410253824,-4466057216]),(⟨1,1,2⟩,[0,40960,-958464,9150464,-47054848,141639680,-245055488,203243520,-75300864,501751808,-1571495936,1402806272]),(⟨1,1,3⟩,[8192,-229376,2588672,-15335424,51920896,-99221504,90832896,-28835840,94150656,-259031040,179929088]),(⟨1,1,4⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨1,2,0⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨1,2,1⟩,[0,40960,-958464,9150464,-47120384,143147008,-256917504,236994560,-73400320,357376000,-1439834112,1457397760]),(⟨1,2,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨1,3,0⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨1,3,1⟩,[8192,-229376,2588672,-15335424,51920896,-98697216,82968576,5767168,65839104,-378044416,367099904]),(⟨1,4,0⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨1,4,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨2,0,0⟩,[4096,-126976,1519616,-9125888,26767360,-7217152,-227057664,808845312,-1253871616,840519680,-788729856,3169828864,-5099712512,2672574464]),(⟨2,0,1⟩,[0,-24576,569344,-5046272,21319680,-37814272,-16572416,144621568,-47194112,-272146432,-347459584,1999126528,-1842032640]),(⟨2,0,2⟩,[-4096,118784,-1343488,7577600,-22454272,30810112,-2064384,-34160640,5058560,63475712,-198344704,268771328]),(⟨2,0,3⟩,[0,32768,-696320,5505024,-20611072,34930688,-11976704,-9961472,-77627392,106856448,40656896]),(⟨2,1,0⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨2,1,1⟩,[0,40960,-958464,9150464,-47120384,143147008,-256917504,236994560,-73400320,357376000,-1439834112,1457397760]),(⟨2,1,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,2,0⟩,[-8192,237568,-2686976,15155200,-44908544,61751296,-7012352,-46432256,-51224576,131014656,-160497664,272384000]),(⟨2,2,1⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,3,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨2,3,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨2,3,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨2,4,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨2,5,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨3,0,0⟩,[0,-81920,1994752,-20127744,110866432,-362233856,694689792,-696516608,344727552,-774602752,2082762752,-1717886976,-32690176]),(⟨3,0,1⟩,[0,-8192,425984,-5898240,37797888,-128614400,227000320,-162807808,76038144,-497770496,968409088,-531349504]),(⟨3,0,2⟩,[0,32768,-688128,5406720,-20545536,37584896,-20480000,-13402112,-41975808,92012544,12386304]),(⟨3,0,3⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨3,1,0⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨3,1,1⟩,[8192,-229376,2588672,-15335424,51920896,-98697216,82968576,5767168,65839104,-378044416,367099904]),(⟨3,2,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨3,2,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨3,2,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,0⟩,[0,0,-524288,6946816,-35127296,79298560,-57147392,-21102592,-116916224,278790144]),(⟨3,3,2⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,3⟩,[-32768,720896,-5472256,15335424,-1015808,-59047936,66289664]),(⟨4,0,0⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨4,0,1⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,0⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨4,2,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨5,0,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨5,2,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨6,0,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-4096,135168,-2011136,17940480,-107048960,448323584,-1337647104,2818441216,-4095733760,4213788672,-4497862656,7729758208,-11396780032,8877850624,-2663383040,262668288]),(⟨0,0,1⟩,[0,49152,-1339392,16195584,-115077120,532054016,-1660280832,3488989184,-4816003072,4606214144,-5450739712,10779500544,-15165534208,9981165568,-1658322944]),(⟨0,0,2⟩,[8192,-253952,3190784,-21520384,84267008,-179486720,98082816,458227712,-1063288832,612982784,-153112576,2563596288,-5058228224,2689089536]),(⟨0,0,3⟩,[0,-114688,2756608,-27746304,153939968,-512131072,1016635392,-1096794112,629727232,-1160691712,3047575552,-2709643264,153169920]),(⟨0,0,4⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨0,0,5⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨0,0,6⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨0,1,0⟩,[0,49152,-1339392,16195584,-115077120,532054016,-1660280832,3488989184,-4816003072,4606214144,-5450739712,10779500544,-15165534208,9981165568,-1658322944]),(⟨0,1,1⟩,[0,8192,-540672,9494528,-82173952,418250752,-1330036736,2636513280,-3121872896,2601213952,-4703322112,10945961984,-12863938560,5758877696]),(⟨0,1,2⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨0,1,3⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨0,1,4⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨0,2,0⟩,[8192,-253952,3190784,-21520384,84267008,-179486720,98082816,458227712,-1063288832,612982784,-153112576,2563596288,-5058228224,2689089536]),(⟨0,2,1⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨0,2,2⟩,[-8192,237568,-2686976,15155200,-44908544,61751296,-7012352,-46432256,-51224576,131014656,-160497664,272384000]),(⟨0,2,3⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨0,3,0⟩,[0,-114688,2756608,-27746304,153939968,-512131072,1016635392,-1096794112,629727232,-1160691712,3047575552,-2709643264,153169920]),(⟨0,3,1⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨0,3,2⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨0,3,3⟩,[0,0,-524288,6946816,-35127296,79298560,-57147392,-21102592,-116916224,278790144]),(⟨0,4,0⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨0,4,1⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨0,5,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨0,6,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072]),(⟨1,0,0⟩,[0,49152,-1339392,16195584,-115077120,532054016,-1660280832,3488989184,-4816003072,4606214144,-5450739712,10779500544,-15165534208,9981165568,-1658322944]),(⟨1,0,1⟩,[0,8192,-540672,9494528,-82173952,418250752,-1330036736,2636513280,-3121872896,2601213952,-4703322112,10945961984,-12863938560,5758877696]),(⟨1,0,2⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨1,0,3⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨1,0,4⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨1,1,0⟩,[0,8192,-540672,9494528,-82173952,418250752,-1330036736,2636513280,-3121872896,2601213952,-4703322112,10945961984,-12863938560,5758877696]),(⟨1,1,1⟩,[-8192,245760,-3301376,26509312,-139845632,490897408,-1095647232,1365770240,-699555840,886816768,-4739325952,8513486848,-5277130752]),(⟨1,1,2⟩,[0,40960,-958464,9150464,-47120384,143147008,-256917504,236994560,-73400320,357376000,-1439834112,1457397760]),(⟨1,1,3⟩,[8192,-229376,2588672,-15335424,51920896,-98697216,82968576,5767168,65839104,-378044416,367099904]),(⟨1,1,4⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨1,2,0⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨1,2,1⟩,[0,40960,-958464,9150464,-47120384,143147008,-256917504,236994560,-73400320,357376000,-1439834112,1457397760]),(⟨1,2,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨1,3,0⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨1,3,1⟩,[8192,-229376,2588672,-15335424,51920896,-98697216,82968576,5767168,65839104,-378044416,367099904]),(⟨1,4,0⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨1,4,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨2,0,0⟩,[8192,-253952,3190784,-21520384,84267008,-179486720,98082816,458227712,-1063288832,612982784,-153112576,2563596288,-5058228224,2689089536]),(⟨2,0,1⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨2,0,2⟩,[-8192,237568,-2686976,15155200,-44908544,61751296,-7012352,-46432256,-51224576,131014656,-160497664,272384000]),(⟨2,0,3⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨2,1,0⟩,[0,-49152,1191936,-11468800,57085952,-154992640,206757888,-71860224,31334400,-418398208,113504256,1639284736,-1895706624]),(⟨2,1,1⟩,[0,40960,-958464,9150464,-47120384,143147008,-256917504,236994560,-73400320,357376000,-1439834112,1457397760]),(⟨2,1,2⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,2,0⟩,[-8192,237568,-2686976,15155200,-44908544,61751296,-7012352,-46432256,-51224576,131014656,-160497664,272384000]),(⟨2,2,1⟩,[0,0,0,0,131072,-2883584,21889024,-61341696,4063232,236191744,-265158656]),(⟨2,2,2⟩,[-16384,409600,-4079616,20725760,-54575104,47235072,125386752,-385564672,346423296,-62390272]),(⟨2,2,3⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨2,2,4⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨2,2,5⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨2,3,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨2,3,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨2,3,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨2,4,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨2,5,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨3,0,0⟩,[0,-114688,2756608,-27746304,153939968,-512131072,1016635392,-1096794112,629727232,-1160691712,3047575552,-2709643264,153169920]),(⟨3,0,1⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨3,0,2⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨3,0,3⟩,[0,0,-524288,6946816,-35127296,79298560,-57147392,-21102592,-116916224,278790144]),(⟨3,1,0⟩,[0,-8192,622592,-9355264,63307776,-229588992,450232320,-415858688,211025920,-745250816,1659273216,-1135394816]),(⟨3,1,1⟩,[8192,-229376,2588672,-15335424,51920896,-98697216,82968576,5767168,65839104,-378044416,367099904]),(⟨3,2,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨3,2,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨3,2,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,0⟩,[0,0,-524288,6946816,-35127296,79298560,-57147392,-21102592,-116916224,278790144]),(⟨3,3,2⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨3,3,3⟩,[-32768,720896,-5472256,15335424,-1015808,-59047936,66289664]),(⟨4,0,0⟩,[-4096,118784,-950272,745472,26910720,-158441472,395886592,-438075392,160231424,-440184832,1439580160,-1203920896]),(⟨4,0,1⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,0⟩,[0,0,65536,-1327104,10207232,-37437440,59162624,-1622016,-27312128,-252166144,384647168]),(⟨4,1,1⟩,[0,-65536,1327104,-10207232,37961728,-67026944,36225024,-999424,133152768,-197476352]),(⟨4,2,2⟩,[16384,-376832,2965504,-8437760,-475136,36093952,-32915456,-13647872]),(⟨5,0,0⟩,[0,65536,-1384448,10911744,-41156608,72515584,-32456704,-23363584,-119603200,198868992,53043200]),(⟨5,2,2⟩,[0,-131072,1966080,-8650752,7077888,29753344,-46792704]),(⟨6,0,0⟩,[0,0,-262144,3473408,-17563648,39649280,-28573696,-10551296,-58458112,139395072])]


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
    (Poly.add (Poly.scale (K.ofRat r453) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 10 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r451*r452 : ℚ)=r453 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 10 13 r451 r452 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 10=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 10 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C143

#print axioms Coulomb8.Columns.C143.sound
