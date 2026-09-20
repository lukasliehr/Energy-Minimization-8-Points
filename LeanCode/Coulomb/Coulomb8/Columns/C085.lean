import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C085

def r0 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -49283072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 352419840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -990511104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -3795189760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 48382214144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -1871904768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 602958495744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -145861935104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1032830451712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -504614387712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -164167680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 91750989824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -2659713024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 6848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -97779712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 101875712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -2392064000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2229403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 59045576704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -40020934656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 732181889024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -1154747957248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 1029474615296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -362424074240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -98530623488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 9465954304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -2654208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -6848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -1292107776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 1415380992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -1997537280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 49602822144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 23662133248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -188344336384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 231710064640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -9446981632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -675348480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -12353536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 148242432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -770736128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 410779648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 15877472256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -88275681280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 228061282304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -306136088576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 173796065280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 9444392960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -3230236672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 52625408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -50593792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 870645760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 2895904768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -26803699712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 78238187520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -104249589760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 47816900608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 1465843712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 786432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -52690944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 138936320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 870187008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -6905921536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 17359962112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -15907422208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 88801280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 40632320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1703936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 85196800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 421986304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -3599499264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 8932163584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -7414743040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -58884096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 16941056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -151060480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 831520768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -2395209728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -1549991936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 6559498240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -201848225792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1616838656, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -596962148352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 331974639616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 1137639424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2258239488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 2555904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 40697856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -424706048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 70057984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 2574647296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -3702784000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 74445455360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -111834726400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 107426807808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -1952776192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 1336705024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -23756800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 155582464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -511705088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -142278656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 1341587456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -41770156032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 87120740352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -83277283328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 14879129600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 2868903936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 98304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -14385152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 34471936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 177471488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1332412416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 3528130560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -3864657920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -780730368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 3726016512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -31686656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 7471104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -27918336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 14614528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 170983424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -355860480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -89260032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 6258688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -154468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -1845231616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 19628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 2621440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -6946816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -209715200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 2231107584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -9364832256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 17777295360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -9458155520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -14537064448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 3078094848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -206700544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1474560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -9535488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 35389440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -39518208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -3901816832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 2201878528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -22749839360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 2565963776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -223969280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -5373952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 79953920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -366804992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 514064384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 107085824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -373030912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 2129920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 14942208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -7077888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -130154496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 1866596352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -7623933952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 14654636032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -10363535360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -226951168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 12320768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -21495808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -161087488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 731381760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -428081152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -2125987840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 23527424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -2949120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 35487744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -222560256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 773849088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1148583936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -2881290240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 3192127488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -57964658688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 43777720320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 123363360768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -46182432768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 279773184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -5865472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 28114944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -156565504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 803602432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1923284992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 431095808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 4276977664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -6228606976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1935114240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -21954560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 4390912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -43548672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 10747904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -117243904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -1819148288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 7274168320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -10047193088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -8535441408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 6610550784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -52068352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 1507328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -11337728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 18087936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -746979328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 957743104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 477364224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -403898368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 118947840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -6881280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -70320128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 2949120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 301596672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -855244800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -3178496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 24641536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -42991616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -322174976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 1462763520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -856162304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -4251975680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 47054848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -24641536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 176209920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -495255552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -1897594880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 24191107072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -935952384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 301479247872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -72930967552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 516415225856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -252307193856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -82083840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 45875494912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -1329856512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 3424256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -48889856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 50937856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -1196032000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -1114701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 29522788352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -20010467328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 366090944512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -577373978624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 514737307648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -181212037120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -49265311744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 4732977152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -1327104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -3424256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -646053888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 707690496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -998768640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 24801411072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 11831066624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -94172168192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 115855032320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -4723490816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -337674240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -6176768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 74121216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -385368064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 205389824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 7938736128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -44137840640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 114030641152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -153068044288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 86898032640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 4722196480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -1615118336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 26312704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -25296896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 435322880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 1447952384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -13401849856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 39119093760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -52124794880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 23908450304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 732921856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -26345472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 69468160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 435093504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -3452960768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 8679981056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -7953711104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 44400640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 20316160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -851968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 42598400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 210993152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -1799749632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 4466081792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -3707371520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -29442048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 8470528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -75530240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 415760384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -1197604864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -774995968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 3279749120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -100924112896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 808419328, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -298481074176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 165987319808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 568819712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -1129119744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 1277952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 20348928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -212353024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 35028992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1287323648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -1851392000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 37222727680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -55917363200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 53713403904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -976388096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 668352512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 966656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -11878400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 77791232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -255852544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -71139328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 670793728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -20885078016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 43560370176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -41638641664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 7439564800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 1434451968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 49152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -7192576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 17235968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 88735744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -666206208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 1764065280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1932328960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -390365184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1863008256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -15843328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -409600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 3735552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -13959168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 7307264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 85491712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -177930240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -44630016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 3129344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -77234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 40501248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -118292480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -922615808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 9814016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -3473408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -104857600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1115553792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -4682416128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 8888647680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -4729077760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -7268532224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 1539047424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -103350272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 737280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -4767744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -196608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 17694720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -19759104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1950908416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 1100939264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -11374919680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 1282981888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -111984640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 39976960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -183402496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 257032192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 53542912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -186515456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 1064960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 196608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -10616832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -3309568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 82182144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -95748096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -1179648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -65077248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 933298176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -3811966976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 7327318016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -5181767680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -113475584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 6160384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -10747904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -80543744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 365690880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -214040576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -1062993920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 11763712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -1474560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 17743872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -111280128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 386924544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -574291968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -1440645120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 1596063744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -28982329344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 21888860160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 61681680384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -23091216384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 139886592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -2932736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 14057472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -78282752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 401801216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -961642496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 215547904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 2138488832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -3114303488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 967557120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -10977280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 2195456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -21774336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 5373952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -58621952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -909574144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 3637084160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -5023596544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -4267720704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 3305275392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -26034176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 753664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -5668864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 9043968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -373489664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 478871552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 238682112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -201949184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 59473920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -3440640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -35160064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 1474560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 150798336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -427622400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -1589248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[0,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28],[0,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41],[0,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[0,r29,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[0,r15,r64,r65,r66,r67,r68,r69,r70,r71,r72],[0,r0,r73,r74,r75,r76,r77,r78,r79,r80],[],[],[],[],[],[],[r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[r81,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106],[r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118],[r107,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128],[r81,r129,r130,r131,r132,r133,r134,r135,r136,-32768],[r81,r137,r138,r139,r140,r141,r142,r143,r144],[],[],[],[],[],[0,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155],[r107,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165],[0,r81,r139,r166,r167,r168,r169,r170,r171,r172],[r81,r137,r173,r174,r175,r176,r177,r178,32768],[],[],[],[],[],[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188],[r179,r189,r190,r191,r192,r193,r194,r195,r196],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r29,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208],[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220],[r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231],[0,r232,r233,r234,r235,r236,r237,r238,r239,262144],[r179,r189,r240,r241,r242,r243,r244,r245,65536],[],[],[],[],[],[r107,r246,r247,r248,r110,r249,r250,r251,r252,r253,r254],[r81,r95,r255,r256,r257,r258,r259,r260,r261,98304],[r81,r137,r173,r174,r175,r176,r177,r178,32768],[],[],[],[],[],[r262,r263,r264,r265,r266,r267,r268,r269,r270],[],[],[],[],[],[],[],[],[],[],[],[],[r179,r189,r240,r241,r242,r243,r244,r245,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285]),(⟨0,0,1⟩,[0,r0,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,0,2⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311]),(⟨0,0,3⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,0,4⟩,[0,r299,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨0,0,5⟩,[0,r0,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨0,0,6⟩,[0,r271,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨0,1,0⟩,[0,r0,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,1,1⟩,[r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,1,2⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,1,3⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨0,1,4⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨0,1,5⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨0,1,6⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412]),(⟨0,2,0⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311]),(⟨0,2,1⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,2,2⟩,[0,r107,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422]),(⟨0,2,3⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,2,4⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨0,2,5⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨0,3,0⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,3,1⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨0,3,2⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,3,3⟩,[r81,r129,r130,r446,r447,r448,r449,r450,r451,r452]),(⟨0,3,4⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨0,4,0⟩,[0,r299,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨0,4,1⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨0,4,2⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨0,4,3⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨0,5,0⟩,[0,r0,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨0,5,1⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨0,5,2⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨0,6,0⟩,[0,r271,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨0,6,1⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412]),(⟨1,0,0⟩,[0,r0,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨1,0,1⟩,[r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,0,2⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨1,0,3⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨1,0,4⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨1,0,5⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨1,0,6⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412]),(⟨1,1,0⟩,[r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,1,1⟩,[r299,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨1,1,2⟩,[r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,1,3⟩,[r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨1,1,4⟩,[0,r262,r263,r495,r496,r497,r498,r499,r500,131072]),(⟨1,1,5⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨1,2,0⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨1,2,1⟩,[r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,2,2⟩,[r209,r501,r502,r503,r379,r504,r505,r506,r507,r508,r509]),(⟨1,2,3⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨1,2,4⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨1,3,0⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨1,3,1⟩,[r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨1,3,2⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨1,3,3⟩,[r179,r189,r190,r191,r192,r193,r194,r195,r196]),(⟨1,4,0⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨1,4,1⟩,[0,r262,r263,r495,r496,r497,r498,r499,r500,131072]),(⟨1,4,2⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨1,5,0⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨1,5,1⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨1,6,0⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412]),(⟨2,0,0⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311]),(⟨2,0,1⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,0,2⟩,[0,r107,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422]),(⟨2,0,3⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨2,0,4⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨2,0,5⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨2,1,0⟩,[r351,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,1,1⟩,[r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨2,1,2⟩,[r209,r501,r502,r503,r379,r504,r505,r506,r507,r508,r509]),(⟨2,1,3⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨2,1,4⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨2,2,0⟩,[0,r107,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422]),(⟨2,2,1⟩,[r209,r501,r502,r503,r379,r504,r505,r506,r507,r508,r509]),(⟨2,2,3⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨2,3,0⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨2,3,1⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨2,3,2⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨2,4,0⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨2,4,1⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨2,5,0⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨3,0,0⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨3,0,1⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨3,0,2⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨3,0,3⟩,[r81,r129,r130,r446,r447,r448,r449,r450,r451,r452]),(⟨3,0,4⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨3,1,0⟩,[r209,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨3,1,1⟩,[r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨3,1,2⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨3,1,3⟩,[r179,r189,r190,r191,r192,r193,r194,r195,r196]),(⟨3,2,0⟩,[r209,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨3,2,1⟩,[r351,r365,r510,r511,r512,r513,r514,r515,r516,49152]),(⟨3,2,2⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨3,3,0⟩,[r81,r129,r130,r446,r447,r448,r449,r450,r451,r452]),(⟨3,3,1⟩,[r179,r189,r190,r191,r192,r193,r194,r195,r196]),(⟨3,4,0⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨4,0,0⟩,[0,r299,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨4,0,1⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨4,0,2⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨4,0,3⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨4,1,0⟩,[r209,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397]),(⟨4,1,1⟩,[0,r262,r263,r495,r496,r497,r498,r499,r500,131072]),(⟨4,1,2⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨4,2,0⟩,[0,r351,r145,r433,r434,r435,r436,r437,r438,r439]),(⟨4,2,1⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨4,3,0⟩,[r81,r137,r453,r454,r455,r456,r457,r458,r459]),(⟨5,0,0⟩,[0,r0,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨5,0,1⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨5,0,2⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨5,1,0⟩,[r351,r398,r399,r400,r401,r402,r403,r404,r405,-16384]),(⟨5,1,1⟩,[r81,r137,r173,r174,r175,r176,r177,r178,32768]),(⟨5,2,0⟩,[r351,r406,r440,r441,r442,r443,r444,r445,16384]),(⟨6,0,0⟩,[0,r271,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨6,0,1⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412]),(⟨6,1,0⟩,[r351,r406,r407,r145,r408,r409,r410,r411,r412])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r517) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r517) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[0,49152,-1622016,22085632,-159465472,643596288,-1309507584,305463296,4492853248,-9177612288,6146899968,453246976,-1214660608]),(⟨2,0,2⟩,[0,49152,-1507328,18677760,-119930880,416055296,-650117120,-337838080,3072196608,-4478943232,1677656064,873463808]),(⟨2,0,3⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,0,4⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,1,0⟩,[0,49152,-1622016,22085632,-159465472,643596288,-1309507584,305463296,4492853248,-9177612288,6146899968,453246976,-1214660608]),(⟨2,1,1⟩,[0,98304,-3014656,37355520,-239861760,832110592,-1300234240,-675676160,6144393216,-8957886464,3355312128,1746927616]),(⟨2,1,2⟩,[-16384,376832,-2834432,4521984,38895616,-186744832,239435776,119341056,-706822144,1457111040,-1433026560]),(⟨2,1,3⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,49152,-1507328,18677760,-119930880,416055296,-650117120,-337838080,3072196608,-4478943232,1677656064,873463808]),(⟨2,2,1⟩,[-16384,376832,-2834432,4521984,38895616,-186744832,239435776,119341056,-706822144,1457111040,-1433026560]),(⟨2,2,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,3,0⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨2,3,1⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,3,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,4,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,49152,-1622016,20512768,-113852416,92569600,2301788160,-13676773376,36840374272,-51054067712,29299458048,3412328448,-6114131968]),(⟨3,0,1⟩,[0,98304,-3014656,35782656,-197918720,375455744,1361051648,-9719119872,24096014336,-27709046784,9309126656,5270142976]),(⟨3,0,2⟩,[-16384,376832,-2834432,6094848,98304,181829632,-1449820160,3877961728,-4010885120,1321320448,-662323200]),(⟨3,0,3⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨3,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[0,98304,-3014656,35782656,-197918720,375455744,1361051648,-9719119872,24096014336,-27709046784,9309126656,5270142976]),(⟨3,1,1⟩,[-49152,1277952,-12206080,48627712,-25395200,-466026496,1792507904,-2551316480,-1870118912,11687395328,-11423268864]),(⟨3,1,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,2,0⟩,[-16384,376832,-2834432,6094848,98304,181829632,-1449820160,3877961728,-4010885120,1321320448,-662323200]),(⟨3,3,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨3,3,1⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,49152,-1507328,17104896,-77987840,-40599552,2011168768,-9381281792,21023817728,-23230103552,7631470592,4396679168]),(⟨4,0,1⟩,[-16384,376832,-2310144,-7012352,137461760,-609320960,1182105600,-552796160,-3049340928,8804483072,-7984005120]),(⟨4,0,3⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨4,1,0⟩,[-16384,376832,-2310144,-7012352,137461760,-609320960,1182105600,-552796160,-3049340928,8804483072,-7984005120]),(⟨4,3,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨5,0,0⟩,[0,-49152,1409024,-13959168,41418752,196313088,-1733099520,4504354816,-4168351744,-125353984,961773568]),(⟨5,0,1⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,0,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨5,1,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨6,0,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,1,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[0,49152,-1622016,22085632,-159465472,643596288,-1309507584,305463296,4492853248,-9177612288,6146899968,453246976,-1214660608]),(⟨1,0,3⟩,[0,49152,-1507328,18677760,-119930880,416055296,-650117120,-337838080,3072196608,-4478943232,1677656064,873463808]),(⟨1,0,4⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨1,0,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,1,0⟩,[0,0,196608,-6488064,88342528,-637861888,2574385152,-5238030336,1221853184,17971412992,-36710449152,24587599872,1812987904,-4858642432]),(⟨1,1,1⟩,[0,0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨1,1,2⟩,[0,49152,-1703936,24313856,-182059008,736919552,-1339162624,-513212416,6055133184,-7936098304,1719402496,1637744640]),(⟨1,1,3⟩,[-16384,425984,-4440064,25821184,-105545728,315293696,-397377536,-913178624,3188637696,-1529708544,-1787871232]),(⟨1,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,2,0⟩,[0,49152,-1425408,16056320,-84754432,163872768,354713600,-2295005184,3141500928,3111174144,-11768872960,7163871232,2279194624]),(⟨1,2,1⟩,[0,-16384,196608,1703936,-39714816,250773504,-708050944,795279360,566624256,-3849076736,7464353792,-5622923264]),(⟨1,2,2⟩,[0,-98304,2818048,-31064064,160432128,-344522752,-87687168,1491468288,-1728577536,20873216,382140416]),(⟨1,2,3⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨1,3,0⟩,[0,49152,-1703936,24313856,-182059008,736919552,-1339162624,-513212416,6055133184,-7936098304,1719402496,1637744640]),(⟨1,3,1⟩,[-16384,425984,-4243456,20054016,-41320448,-14483456,283279360,-626393088,157466624,1446674432,-1624096768]),(⟨1,3,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,3,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,-49152,1212416,-9764864,15990784,157515776,-724500480,458948608,2166882304,-2965946368,27295744]),(⟨1,4,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[0,49152,-1523712,18055168,-90128384,-12976128,2458877952,-13272481792,35051372544,-49720082432,32449216512,-1663533056,-5613174784,1000308736]),(⟨2,0,1⟩,[0,98304,-3031040,36962304,-218710016,534839296,751796224,-8701214720,24510431232,-32240992256,16034742272,2839674880,-1933983744]),(⟨2,0,2⟩,[0,49152,-1703936,25427968,-212467712,1056473088,-2962358272,3539927040,1960443904,-8428142592,4170973184,1589575680]),(⟨2,0,3⟩,[-16384,327680,-1490944,-7864320,66945024,52035584,-1480425472,4294967296,-4492181504,1893269504,-1399308288]),(⟨2,0,4⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨2,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,1,0⟩,[0,98304,-2834432,30932992,-143998976,55115776,2416017408,-11301683200,23159078912,-19952205824,-1881030656,9550299136,1559871488]),(⟨2,1,1⟩,[-16384,425984,-4440064,25395200,-96370688,246218752,-214663168,-742195200,1661124608,-287014912,944455680,-3411968000]),(⟨2,1,2⟩,[-32768,802816,-7077888,24576000,-2424832,-201228288,522715136,-507052032,-549355520,2903785472,-3057123328]),(⟨2,1,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-16384,0,8454144,-132251648,891191296,-3020292096,4673044480,-545128448,-7798276096,9957670912,-4906811392]),(⟨2,2,1⟩,[-32768,802816,-7077888,24576000,-2424832,-201228288,522715136,-507052032,-549355520,2903785472,-3057123328]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-16384,327680,-1490944,-7864320,66945024,52035584,-1480425472,4294967296,-4492181504,1893269504,-1399308288]),(⟨2,3,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,98304,-3031040,35389440,-173096960,-16187392,4363091968,-22683451392,56857952256,-74117447680,39187300352,5798756352,-6833455104]),(⟨3,0,1⟩,[-16384,491520,-6144000,40796160,-134643712,-45154304,2504556544,-10918756352,22118318080,-19668041728,1111572480,6607634432]),(⟨3,0,2⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨3,0,3⟩,[16384,-409600,3735552,-12386304,-32538624,466649088,-1905983488,3663659008,-2590883840,-397164544]),(⟨3,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-16384,491520,-6340608,46432256,-196771840,275709952,1815511040,-11094130688,25101254656,-23125196800,1153318912,7371915264]),(⟨3,1,1⟩,[-49152,1277952,-12206080,48627712,-25395200,-466026496,1792507904,-2551316480,-1870118912,11687395328,-11423268864]),(⟨3,1,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,2,0⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨3,3,0⟩,[16384,-409600,3735552,-12386304,-32538624,466649088,-1905983488,3663659008,-2590883840,-397164544]),(⟨3,3,1⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[0,0,-196608,5177344,-50593792,183762944,349044736,-5165678592,16839868416,-22700359680,8447131648,4239327232]),(⟨4,0,1⟩,[-16384,376832,-2310144,-7012352,137461760,-609320960,1182105600,-552796160,-3049340928,8804483072,-7984005120]),(⟨4,0,2⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨4,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,1,0⟩,[-16384,376832,-2506752,-1245184,73236480,-279543808,501448704,-839581696,-18169856,5828100096,-8147779584]),(⟨4,1,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,0,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨5,0,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,0,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,1,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨6,0,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,1,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928])]

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[0,49152,-1622016,22085632,-159465472,643596288,-1309507584,305463296,4492853248,-9177612288,6146899968,453246976,-1214660608]),(⟨0,2,2⟩,[0,49152,-1507328,18677760,-119930880,416055296,-650117120,-337838080,3072196608,-4478943232,1677656064,873463808]),(⟨0,2,3⟩,[0,-49152,1409024,-15532032,80216064,-172261376,-43843584,745734144,-864288768,10436608,191070208]),(⟨0,2,4⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,3,0⟩,[0,49152,-1622016,20512768,-113852416,92569600,2301788160,-13676773376,36840374272,-51054067712,29299458048,3412328448,-6114131968]),(⟨0,3,1⟩,[0,98304,-3014656,35782656,-197918720,375455744,1361051648,-9719119872,24096014336,-27709046784,9309126656,5270142976]),(⟨0,3,2⟩,[-16384,376832,-2834432,6094848,98304,181829632,-1449820160,3877961728,-4010885120,1321320448,-662323200]),(⟨0,3,3⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨0,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,4,0⟩,[0,49152,-1507328,17104896,-77987840,-40599552,2011168768,-9381281792,21023817728,-23230103552,7631470592,4396679168]),(⟨0,4,1⟩,[-16384,376832,-2310144,-7012352,137461760,-609320960,1182105600,-552796160,-3049340928,8804483072,-7984005120]),(⟨0,4,3⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨0,5,0⟩,[0,-49152,1409024,-13959168,41418752,196313088,-1733099520,4504354816,-4168351744,-125353984,961773568]),(⟨0,5,1⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨0,6,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[0,-49152,1818624,-27885568,225099776,-948666368,1011220480,10662707200,-65365377024,188656861184,-317568466944,300045271040,-113712447488,-31631409152,26436730880]),(⟨1,0,1⟩,[0,-49152,1900544,-30507008,261881856,-1248559104,2624585728,4207149056,-43972427776,129636188160,-196464672768,143540060160,-19048300544,-23869325312]),(⟨1,0,2⟩,[0,98304,-3031040,36536320,-207372288,415956992,1370456064,-10277683200,25514573824,-27861483520,5349228544,10360684544,-1879392256]),(⟨1,0,3⟩,[0,98304,-3342336,45449216,-308543488,988479488,-240254976,-8749383680,28334358528,-37360533504,17180721152,2528870400]),(⟨1,0,4⟩,[0,-49152,1212416,-9764864,15990784,157515776,-724500480,458948608,2166882304,-2965946368,27295744]),(⟨1,0,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,1,0⟩,[0,-49152,1900544,-30507008,261881856,-1248559104,2624585728,4207149056,-43972427776,129636188160,-196464672768,143540060160,-19048300544,-23869325312]),(⟨1,1,1⟩,[16384,-491520,6111232,-43122688,203685888,-671154176,1184006144,1123680256,-11012128768,19585073152,2644787200,-47168880640,42335698944]),(⟨1,1,2⟩,[0,-16384,0,7340032,-101842944,571637760,-1397096448,619905024,3549560832,-7306231808,7506100224,-4858642432]),(⟨1,1,3⟩,[-32768,884736,-9125888,44302336,-90046464,-71368704,865239040,-2005925888,474251264,5683249152,-6837583872]),(⟨1,1,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,2,0⟩,[0,98304,-3031040,36536320,-207372288,415956992,1370456064,-10277683200,25514573824,-27861483520,5349228544,10360684544,-1879392256]),(⟨1,2,1⟩,[0,32768,-1507328,26017792,-221773824,987693056,-2047213568,282066944,6621757440,-11785175040,9183756288,-3985178624]),(⟨1,2,2⟩,[-16384,327680,-1425408,-11010048,119111680,-359006208,195592192,865075200,-1571110912,1467547648,-1241956352]),(⟨1,2,3⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨1,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[0,147456,-4849664,62554112,-386531328,947879936,1770913792,-18130665472,49358176256,-60590637056,24812191744,6925549568]),(⟨1,3,1⟩,[-65536,1736704,-17088512,72876032,-74121216,-522911744,2374467584,-3930849280,-1553334272,15923970048,-16636755968]),(⟨1,3,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨1,3,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨1,4,0⟩,[-16384,376832,-2506752,-1245184,73236480,-279543808,501448704,-839581696,-18169856,5828100096,-8147779584]),(⟨1,4,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,0⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨2,0,0⟩,[0,0,180224,-5963776,83410944,-623673344,2509078528,-3827302400,-10142908416,61944692736,-127305007104,117288927232,-26474463232,-18010374144]),(⟨2,0,1⟩,[16384,-393216,2883584,-131072,-89735168,343408640,271581184,-4977065984,14849654784,-24944705536,36595302400,-51039830016,36907859968]),(⟨2,0,2⟩,[0,-16384,0,8454144,-132251648,891191296,-3020292096,4673044480,-545128448,-7798276096,9957670912,-4906811392]),(⟨2,0,3⟩,[-32768,786432,-6176768,10616832,82444288,-334626816,-217808896,3202220032,-7206567936,9106227200,-6449020928]),(⟨2,0,4⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,1,0⟩,[16384,-393216,2883584,-131072,-89735168,343408640,271581184,-4977065984,14849654784,-24944705536,36595302400,-51039830016,36907859968]),(⟨2,1,1⟩,[-16384,360448,-2736128,8421376,-16154624,80936960,-272596992,390922240,-844447744,342851584,6731153408,-9908355072]),(⟨2,1,2⟩,[-32768,802816,-7077888,24576000,-2424832,-201228288,522715136,-507052032,-549355520,2903785472,-3057123328]),(⟨2,1,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-16384,0,8454144,-132251648,891191296,-3020292096,4673044480,-545128448,-7798276096,9957670912,-4906811392]),(⟨2,2,1⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨2,3,1⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,147456,-4636672,55869440,-295714816,235896832,5378834432,-30666129408,79231025152,-105090105344,56305401856,8995569664,-10992041984]),(⟨3,0,1⟩,[-16384,491520,-6340608,46432256,-196771840,275709952,1815511040,-11094130688,25101254656,-23125196800,1153318912,7371915264]),(⟨3,0,2⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨3,0,3⟩,[16384,-409600,3735552,-12386304,-32538624,466649088,-1905983488,3663659008,-2590883840,-397164544]),(⟨3,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-16384,491520,-6340608,46432256,-196771840,275709952,1815511040,-11094130688,25101254656,-23125196800,1153318912,7371915264]),(⟨3,1,1⟩,[-49152,1277952,-12206080,48627712,-25395200,-466026496,1792507904,-2551316480,-1870118912,11687395328,-11423268864]),(⟨3,1,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,2,0⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨3,2,1⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨3,2,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,3,0⟩,[16384,-458752,5177344,-26869760,10059776,677642240,-3705733120,8129740800,-6298255360,-603258880]),(⟨3,3,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,4,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨4,0,1⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,0,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,1,0⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,1,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,0,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨5,0,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,0,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,1,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨6,0,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,1,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-49152,1818624,-27885568,225099776,-948666368,1011220480,10662707200,-65365377024,188656861184,-317568466944,300045271040,-113712447488,-31631409152,26436730880]),(⟨0,1,1⟩,[0,-49152,1900544,-30507008,261881856,-1248559104,2624585728,4207149056,-43972427776,129636188160,-196464672768,143540060160,-19048300544,-23869325312]),(⟨0,1,2⟩,[0,98304,-3031040,36536320,-207372288,415956992,1370456064,-10277683200,25514573824,-27861483520,5349228544,10360684544,-1879392256]),(⟨0,1,3⟩,[0,98304,-3342336,45449216,-308543488,988479488,-240254976,-8749383680,28334358528,-37360533504,17180721152,2528870400]),(⟨0,1,4⟩,[0,-49152,1212416,-9764864,15990784,157515776,-724500480,458948608,2166882304,-2965946368,27295744]),(⟨0,1,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨0,2,0⟩,[0,0,180224,-5963776,83410944,-623673344,2509078528,-3827302400,-10142908416,61944692736,-127305007104,117288927232,-26474463232,-18010374144]),(⟨0,2,1⟩,[16384,-393216,2883584,-131072,-89735168,343408640,271581184,-4977065984,14849654784,-24944705536,36595302400,-51039830016,36907859968]),(⟨0,2,2⟩,[0,-16384,0,8454144,-132251648,891191296,-3020292096,4673044480,-545128448,-7798276096,9957670912,-4906811392]),(⟨0,2,3⟩,[-32768,786432,-6176768,10616832,82444288,-334626816,-217808896,3202220032,-7206567936,9106227200,-6449020928]),(⟨0,2,4⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨0,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,3,0⟩,[0,147456,-4636672,55869440,-295714816,235896832,5378834432,-30666129408,79231025152,-105090105344,56305401856,8995569664,-10992041984]),(⟨0,3,1⟩,[-16384,491520,-6340608,46432256,-196771840,275709952,1815511040,-11094130688,25101254656,-23125196800,1153318912,7371915264]),(⟨0,3,2⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨0,3,3⟩,[16384,-409600,3735552,-12386304,-32538624,466649088,-1905983488,3663659008,-2590883840,-397164544]),(⟨0,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,4,0⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨0,4,1⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨0,4,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨0,4,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,5,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨0,5,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨0,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨0,6,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[0,-49152,1818624,-27885568,225099776,-948666368,1011220480,10662707200,-65365377024,188656861184,-317568466944,300045271040,-113712447488,-31631409152,26436730880]),(⟨1,0,1⟩,[0,-49152,1900544,-30507008,261881856,-1248559104,2624585728,4207149056,-43972427776,129636188160,-196464672768,143540060160,-19048300544,-23869325312]),(⟨1,0,2⟩,[0,98304,-3031040,36536320,-207372288,415956992,1370456064,-10277683200,25514573824,-27861483520,5349228544,10360684544,-1879392256]),(⟨1,0,3⟩,[0,98304,-3342336,45449216,-308543488,988479488,-240254976,-8749383680,28334358528,-37360533504,17180721152,2528870400]),(⟨1,0,4⟩,[0,-49152,1212416,-9764864,15990784,157515776,-724500480,458948608,2166882304,-2965946368,27295744]),(⟨1,0,5⟩,[0,-49152,1441792,-16056320,82444288,-170164224,-71696384,757792768,-744095744,-40943616]),(⟨1,1,0⟩,[0,-98304,3604480,-54525952,435421184,-1859256320,2674786304,13652328448,-89166708736,241300963328,-356218896384,262492520448,-39909588992,-42880008192]),(⟨1,1,1⟩,[32768,-983040,12025856,-80216064,332660736,-862584832,703791104,4847828992,-20672905216,26881359872,23205347328,-101048385536,81177542656]),(⟨1,1,2⟩,[0,-32768,196608,9043968,-141557760,822411264,-2105147392,1415184384,4116185088,-11155308544,14970454016,-10481565696]),(⟨1,1,3⟩,[-65536,1769472,-18055168,82837504,-115867648,-472514560,2411134976,-3725066240,-2082668544,14342881280,-13511393280]),(⟨1,1,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,2,0⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨1,2,1⟩,[-16384,360448,-2932736,14057472,-78282752,401801216,-961642496,215547904,2138488832,-3114303488,6772899840,-9144074240]),(⟨1,2,2⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨1,2,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨1,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-16384,540672,-7979008,67567616,-323256320,527269888,2914418688,-19330301952,47380480000,-52549632000,16614637568,8263041024]),(⟨1,3,1⟩,[-65536,1736704,-17088512,72876032,-74121216,-522911744,2374467584,-3930849280,-1553334272,15923970048,-16636755968]),(⟨1,3,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨1,3,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨1,4,0⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨1,4,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨1,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨2,0,0⟩,[0,0,180224,-5963776,83410944,-623673344,2509078528,-3827302400,-10142908416,61944692736,-127305007104,117288927232,-26474463232,-18010374144]),(⟨2,0,1⟩,[16384,-393216,2883584,-131072,-89735168,343408640,271581184,-4977065984,14849654784,-24944705536,36595302400,-51039830016,36907859968]),(⟨2,0,2⟩,[0,-16384,0,8454144,-132251648,891191296,-3020292096,4673044480,-545128448,-7798276096,9957670912,-4906811392]),(⟨2,0,3⟩,[-32768,786432,-6176768,10616832,82444288,-334626816,-217808896,3202220032,-7206567936,9106227200,-6449020928]),(⟨2,0,4⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,1,0⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨2,1,1⟩,[-16384,360448,-2932736,14057472,-78282752,401801216,-961642496,215547904,2138488832,-3114303488,6772899840,-9144074240]),(⟨2,1,2⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨2,1,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-65536,1310720,-3473408,-104857600,1115553792,-4682416128,8888647680,-4729077760,-7268532224,10773331968,-5064163328]),(⟨2,2,1⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨2,3,1⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,147456,-4636672,55869440,-295714816,235896832,5378834432,-30666129408,79231025152,-105090105344,56305401856,8995569664,-10992041984]),(⟨3,0,1⟩,[-16384,491520,-6340608,46432256,-196771840,275709952,1815511040,-11094130688,25101254656,-23125196800,1153318912,7371915264]),(⟨3,0,2⟩,[-16384,327680,-1425408,-9437184,80314368,9568256,-1493663744,4623695872,-4875173888,1331757056,-471252992]),(⟨3,0,3⟩,[16384,-409600,3735552,-12386304,-32538624,466649088,-1905983488,3663659008,-2590883840,-397164544]),(⟨3,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-16384,540672,-7979008,67567616,-323256320,527269888,2914418688,-19330301952,47380480000,-52549632000,16614637568,8263041024]),(⟨3,1,1⟩,[-65536,1736704,-17088512,72876032,-74121216,-522911744,2374467584,-3930849280,-1553334272,15923970048,-16636755968]),(⟨3,1,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨3,1,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨3,2,0⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨3,2,1⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨3,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[32768,-819200,7471104,-24772608,-65077248,933298176,-3811966976,7327318016,-5181767680,-794329088]),(⟨3,3,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,4,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨4,0,1⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,0,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,1,0⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,1,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,0,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨5,0,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,0,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,1,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨6,0,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,1,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-49152,1720320,-24641536,176209920,-495255552,-1897594880,24191107072,-111378333696,301479247872,-510516772864,516415225856,-252307193856,-4022108160,45875494912,-9308995584]),(⟨0,0,1⟩,[0,-98304,3424256,-48889856,356564992,-1196032000,-1114701824,29522788352,-140073271296,366090944512,-577373978624,514737307648,-181212037120,-49265311744,33130840064]),(⟨0,0,2⟩,[0,49152,-1327104,11698176,-3424256,-646053888,4953833472,-16979066880,24801411072,11831066624,-94172168192,115855032320,-33064435712,-16546037760]),(⟨0,0,3⟩,[0,196608,-6176768,74121216,-385368064,205389824,7938736128,-44137840640,114030641152,-153068044288,86898032640,4722196480,-11305828352]),(⟨0,0,4⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨0,0,5⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨0,0,6⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨0,1,0⟩,[0,-98304,3424256,-48889856,356564992,-1196032000,-1114701824,29522788352,-140073271296,366090944512,-577373978624,514737307648,-181212037120,-49265311744,33130840064]),(⟨0,1,1⟩,[16384,-557056,8470528,-75530240,415760384,-1197604864,-774995968,22958243840,-100924112896,233633185792,-298481074176,165987319808,27872165888,-55326867456]),(⟨0,1,2⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨0,1,3⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨0,1,4⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨0,1,5⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨0,1,6⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨0,2,0⟩,[0,49152,-1327104,11698176,-3424256,-646053888,4953833472,-16979066880,24801411072,11831066624,-94172168192,115855032320,-33064435712,-16546037760]),(⟨0,2,1⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨0,2,2⟩,[0,-65536,1310720,-3473408,-104857600,1115553792,-4682416128,8888647680,-4729077760,-7268532224,10773331968,-5064163328]),(⟨0,2,3⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨0,2,4⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨0,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,3,0⟩,[0,196608,-6176768,74121216,-385368064,205389824,7938736128,-44137840640,114030641152,-153068044288,86898032640,4722196480,-11305828352]),(⟨0,3,1⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨0,3,2⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨0,3,3⟩,[32768,-819200,7471104,-24772608,-65077248,933298176,-3811966976,7327318016,-5181767680,-794329088]),(⟨0,3,4⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,4,0⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨0,4,1⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨0,4,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨0,4,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,5,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨0,5,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨0,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,6,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨0,6,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[0,-98304,3424256,-48889856,356564992,-1196032000,-1114701824,29522788352,-140073271296,366090944512,-577373978624,514737307648,-181212037120,-49265311744,33130840064]),(⟨1,0,1⟩,[16384,-557056,8470528,-75530240,415760384,-1197604864,-774995968,22958243840,-100924112896,233633185792,-298481074176,165987319808,27872165888,-55326867456]),(⟨1,0,2⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨1,0,3⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨1,0,4⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨1,0,5⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨1,0,6⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,1,0⟩,[16384,-557056,8470528,-75530240,415760384,-1197604864,-774995968,22958243840,-100924112896,233633185792,-298481074176,165987319808,27872165888,-55326867456]),(⟨1,1,1⟩,[49152,-1474560,17743872,-111280128,386924544,-574291968,-1440645120,11172446208,-28982329344,21888860160,61681680384,-161638514688,116525531136]),(⟨1,1,2⟩,[-16384,360448,-2932736,14057472,-78282752,401801216,-961642496,215547904,2138488832,-3114303488,6772899840,-9144074240]),(⟨1,1,3⟩,[-81920,2195456,-21774336,91357184,-58621952,-909574144,3637084160,-5023596544,-4267720704,23136927744,-21686468608]),(⟨1,1,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,2,0⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨1,2,1⟩,[-16384,360448,-2932736,14057472,-78282752,401801216,-961642496,215547904,2138488832,-3114303488,6772899840,-9144074240]),(⟨1,2,2⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨1,2,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨1,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨1,3,1⟩,[-81920,2195456,-21774336,91357184,-58621952,-909574144,3637084160,-5023596544,-4267720704,23136927744,-21686468608]),(⟨1,3,2⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨1,3,3⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨1,4,0⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨1,4,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨1,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨2,0,0⟩,[0,49152,-1327104,11698176,-3424256,-646053888,4953833472,-16979066880,24801411072,11831066624,-94172168192,115855032320,-33064435712,-16546037760]),(⟨2,0,1⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨2,0,2⟩,[0,-65536,1310720,-3473408,-104857600,1115553792,-4682416128,8888647680,-4729077760,-7268532224,10773331968,-5064163328]),(⟨2,0,3⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨2,0,4⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,1,0⟩,[16384,-344064,1277952,20348928,-212353024,595492864,1287323648,-12959744000,37222727680,-55917363200,53713403904,-47843016704,32749273088]),(⟨2,1,1⟩,[-16384,360448,-2932736,14057472,-78282752,401801216,-961642496,215547904,2138488832,-3114303488,6772899840,-9144074240]),(⟨2,1,2⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨2,1,3⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[0,-65536,1310720,-3473408,-104857600,1115553792,-4682416128,8888647680,-4729077760,-7268532224,10773331968,-5064163328]),(⟨2,2,1⟩,[-32768,753664,-5668864,9043968,77791232,-373489664,478871552,238682112,-1413644288,2914222080,-2866053120]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨2,3,1⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨2,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[0,196608,-6176768,74121216,-385368064,205389824,7938736128,-44137840640,114030641152,-153068044288,86898032640,4722196480,-11305828352]),(⟨3,0,1⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨3,0,2⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨3,0,3⟩,[32768,-819200,7471104,-24772608,-65077248,933298176,-3811966976,7327318016,-5181767680,-794329088]),(⟨3,0,4⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,1,0⟩,[-32768,966656,-11878400,77791232,-255852544,-71139328,4695556096,-20885078016,43560370176,-41638641664,7439564800,10041163776]),(⟨3,1,1⟩,[-81920,2195456,-21774336,91357184,-58621952,-909574144,3637084160,-5023596544,-4267720704,23136927744,-21686468608]),(⟨3,1,2⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨3,1,3⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,2,0⟩,[-32768,737280,-4767744,-3342336,123863040,-138313728,-1950908416,7706574848,-11374919680,8980873216,-5487247360]),(⟨3,2,1⟩,[16384,-344064,2162688,-589824,-35160064,72253440,150798336,-427622400,-189120512,696041472]),(⟨3,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[32768,-819200,7471104,-24772608,-65077248,933298176,-3811966976,7327318016,-5181767680,-794329088]),(⟨3,3,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,4,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,49152,-1835008,26312704,-177078272,435322880,1447952384,-13401849856,39119093760,-52124794880,23908450304,5130452992]),(⟨4,0,1⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,0,2⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,1,0⟩,[-32768,835584,-7192576,17235968,88735744,-666206208,1764065280,-1932328960,-2732556288,13041057792,-13197492224]),(⟨4,1,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[0,16384,-131072,-2686976,39976960,-183402496,257032192,374800384,-1305608192,887111680]),(⟨4,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,0,0⟩,[0,-98304,2752512,-26345472,69468160,435093504,-3452960768,8679981056,-7953711104,310804480,995491840]),(⟨5,0,1⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,0,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,1,0⟩,[16384,-409600,3735552,-13959168,7307264,85491712,-177930240,-44630016,372391936,-232013824]),(⟨5,1,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨6,0,0⟩,[0,-49152,1441792,-14483456,42598400,210993152,-1799749632,4466081792,-3707371520,-206094336]),(⟨6,0,1⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,1,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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
    (Poly.add (Poly.scale (K.ofRat r518) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 4).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r517*r517 : ℚ)=r518 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 4 r517 r517 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=4 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 4).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C085

#print axioms Coulomb8.Columns.C085.sound
