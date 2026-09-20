import Thomson8.Extensions.C000
import Thomson8.Extensions.C001
import Thomson8.Extensions.C002
import Thomson8.Extensions.C003
import Thomson8.Extensions.C010
import Thomson8.Extensions.C011
import Thomson8.Extensions.C012
import Thomson8.Extensions.C013
import Thomson8.Extensions.C020
import Thomson8.Extensions.C021
import Thomson8.Extensions.C022
import Thomson8.Extensions.C023
import Thomson8.Extensions.C030
import Thomson8.Extensions.C031
import Thomson8.Extensions.C032
import Thomson8.Extensions.C033
import Thomson8.Extensions.C100
import Thomson8.Extensions.C101
import Thomson8.Extensions.C102
import Thomson8.Extensions.C103
import Thomson8.Extensions.C110
import Thomson8.Extensions.C111
import Thomson8.Extensions.C112
import Thomson8.Extensions.C113
import Thomson8.Extensions.C120
import Thomson8.Extensions.C121
import Thomson8.Extensions.C122
import Thomson8.Extensions.C123
import Thomson8.Extensions.C130
import Thomson8.Extensions.C131
import Thomson8.Extensions.C132
import Thomson8.Extensions.C133
import Thomson8.Extensions.C200
import Thomson8.Extensions.C201
import Thomson8.Extensions.C202
import Thomson8.Extensions.C203
import Thomson8.Extensions.C210
import Thomson8.Extensions.C211
import Thomson8.Extensions.C212
import Thomson8.Extensions.C213
import Thomson8.Extensions.C220
import Thomson8.Extensions.C221
import Thomson8.Extensions.C222
import Thomson8.Extensions.C223
import Thomson8.Extensions.C230
import Thomson8.Extensions.C231
import Thomson8.Extensions.C232
import Thomson8.Extensions.C233
import Thomson8.Extensions.C300
import Thomson8.Extensions.C301
import Thomson8.Extensions.C302
import Thomson8.Extensions.C303
import Thomson8.Extensions.C310
import Thomson8.Extensions.C311
import Thomson8.Extensions.C312
import Thomson8.Extensions.C313
import Thomson8.Extensions.C320
import Thomson8.Extensions.C321
import Thomson8.Extensions.C322
import Thomson8.Extensions.C323
import Thomson8.Extensions.C330
import Thomson8.Extensions.C331
import Thomson8.Extensions.C332
import Thomson8.Extensions.C333

namespace Thomson8

theorem all_extension_checks (u v t a b c : Fin 4) : extensionCheck u v t a b c := by
  fin_cases u <;> fin_cases v <;> fin_cases t
  · exact Extensions.check_C000 a b c
  · exact Extensions.check_C001 a b c
  · exact Extensions.check_C002 a b c
  · exact Extensions.check_C003 a b c
  · exact Extensions.check_C010 a b c
  · exact Extensions.check_C011 a b c
  · exact Extensions.check_C012 a b c
  · exact Extensions.check_C013 a b c
  · exact Extensions.check_C020 a b c
  · exact Extensions.check_C021 a b c
  · exact Extensions.check_C022 a b c
  · exact Extensions.check_C023 a b c
  · exact Extensions.check_C030 a b c
  · exact Extensions.check_C031 a b c
  · exact Extensions.check_C032 a b c
  · exact Extensions.check_C033 a b c
  · exact Extensions.check_C100 a b c
  · exact Extensions.check_C101 a b c
  · exact Extensions.check_C102 a b c
  · exact Extensions.check_C103 a b c
  · exact Extensions.check_C110 a b c
  · exact Extensions.check_C111 a b c
  · exact Extensions.check_C112 a b c
  · exact Extensions.check_C113 a b c
  · exact Extensions.check_C120 a b c
  · exact Extensions.check_C121 a b c
  · exact Extensions.check_C122 a b c
  · exact Extensions.check_C123 a b c
  · exact Extensions.check_C130 a b c
  · exact Extensions.check_C131 a b c
  · exact Extensions.check_C132 a b c
  · exact Extensions.check_C133 a b c
  · exact Extensions.check_C200 a b c
  · exact Extensions.check_C201 a b c
  · exact Extensions.check_C202 a b c
  · exact Extensions.check_C203 a b c
  · exact Extensions.check_C210 a b c
  · exact Extensions.check_C211 a b c
  · exact Extensions.check_C212 a b c
  · exact Extensions.check_C213 a b c
  · exact Extensions.check_C220 a b c
  · exact Extensions.check_C221 a b c
  · exact Extensions.check_C222 a b c
  · exact Extensions.check_C223 a b c
  · exact Extensions.check_C230 a b c
  · exact Extensions.check_C231 a b c
  · exact Extensions.check_C232 a b c
  · exact Extensions.check_C233 a b c
  · exact Extensions.check_C300 a b c
  · exact Extensions.check_C301 a b c
  · exact Extensions.check_C302 a b c
  · exact Extensions.check_C303 a b c
  · exact Extensions.check_C310 a b c
  · exact Extensions.check_C311 a b c
  · exact Extensions.check_C312 a b c
  · exact Extensions.check_C313 a b c
  · exact Extensions.check_C320 a b c
  · exact Extensions.check_C321 a b c
  · exact Extensions.check_C322 a b c
  · exact Extensions.check_C323 a b c
  · exact Extensions.check_C330 a b c
  · exact Extensions.check_C331 a b c
  · exact Extensions.check_C332 a b c
  · exact Extensions.check_C333 a b c

#print axioms all_extension_checks

end Thomson8
