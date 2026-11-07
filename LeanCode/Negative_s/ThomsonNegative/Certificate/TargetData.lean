import Init

namespace ThomsonNegative.Certificate.TargetData

def entries : List (Nat × Bool × Nat) := [(1, false, 1), (2, true, 2), (3, false, 3), (3, true, 3), (3, false, 1), (4, false, 2), (4, false, 4), (4, true, 4), (4, false, 1), (5, true, 5), (5, false, 5), (5, false, 5), (5, true, 5), (5, false, 1), (6, false, 3), (6, true, 2), (6, true, 12), (6, false, 9), (6, false, 6), (6, true, 6), (6, false, 1), (7, false, 7), (7, false, 7), (7, true, 7), (7, true, 21), (7, false, 14), (7, false, 7), (7, true, 7), (7, false, 1), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (8, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (9, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (10, false, 0), (11, false, 0), (12, false, 0), (11, false, 0)]
def entry (r : Nat) : Nat × Bool × Nat := entries.getD r (0,false,0)

end ThomsonNegative.Certificate.TargetData
