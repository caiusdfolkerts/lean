module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R2C3

kernel_lrat_refutation extension
  "p cnf 10 18\n1 0\n2 0\n3 0\n4 0\n5 0\n6 0\n-7 -5 8 10 0\n-7 -6 9 10 0\n-8 -2 7 9 0\n-8 -4 7 10 0\n-9 -1 7 8 0\n-10 -3 8 9 0\n7 8 9 10 0\n-10 -9 -8 7 0\n-10 -9 -7 8 0\n-10 -8 -7 9 0\n-9 -8 -7 10 0\n-10 -9 -8 -7 0\n"
  "19 8 7 0 3 1 11 12 13 0\n20 7 0 4 2 19 9 10 14 0\n21 -9 -10 0 20 18 15 0\n22 -10 0 20 3 21 12 16 0\n23 9 0 20 6 22 8 0\n24 8 0 20 5 22 7 0\n25 0 23 24 20 22 17 0\n"

end Papers.RationalityTen.MatroidCases.N5R2C3
