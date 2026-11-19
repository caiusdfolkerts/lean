module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C1

kernel_lrat_refutation extension
  "p cnf 15 20\n-1 0\n-2 0\n-3 0\n4 0\n5 0\n6 0\n7 0\n-10 0\n-12 -4 1 11 0\n-13 -4 2 11 0\n-15 -4 10 14 0\n-11 -5 1 12 0\n-13 -5 3 12 0\n-11 -6 2 13 0\n-12 -6 3 13 0\n-14 -7 10 15 0\n11 12 13 14 15 0\n-15 -14 11 12 13 0\n-13 -12 -11 14 15 0\n-15 -14 -13 -12 -11 0\n"
  "21 11 14 15 0 4 2 1 9 10 17 0\n22 14 0 6 2 5 1 4 8 11 21 12 14 19 0\n23 15 0 22 7 8 16 0\n24 -13 0 23 22 5 3 4 2 10 13 20 0\n25 -11 0 6 2 24 14 0\n26 -12 0 6 3 24 15 0\n27 0 23 22 25 26 24 18 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C1
