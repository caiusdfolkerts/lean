module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C4

kernel_lrat_refutation extension
  "p cnf 15 23\n-1 0\n2 0\n3 0\n4 0\n6 0\n7 0\n9 0\n10 0\n-12 -2 1 11 0\n-11 -3 1 12 0\n-12 -9 13 15 0\n-12 -10 14 15 0\n-13 -7 11 15 0\n-14 -7 11 15 0\n-15 -2 11 13 0\n-15 -4 11 14 0\n-15 -6 13 14 0\n11 12 13 14 15 0\n-15 -14 -13 11 12 0\n-15 -14 -12 -11 13 0\n-15 -13 -12 -11 14 0\n-14 -13 -12 -11 15 0\n-15 -14 -13 -12 -11 0\n"
  "24 15 11 12 0 6 14 13 18 0\n25 11 0 4 2 1 9 24 15 16 19 0\n26 12 0 25 3 1 10 0\n27 -14 -15 0 26 25 23 20 0\n28 -15 0 26 25 5 27 17 21 0\n29 14 0 26 8 28 12 0\n30 13 0 26 7 28 11 0\n31 0 29 30 26 25 28 22 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C4
