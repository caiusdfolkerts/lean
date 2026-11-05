module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C2

kernel_lrat_refutation extension
  "p cnf 15 23\n-1 0\n-2 0\n4 0\n5 0\n6 0\n7 0\n8 0\n9 0\n10 0\n-12 -4 1 11 0\n-13 -4 2 11 0\n-11 -5 1 12 0\n-11 -6 2 13 0\n-11 -10 14 15 0\n-14 -7 11 15 0\n-14 -8 12 15 0\n-14 -9 13 15 0\n-15 -4 11 14 0\n11 12 13 14 15 0\n-15 -14 11 12 13 0\n-15 -13 -12 -11 14 0\n-14 -13 -12 -11 15 0\n-15 -14 -13 -12 -11 0\n"
  "24 11 14 0 3 2 1 10 11 18 19 0\n25 14 0 9 5 2 4 1 24 12 13 14 21 0\n26 -11 -15 0 25 5 2 4 1 12 13 23 0\n27 -15 0 25 3 2 1 26 10 11 20 0\n28 13 0 25 8 27 17 0\n29 12 0 25 7 27 16 0\n30 11 0 25 6 27 15 0\n31 0 25 28 29 30 27 22 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C2
