module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C3

kernel_lrat_refutation extension
  "p cnf 15 21\n-1 0\n2 0\n3 0\n4 0\n-6 0\n7 0\n8 0\n9 0\n-12 -2 1 11 0\n-14 -2 6 13 0\n-11 -3 1 12 0\n-13 -4 6 14 0\n-11 -9 13 15 0\n-13 -7 11 15 0\n-13 -8 12 15 0\n-15 -2 11 13 0\n11 12 13 14 15 0\n-15 -14 -13 11 12 0\n-15 -12 -11 13 14 0\n-14 -13 -12 -11 15 0\n-15 -14 -13 -12 -11 0\n"
  "22 11 13 14 0 2 1 9 16 17 0\n23 14 0 8 3 1 4 5 12 22 11 13 19 0\n24 13 0 23 2 5 10 0\n25 -12 -15 0 23 24 2 1 9 21 0\n26 -15 0 23 24 3 1 25 11 18 0\n27 12 0 24 7 26 15 0\n28 11 0 24 6 26 14 0\n29 0 23 24 27 28 26 20 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C3
