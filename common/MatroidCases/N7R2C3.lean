module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C3

kernel_lrat_refutation extension
  "p cnf 21 21\n-2 0\n-3 0\n4 0\n5 0\n6 0\n7 0\n-10 0\n11 0\n-15 0\n-18 -4 2 16 0\n-20 -4 10 19 0\n-18 -5 3 17 0\n-16 -6 2 18 0\n-17 -6 3 18 0\n-19 -7 10 20 0\n-21 -7 15 20 0\n-20 -11 15 21 0\n16 17 18 19 20 21 0\n-21 -20 -19 16 17 18 0\n-18 -17 -16 19 20 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "22 18 19 20 21 0 5 2 1 13 14 18 0\n23 20 0 4 2 3 1 6 9 7 15 16 22 10 12 20 0\n24 19 0 23 3 7 11 0\n25 21 0 23 8 9 17 0\n26 -18 0 25 23 24 4 2 3 1 10 12 21 0\n27 -16 0 5 1 26 13 0\n28 -17 0 5 2 26 14 0\n29 0 25 23 24 27 28 26 19 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C3
